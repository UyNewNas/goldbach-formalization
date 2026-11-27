"""Publish a completed analytic verification without historical credit transfer."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-analytic-closure-20261127')
OUT = ROOT / 'docs/verification/20261128-p26-higher-moments'


def pin(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def checked(path, expected):
    assert pin(path) == {k: expected[k] for k in ['bytes', 'sha256']}


def main():
    run = json.loads((STAGE / 'verification/RUN.json').read_text())
    assert run['status'] == 'succeeded' and run['formal_acceptance']
    assert run['fresh_kernel_import_replay_succeeded']
    assert run['P2_6_complete'] is False and run['original_full_snapshot_verified'] is False
    assert run['owned_declaration_count'] == 600 and len(run['owned_counts']) == 21
    assert all(c['exit_code'] == 0 and c['stop_reason'] is None for c in run['commands'])
    assert run['external_inputs_before']['status'] == run['external_inputs_after']['status'] == 'matched'
    assert not run['external_inputs_before']['problems'] and not run['external_inputs_after']['problems']
    normal_path = Path(run['normal_build']['path'])
    checked(normal_path, run['normal_build'])
    normal = json.loads(normal_path.read_text())
    assert len(normal['commands']) == len(normal['nodes']) == 228
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(normal_path, OUT / 'NORMAL_BUILD.json')
    shutil.copyfile(STAGE / 'verification/RUN.json', OUT / 'RUN.json')
    shutil.copyfile(STAGE / 'verification/owned-declarations.json', OUT / 'owned-declarations.json')
    for name in ['SELECTED_NATIVE_INPUTS.json', 'EXTERNAL_INPUTS_READBACK.json']:
        shutil.copyfile(STAGE / name, OUT / name)
    for label, commands in [('normal', normal['commands']), ('verification', run['commands'])]:
        target = OUT / label
        target.mkdir(exist_ok=True)
        for command in commands:
            path = Path(command['log']['path'])
            checked(path, command['log'])
            shutil.copyfile(path, target / path.name)
    for item in [run['audit_source'], run['verifier_source']]:
        checked(Path(item['path']), item)
    members = {}
    for command in normal['commands']:
        assert command['exit_code'] == 0
        checked(Path(command['source']['path']), command['source'])
        obj = Path(command['object']['path'])
        checked(obj, command['object'])
        members['objects/' + command['module'].replace('.', '/') + '.olean'] = obj
    assert len(members) == 228
    archive = OUT / 'project-objects.tar.xz'
    with tarfile.open(archive, 'w:xz', preset=6) as tar:
        for name, path in sorted(members.items()):
            data = path.read_bytes()
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            tar.addfile(info, io.BytesIO(data))
    with tarfile.open(archive, 'r:xz') as tar:
        assert len(tar.getmembers()) == len(members)
        for item in tar:
            assert tar.extractfile(item).read() == members[item.name].read_bytes()
    declarations = json.loads((OUT / 'owned-declarations.json').read_text())
    assert len(declarations) == len({x['name'] for x in declarations}) == 600
    for item in declarations:
        assert not (item['unsafe'] or item['partial'] or item['axiom'])
        assert set(item['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert '⋯' not in item['type']
    receipt = {'schema': 'p26_current_analytic_context_capsule_v1',
               'scope': run['scope'], 'formal_acceptance': True,
               'P2_6_complete': False, 'original_full_snapshot_verified': False,
               'project_objects': len(members), 'target_modules': len(run['owned_counts']),
               'owned_declarations': len(declarations),
               'imported_modules': run['imported_module_count'],
               'actual_native_imports': run['actual_native_import_count'],
               'fresh_kernel_import_replay_succeeded': True,
               'archive': {'name': archive.name, **pin(archive)},
               'run': pin(OUT / 'RUN.json'), 'normal_build': pin(OUT / 'NORMAL_BUILD.json'),
               'owned_inventory': pin(OUT / 'owned-declarations.json'),
               'packager_source': pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
