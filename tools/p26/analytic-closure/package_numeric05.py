"""Package the successful original Cell05 Q80/Q96 finite certificates."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-numeric05-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-cell05-numerics'
PHASES = [('pilot', 'verification-pilot'), ('q80', 'verification-complete'),
          ('q96', 'verification-q96')]


def pin(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    OUT.mkdir(exist_ok=True, parents=True)
    receipts, declarations, command_count, module_count = {}, [], 0, 0
    runs = []
    for tag, folder in PHASES:
        source = STAGE / folder
        run = json.loads((source / 'RUN.json').read_text())
        assert run['status'] == 'succeeded' and run['P2_6_complete'] is False
        assert all(command['exit_code'] == 0 for command in run['commands'])
        runs.append(run)
        target = OUT / tag
        target.mkdir(exist_ok=True)
        shutil.copyfile(source / 'RUN.json', target / 'RUN.json')
        shutil.copyfile(source / 'owned-declarations.json', target / 'owned-declarations.json')
        for command in run['commands']:
            path = Path(command['log']['path'])
            assert pin(path) == {k: command['log'][k] for k in ['bytes', 'sha256']}
            shutil.copyfile(path, target / path.name)
        owned = json.loads((source / 'owned-declarations.json').read_text())
        assert len(owned) == run['owned_declarations']
        for item in owned:
            assert not (item['unsafe'] or item['partial'] or item['axiom'])
            assert set(item['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        declarations.extend(owned)
        command_count += len(run['commands'])
        module_count += len(run['owned_counts'])
        receipts[tag] = pin(target / 'RUN.json')
    assert len(declarations) == len({x['name'] for x in declarations}) == 89
    assert command_count == 37 and module_count == 17
    (OUT / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    for name in ['BASE_CONTEXT.json', 'PREFLIGHT.json']:
        shutil.copyfile(STAGE / name, OUT / name)
    preflight = json.loads((STAGE / 'PREFLIGHT.json').read_text())
    for source in preflight['sources'].values():
        assert pin(Path(source['path'])) == {k: source[k] for k in ['bytes', 'sha256']}
    final = runs[-1]
    members = {}
    for module, info in final['project_closure'].items():
        source = ROOT / (module.replace('.', '/') + '.lean')
        assert pin(source) == {k: info['source'][k] for k in ['bytes', 'sha256']}
        expected = info.get('new_object', info.get('reused_object'))
        assert expected is not None
        path = Path(expected['path'])
        assert pin(path) == {k: expected[k] for k in ['bytes', 'sha256']}
        members['objects/' + module.replace('.', '/') + '.olean'] = path
    assert len(members) == 192
    archive = OUT / 'project-objects.tar.xz'
    with tarfile.open(archive, 'w:xz', preset=6) as tar:
        for name, path in sorted(members.items()):
            data = path.read_bytes()
            member = tarfile.TarInfo(name)
            member.size, member.mode, member.mtime = len(data), 0o644, 0
            tar.addfile(member, io.BytesIO(data))
    with tarfile.open(archive, 'r:xz') as tar:
        entries = tar.getmembers()
        assert len(entries) == len(members)
        for member in entries:
            assert tar.extractfile(member).read() == members[member.name].read_bytes()
    receipt = {'schema': 'p26_cell05_original_numeric_capsule_v1',
               'scope': final['scope'], 'P2_6_complete': False,
               'target_modules': module_count, 'owned_declarations': len(declarations),
               'normal_commands': 17, 'kernel_commands': 17, 'owned_audits': 3,
               'Q80_factors': 560, 'Q96_rows': 56, 'project_objects': len(members),
               'archive': {'name': archive.name, **pin(archive)},
               'phase_receipts': receipts, 'original_inputs': preflight['sources'],
               'packager_source': pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
