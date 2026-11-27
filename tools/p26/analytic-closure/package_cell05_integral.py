"""Package successful original Cell05 finite-to-integral verification only."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-joined05-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-cell05-integral'
PHASES = [('encoding', STAGE / 'verification-encoding'),
          ('physical', STAGE / 'verification-physical'),
          ('separation', Path('/workspace/p26-separation05-20261128/verification')),
          ('packing', STAGE / 'verification-packing'),
          ('source', STAGE / 'verification-source')]


def pin(path):
    data = path.read_bytes()
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def checked(path, expected):
    assert pin(path) == {k: expected[k] for k in ['bytes', 'sha256']}


def main():
    analytic = json.loads(Path('/workspace/p26-analytic-closure-20261127/verification/RUN.json').read_text())
    assert analytic['formal_acceptance'] and analytic['fresh_kernel_import_replay_succeeded']
    OUT.mkdir(exist_ok=True, parents=True)
    declarations, modules, receipts, runs = [], {}, {}, []
    command_count = 0
    for tag, folder in PHASES:
        run = json.loads((folder / 'RUN.json').read_text())
        assert run['status'] == 'succeeded' and run['P2_6_complete'] is False
        assert all(c['exit_code'] == 0 for c in run['commands'])
        target = OUT / tag
        target.mkdir(exist_ok=True)
        shutil.copyfile(folder / 'RUN.json', target / 'RUN.json')
        shutil.copyfile(folder / 'owned-declarations.json', target / 'owned-declarations.json')
        for command in run['commands']:
            path = Path(command['log']['path'])
            checked(path, command['log'])
            shutil.copyfile(path, target / path.name)
        owned = json.loads((folder / 'owned-declarations.json').read_text())
        assert len(owned) == run['owned_declarations']
        declarations.extend(owned)
        for module, count in run['owned_counts'].items():
            assert module not in modules
            modules[module] = count
        command_count += len(run['commands'])
        receipts[tag] = pin(target / 'RUN.json')
        runs.append(run)
    assert len(modules) == 22 and command_count == 49
    assert len(declarations) == len({x['name'] for x in declarations})
    for item in declarations:
        assert not (item['unsafe'] or item['partial'] or item['axiom'])
        assert set(item['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert '⋯' not in item['type']
    external_path = ROOT / 'tools/p26/analytic-closure/verify_external_inputs.py'
    spec = importlib.util.spec_from_file_location('p26_final_cell05_external_readback', external_path)
    external_verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(external_verifier)
    external_verifier.OUT = STAGE / 'FINAL_EXTERNAL_READBACK.json'
    external_verifier.main()
    external = json.loads(external_verifier.OUT.read_text())
    assert external['status'] == 'matched' and not external['problems']
    assert external['plan'] == analytic['external_inputs_after']['plan']
    shutil.copyfile(external_verifier.OUT, OUT / 'FINAL_EXTERNAL_READBACK.json')
    (OUT / 'owned-declarations.json').write_text(json.dumps(declarations, indent=2) + '\n')
    shutil.copyfile(STAGE / 'BASE_CONTEXT.json', OUT / 'BASE_CONTEXT.json')
    shutil.copyfile('/workspace/p26-separation05-20261128/PREFLIGHT.json', OUT / 'SEPARATION_PROPOSAL.json')
    members, context_objects = {}, 0
    for module, info in runs[-1]['project_closure'].items():
        checked(Path(info['source']['path']), info['source'])
        expected = info.get('new_object', info.get('reused_object'))
        assert expected is not None
        path = Path(expected['path'])
        checked(path, expected)
        context_objects += 1
        if module in modules:
            members['objects/' + module.replace('.', '/') + '.olean'] = path
    assert context_objects == 439 and len(members) == 22
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
    receipt = {'schema': 'p26_original_cell05_integral_capsule_v1',
               'scope': runs[-1]['scope'], 'P2_6_complete': False,
               'original_full_snapshot_verified': False,
               'project_objects_in_context': context_objects,
               'packaged_project_objects': len(members), 'target_modules': len(modules),
               'owned_declarations': len(declarations),
               'normal_commands': 22, 'kernel_commands': 22, 'owned_audits': 5,
               'original_rows': 56, 'separated_pairs': 1540,
               'original_vertices': 28, 'source_gates': 97,
               'exact_bound': '269254868222475389 / 2^96 <= integral(cell 5, conservativeDensity)',
               'archive': {'name': archive.name, **pin(archive)},
               'parent_capsules': {
                   'analytic': pin(ROOT / 'docs/verification/20261128-p26-higher-moments/CAPSULE.json'),
                   'numeric': pin(ROOT / 'docs/verification/20261128-p26-cell05-numerics/CAPSULE.json')},
               'phases': receipts, 'owned_inventory': pin(OUT / 'owned-declarations.json'),
               'final_external_readback': pin(OUT / 'FINAL_EXTERNAL_READBACK.json'),
               'packager_source': pin(Path(__file__))}
    (OUT / 'CAPSULE.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt), flush=True)


if __name__ == '__main__':
    main()
