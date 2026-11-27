"""Package only a successful, source-bound original Cell05 verification."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-moment05-20261128')
OUT = ROOT / 'docs/verification/20261128-p26-moment05'


def pin(path):
    raw = path.read_bytes()
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def main():
    verified = STAGE / 'verification'
    run = json.loads((verified / 'RUN.json').read_text())
    normal = json.loads((STAGE / 'RUN.json').read_text())
    assert run['status'] == 'succeeded' and run['P2_6_complete'] is False
    assert normal['status'] == 'normal_build_succeeded_not_formally_accepted'
    assert len(run['owned_counts']) == 36 and len(run['commands']) == 73
    assert all(c['exit_code'] == 0 for c in run['commands'])
    assert len(normal['nodes']) == len(normal['commands']) == 43
    assert all(c['exit_code'] == 0 for c in normal['commands'])
    raw = run['original_raw_input']
    assert pin(Path(raw['path'])) == {k: raw[k] for k in ['bytes', 'sha256']}
    OUT.mkdir(exist_ok=True, parents=True)
    shutil.copyfile(STAGE / 'RUN.json', OUT / 'NORMAL_BUILD.json')
    shutil.copyfile(verified / 'RUN.json', OUT / 'RUN.json')
    shutil.copyfile(verified / 'owned-declarations.json', OUT / 'owned-declarations.json')
    for command in run['commands']:
        path = Path(command['log']['path'])
        assert pin(path) == {k: command['log'][k] for k in ['bytes', 'sha256']}
        shutil.copyfile(path, OUT / path.name)
    members = {}
    for module, info in run['project_closure'].items():
        source = ROOT / (module.replace('.', '/') + '.lean')
        assert pin(source) == {k: info['source'][k] for k in ['bytes', 'sha256']}
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None
        path = Path(obj['path'])
        assert pin(path) == {k: obj[k] for k in ['bytes', 'sha256']}
        members['objects/' + module.replace('.', '/') + '.olean'] = path
    assert len(members) == 43
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
            data = tar.extractfile(member).read()
            assert data == members[member.name].read_bytes()
    receipt = {
        'schema': 'p26_moment05_exact_project_capsule_v1',
        'archive': {'name': archive.name, **pin(archive)},
        'project_object_count': len(members),
        'verified_module_count': len(run['owned_counts']),
        'owned_declaration_count': run['owned_declarations'],
        'normal_command_count': sum(c['label'].endswith('-normal') for c in run['commands']),
        'kernel_command_count': sum(c['label'].endswith('-kernel') for c in run['commands']),
        'original_raw_input': raw,
        'raw_archive_commit': 'a2a7146f8de2beb8fc79f09d111f4af023840580',
        'formal_scope': run['scope'], 'P2_6_complete': False,
        'run': pin(OUT / 'RUN.json'), 'normal_build': pin(OUT / 'NORMAL_BUILD.json'),
        'owned_declarations': pin(OUT / 'owned-declarations.json'),
        'packager_source': pin(Path(__file__)),
    }
    (OUT / 'CAPSULE.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
