"""Restore byte-pinned Cell00 suppliers; this is not new proof credit."""
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell00-next-20261128')
COMMIT = 'e70a90d15ca73917cc500f4750bb205074fc2dda'
ARCHIVE_SHA = '9518e531726e6c1ca0970e7751424469cedea08e702952d22be49584c48d0df6'
MANIFEST_SHA = '0eeb14fbd6b4c57c037884ab9ccb8291bcd3a4e91d743a5bad9aafdebd20ffeb'
PARENT = ROOT / 'docs/verification/20261128-p26-cell05-integral/source/RUN.json'


def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def same(actual, expected):
    return all(actual[k] == expected[k] for k in ['bytes', 'sha256'])


def put_checked(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists():
        assert path.read_bytes() == data, path
    else:
        path.write_bytes(data)


def main():
    raw = subprocess.check_output(['git', '--git-dir=' + str(STAGE / 'suppliers.git'),
                                   'show', COMMIT + ':old-cell00-suppliers.tar.xz'])
    assert len(raw) == 30261756 and hashlib.sha256(raw).hexdigest() == ARCHIVE_SHA
    incoming = STAGE / 'incoming'
    with tarfile.open(fileobj=io.BytesIO(raw), mode='r:xz') as tar:
        data = tar.extractfile('MANIFEST.json').read()
        assert hashlib.sha256(data).hexdigest() == MANIFEST_SHA
        manifest = json.loads(data)
        put_checked(incoming / 'MANIFEST.json', data)
        selected = {x['archive_path']: x for x in manifest['files']
                    if x['role'] in ['project_source', 'project_object']}
        assert len(selected) == 960
        assert {m.name for m in tar.getmembers()} == set(selected) | {'MANIFEST.json'}
        for name, expected in selected.items():
            assert '..' not in Path(name).parts and not Path(name).is_absolute()
            member = tar.getmember(name)
            assert member.isfile()
            data = tar.extractfile(member).read()
            assert len(data) == expected['bytes']
            assert hashlib.sha256(data).hexdigest() == expected['sha256']
            put_checked(incoming / name, data)

    old = {}
    for item in selected.values():
        role = 'source' if item['role'] == 'project_source' else 'object'
        old.setdefault(item['module'], {})[role] = {
            'path': str(incoming / item['archive_path']), 'bytes': item['bytes'],
            'sha256': item['sha256']}
    assert len(old) == 480 and all(set(v) == {'source', 'object'} for v in old.values())
    for module, info in old.items():
        current = ROOT / (module.replace('.', '/') + '.lean')
        assert same(pin(current), info['source'])

    evidence = ROOT / 'docs/verification/20261126-p26/cell00-original-floor/evidence.tar.xz'
    exported = json.loads((evidence.parent / 'EXPORT_MANIFEST.json').read_text())
    module = 'ImbalancedChen.P2OriginalSaving19Cell00AllOriginalFloorBridge'
    info = exported['new_owners'][module]
    with tarfile.open(evidence, 'r:xz') as tar:
        pair = {}
        for role, suffix in [('source', '.lean'), ('object', '.olean')]:
            item = info[role]
            data = tar.extractfile(item['archive_member']).read()
            assert len(data) == item['bytes'] and hashlib.sha256(data).hexdigest() == item['sha256']
            dest = incoming / ('sources' if role == 'source' else 'objects') / (module.replace('.', '/') + suffix)
            put_checked(dest, data)
            pair[role] = pin(dest)
        assert same(pin(ROOT / (module.replace('.', '/') + '.lean')), pair['source'])
        old[module] = pair

    parent = json.loads(PARENT.read_text())
    assert parent['status'] == 'succeeded' and len(parent['project_closure']) == 439
    objects = STAGE / 'objects'
    catalog, shared = {}, []

    def copy_object(module, source, obj, origin):
        assert pin(Path(source['path'])) == source
        assert pin(Path(obj['path'])) == obj
        target = objects / (module.replace('.', '/') + '.olean')
        put_checked(target, Path(obj['path']).read_bytes())
        return {'source': source, 'original_object': obj,
                'selected_object': pin(target), 'origin': origin}

    for module, info in parent['project_closure'].items():
        obj = info.get('new_object', info.get('reused_object'))
        assert obj is not None
        catalog[module] = copy_object(module, info['source'], obj, 'accepted-current-parent')
    for module, info in old.items():
        source = pin(ROOT / (module.replace('.', '/') + '.lean'))
        assert same(source, info['source'])
        if module in catalog:
            assert source == catalog[module]['source']
            assert same(catalog[module]['selected_object'], info['object'])
            shared.append(module)
        else:
            catalog[module] = copy_object(module, source, info['object'], 'original-byte-pinned-cell00-cache')
    assert len(shared) == 14 and len(catalog) == 906
    base_path = ROOT / 'docs/verification/20261128-p26-cell05-integral/BASE_CONTEXT.json'
    base = json.loads(base_path.read_text())
    native = []
    for item in base['native_artifacts']:
        source = item['selected']
        path = Path(source['path'])
        assert pin(path) == source
        target = objects / path.relative_to(base['objects'])
        put_checked(target, path.read_bytes())
        native.append(pin(target))
    assert len(native) == 555
    report = {'schema': 'p26_cell00_recovered_supplier_composition_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'original_full_snapshot_verified': False,
              'supplier_archive_commit': COMMIT, 'archive_sha256': ARCHIVE_SHA,
              'old_manifest_sha256': MANIFEST_SHA,
              'parent': pin(PARENT), 'parent_base': pin(base_path),
              'project_closure': catalog, 'identical_old_common_objects': shared,
              'native_artifacts': native, 'runtime': parent['runtime'],
              'lean_path': ':'.join([str(objects), *parent['lean_path'].split(':')[1:]]),
              'objects': str(objects), 'restore_source': pin(Path(__file__)),
              'pending_aggregate': 'ImbalancedChen.P2OriginalSaving19Cell00AllRowArithmetic'}
    (STAGE / 'RECOVERED_CONTEXT.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'project_modules': len(catalog), 'old_common_identical': len(shared),
                      'native_artifacts': len(native), 'formal_acceptance': False}))


if __name__ == '__main__':
    main()
