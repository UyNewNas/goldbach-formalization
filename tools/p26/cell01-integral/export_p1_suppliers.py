"""Export exact original Cell01 suppliers; recovery is not proof acceptance."""
import hashlib
import io
import json
from pathlib import Path
import tarfile
import time

BASE = Path('/workspace/p26-continuation-59264dd64286/cell01-finite-suppliers-P1')
MATCH = Path('/workspace/p26-cell01-cache-check-20261128/SOURCE_MATCH.json')
OUT = Path('/workspace/p26-cell01-supplier-export-20261128')


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def check(path, expected):
    actual = pin(path)
    assert all(actual[k] == expected[k] for k in ['bytes', 'sha256']), str(path)
    return actual


def main():
    started = time.monotonic()
    matched = json.loads(MATCH.read_text())
    assert len(matched['matched']) == 399 and not matched['different']
    assert not matched['outside_current_closure'] and not matched['formal_acceptance']
    installer_path = BASE / 'INSTALLATION_SUMMARY.json'
    installer = json.loads(installer_path.read_text())
    assert installer['status'] == 'EXACT_399_CANONICAL_SUPPLIERS_HARDLINKED'
    assert installer['modules'] == 399 and installer['files'] == 798
    registry_pin = installer['source_registry']
    registry_path = Path(registry_pin['path'])
    check(registry_path, registry_pin)
    registry = json.loads(registry_path.read_text())
    records = registry['files']
    assert isinstance(records, list) and records
    members, suppliers, selected_records = {}, {}, {}
    for info in matched['matched']:
        module = info['module']
        assert module not in suppliers
        entry = {}
        for key, extension, folder in [('source', '.lean', 'sources'),
                                        ('object', '.olean', 'objects')]:
            path = Path(info[key]['path'])
            actual = check(path, info[key])
            suffix = '/' + module.replace('.', '/') + extension
            bindings = [r for r in records if r['path'].endswith(suffix) and
                        all(r.get(k) == actual[k] for k in ['bytes', 'sha256'])]
            assert bindings, (module, key, 'not bound by original input fingerprint registry')
            member = folder + suffix
            members[member] = path
            entry[key] = {'member': member, **actual}
            selected_records[module + ':' + key] = [
                {k: r[k] for k in ['path', 'bytes', 'sha256']} for r in bindings]
        suppliers[module] = entry
    assert len(suppliers) == 399 and len(members) == 798
    OUT.mkdir(exist_ok=True)
    manifest = {'schema': 'p26_cell01_exact_original_supplier_transport_v1',
                'formal_acceptance': False, 'P2_6_complete': False,
                'current_source_commit': matched['current_source_commit'],
                'supplier_count': 399, 'suppliers': suppliers,
                'original_installer': pin(installer_path),
                'original_input_registry': registry_pin,
                'selected_registry_bindings': selected_records,
                'source_match': pin(MATCH), 'exporter_source': pin(Path(__file__)),
                'scope': 'Transport of old exact source/object inputs only. New-context replay and full owned auditing remain required.'}
    manifest_path = OUT / 'MANIFEST.json'
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    members['MANIFEST.json'] = manifest_path
    archive = OUT / 'cell01-original399-suppliers.tar.xz'
    with tarfile.open(archive, 'w:xz', preset=6) as tar:
        for name, path in sorted(members.items()):
            raw = path.read_bytes()
            entry = tarfile.TarInfo(name)
            entry.size, entry.mode, entry.mtime = len(raw), 0o644, 0
            tar.addfile(entry, io.BytesIO(raw))
    with tarfile.open(archive, 'r:xz') as tar:
        assert len(tar.getmembers()) == 799
        for entry in tar:
            assert entry.isfile() and tar.extractfile(entry).read() == members[entry.name].read_bytes()
    for info in matched['matched']:
        for key in ['source', 'object']:
            check(Path(info[key]['path']), info[key])
    check(registry_path, registry_pin)
    result = {'schema': 'p26_cell01_supplier_transport_capsule_v1',
              'formal_acceptance': False, 'P2_6_complete': False,
              'suppliers': 399, 'archive_members_read_back': 799,
              'archive': pin(archive), 'manifest': pin(manifest_path),
              'seconds': time.monotonic() - started}
    (OUT / 'TRANSFER.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__': main()
