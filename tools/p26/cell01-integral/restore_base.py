"""Compose old exact Cell01 objects with the already accepted current base."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path(__file__).resolve().parents[3]
STAGE = Path('/workspace/p26-cell01-next-20261128')
PARENT = Path('/workspace/p26-cell00-next-20261128/CURRENT_ACCEPTED_CONTEXT.json')


def pin(path):
    raw = path.read_bytes()
    return {'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def check(path, expected):
    actual = pin(path)
    assert all(actual[k] == expected[k] for k in ['bytes', 'sha256']), str(path)
    return actual


def install(source, target, expected):
    check(source, expected)
    target.parent.mkdir(parents=True, exist_ok=True)
    if target.exists():
        check(target, expected)
    else:
        shutil.copyfile(source, target)
        check(target, expected)
    return pin(target)


def main():
    parent_pin = pin(PARENT)
    parent = json.loads(PARENT.read_text())
    assert parent['formal_acceptance'] and len(parent['project_closure']) == 930
    transport = STAGE / 'transport'
    transfer = json.loads((transport / 'TRANSFER.json').read_text())
    archive = transport / 'cell01-original399-suppliers.tar.xz'
    assert transfer['archive']['sha256'] == '5278c2838907db737fd14ee6c5cd34afea609f73d875a5a7f8c3d29dd3239c72'
    check(archive, transfer['archive'])
    manifest_path = transport / 'MANIFEST.json'
    check(manifest_path, transfer['manifest'])
    manifest = json.loads(manifest_path.read_text())
    assert not manifest['formal_acceptance'] and manifest['supplier_count'] == 399
    incoming = STAGE / 'incoming'
    recovered = {}
    with tarfile.open(archive, 'r:xz') as tar:
        assert len(tar.getmembers()) == 799
        assert tar.extractfile('MANIFEST.json').read() == manifest_path.read_bytes()
        for module, info in manifest['suppliers'].items():
            row = {}
            for key, suffix, directory in [('source', '.lean', 'sources'),
                                            ('object', '.olean', 'objects')]:
                entry = info[key]
                member = directory + '/' + module.replace('.', '/') + suffix
                assert entry['member'] == member
                raw = tar.extractfile(member).read()
                assert len(raw) == entry['bytes'] and hashlib.sha256(raw).hexdigest() == entry['sha256']
                bindings = manifest['selected_registry_bindings'][module + ':' + key]
                assert bindings and all(all(b[k] == entry[k] for k in ['bytes', 'sha256']) for b in bindings)
                target = incoming / member
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists(): assert target.read_bytes() == raw
                else: target.write_bytes(raw)
                row[key] = pin(target)
            current_source = ROOT / (module.replace('.', '/') + '.lean')
            check(current_source, row['source'])
            row['source'] = pin(current_source)
            recovered[module] = row
    old_public = json.loads((ROOT / 'docs/verification/20261126-p26/cell01-row000-pilot/Cell01Row000_SUPPLIERS.json').read_text())
    assert len(old_public['suppliers']) == 398
    for info in old_public['suppliers']:
        actual = recovered[info['module']]
        for key in ['source', 'object']:
            assert all(actual[key][k] == info[key][k] for k in ['bytes', 'sha256'])
    row000 = json.loads((STAGE / 'RECOVERED_ROW000_OBJECTS.json').read_text())
    assert not row000['formal_acceptance'] and len(row000['modules']) == 23
    for info in row000['modules']:
        module = info['module']
        check(Path(info['source']['path']), info['source'])
        check(Path(info['object']['path']), info['object'])
        source = ROOT / (module.replace('.', '/') + '.lean')
        check(source, info['source'])
        if module in recovered:
            for key in ['source', 'object']:
                assert all(recovered[module][key][k] == info[key][k] for k in ['bytes', 'sha256'])
        else:
            recovered[module] = {'source': pin(source), 'object': info['object']}
    assert len(recovered) == 421
    objects = STAGE / 'objects'
    catalog, common_differences, new_modules = {}, [], []
    for module, info in parent['project_closure'].items():
        check(Path(info['source']['path']), info['source'])
        target = objects / (module.replace('.', '/') + '.olean')
        chosen = install(Path(info['selected_object']['path']), target, info['selected_object'])
        catalog[module] = {'source': info['source'], 'selected_object': chosen, 'origin': 'accepted-current930'}
    common = 0
    for module, info in recovered.items():
        if module in catalog:
            common += 1
            assert info['source'] == catalog[module]['source']
            old, current = info['object'], catalog[module]['selected_object']
            if any(old[k] != current[k] for k in ['bytes', 'sha256']):
                common_differences.append({'module': module, 'old_object': old, 'selected_current_object': current})
        else:
            target = objects / (module.replace('.', '/') + '.olean')
            chosen = install(Path(info['object']['path']), target, info['object'])
            catalog[module] = {'source': info['source'], 'selected_object': chosen, 'origin': 'recovered-not-yet-qualified'}
            new_modules.append(module)
    assert common == 14 and len(new_modules) == 407 and len(catalog) == 1337
    native = []
    old_object_root = Path(parent['lean_path'].split(':')[0])
    for item in parent['native_artifacts']:
        relative = Path(item['path']).relative_to(old_object_root)
        native.append(install(Path(item['path']), objects / relative, item))
    assert len(native) == 555
    for item in parent['runtime'].values(): check(Path(item['path']), item)
    assert pin(PARENT) == parent_pin
    lean_path = str(objects) + ':' + parent['lean_path'].split(':', 1)[1]
    context = {'schema': 'p26_cell01_recovered_context_v1', 'formal_acceptance': False,
               'P2_6_complete': False, 'accepted_parent': parent_pin,
               'source_commit': 'f38d08fdcf952b52a7bd97d03158eb89917a21d0',
               'project_closure': catalog, 'incoming_modules': sorted(new_modules),
               'common_modules': common, 'common_old_object_differences': common_differences,
               'native_artifacts': native, 'runtime': parent['runtime'], 'lean_path': lean_path,
               'transport_archive': pin(archive), 'transport_manifest': pin(manifest_path),
               'old_row000_recovery': pin(STAGE / 'RECOVERED_ROW000_OBJECTS.json'),
               'restorer_source': pin(Path(__file__))}
    (STAGE / 'RECOVERED_BASE_CONTEXT.json').write_text(json.dumps(context, indent=2) + '\n')
    (STAGE / 'INCOMING_BASE_MODULES.json').write_text(json.dumps(sorted(new_modules), indent=2) + '\n')
    print(json.dumps({'selected_project_objects': len(catalog), 'recovered_modules': len(new_modules),
                      'retained_current_common_objects': common, 'different_old_common_objects': len(common_differences),
                      'native_artifacts': len(native), 'formal_acceptance': False}), flush=True)


if __name__ == '__main__': main()
