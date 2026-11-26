#!/usr/bin/env python3
"""Freeze the one-owner P1 package locally from the accepted 23rd-owner evidence."""
from pathlib import Path
import argparse
import ast
import hashlib
import io
import json
import tarfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
TARGET = 'ImbalancedChen.P2OriginalSaving19OriginalFloorTransport'
ORIGIN = '/workspace/p26-continuation-59264dd64286/cell01-row000-original-floor'
ATTEMPT = '20261126T045413255133Z-03f42f40'


def fp_bytes(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE / 'generic-source-v1')
    args = parser.parse_args()
    output = args.output.absolute()
    assert output.resolve() == output and not output.exists()
    series = json.loads((HERE / 'SOURCE_MANIFEST.json').read_text())
    assert series['owner']['module'] == TARGET
    assert series['owner']['sha256'] == '9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574'
    wanted = {r['module']: r for r in series['project_source_closure'] if r['module'] != TARGET}
    assert len(wanted) == 233
    archive = REPO / 'docs/verification/20261126-p26/cell01-row000-original-floor/evidence.tar.xz'
    with tarfile.open(archive, 'r:xz') as old:
        entries = {m.name: m for m in old.getmembers()}
        def old_bytes(member):
            item = entries[member]
            assert item.isfile()
            return old.extractfile(item).read()
        def old_json(member):
            return json.loads(old_bytes(member))
        prefix = 'attempts/' + ATTEMPT + '/'
        context = old_json(prefix + 'RUN.json')
        inputs = old_json(prefix + 'INPUT_FINGERPRINTS.json')
        result = old_json(prefix + 'RESULT.json')
        assert context['canonical_project_suppliers'] == len(inputs['canonical_modules']) == 1111
        assert result['status'] == 'PASS_CELL01_ROW000_ORIGINAL_FLOOR'
        assert context['target'] == 'ImbalancedChen.P2OriginalSaving19Cell01Row000OriginalFloorBridge'
        origin_pins = {}
        def add_origin(member):
            value = {'path': ORIGIN + '/' + member, **fp_bytes(old_bytes(member))}
            origin_pins[value['path']] = value
            return value
        run_pin = add_origin(prefix + 'RUN.json')
        input_pin = add_origin(prefix + 'INPUT_FINGERPRINTS.json')
        result_pin = add_origin(prefix + 'RESULT.json')
        assert run_pin == result['context'] and input_pin == context['inputs']
        for mode in ('normal', 'kernel', 'owned'):
            for name in ('ACCEPTED_STEP.json', 'command.json', 'result.json', 'output.log'):
                add_origin(prefix + 'steps/' + mode + '/' + name)
            if mode == 'owned':
                add_origin(prefix + 'steps/owned/owned-declarations.json')
        union = inputs['project_object_union']
        rows = []
        for module, source_pin in sorted(wanted.items()):
            canonical = inputs['canonical_modules'][module]
            assert all(canonical['source'][k] == source_pin[k] for k in ('bytes', 'sha256'))
            obj = next(row for row in union if row['module'] == module and row['path'].endswith('.olean'))
            assert all(obj[k] == canonical['object'][k] for k in ('bytes', 'sha256'))
            sidecars = [{k: entry[k] for k in ('path', 'bytes', 'sha256')}
                        for entry in union if entry['module'] == module and
                        entry['path'] != obj['path']]
            rows.append({'module': module, 'canonical': canonical, 'source': canonical['source'],
                         'object': {k: obj[k] for k in ('path', 'bytes', 'sha256')},
                         'sidecars': sidecars})
    source_member = 'sources/' + TARGET.replace('.', '/') + '.lean'
    audit_member = 'audit/' + TARGET.split('.')[-1] + '.lean'
    source = (REPO / (TARGET.replace('.', '/') + '.lean')).read_bytes()
    audit = (HERE / 'owned-audit.lean').read_bytes()
    assert fp_bytes(source) == {k: series['owner'][k] for k in ('bytes', 'sha256')}
    assert fp_bytes(audit)['sha256'] == '4fa2d4bc9272505e76c14088e08ff309df9ba21981532016f4ff5ba6b89c7680'
    registry = {'schema': 'p26_generic_floor_one_owner_registry_v1', 'target': TARGET,
        'source': fp_bytes(source), 'audit': fp_bytes(audit),
        'source_member': source_member, 'audit_member': audit_member,
        'suppliers': rows, 'external_modules': inputs['external_modules'],
        'accepted_runtime': context,
        'origin': {'stage': ORIGIN, 'attempt': ORIGIN + '/attempts/' + ATTEMPT,
                   'run': run_pin, 'inputs': input_pin, 'result': result_pin,
                   'pinned_files': list(origin_pins.values())},
        'accepted_evidence_archive': {'repository_path': str(archive.relative_to(REPO)),
                                      **fp_bytes(archive.read_bytes())},
        'new_proof_owners': 1, 'supplier_normal_or_kernel_commands': 0,
        'source_generation_on_cloud': False,
        'supplier_source_bytes': sum(r['source']['bytes'] for r in rows),
        'supplier_object_bytes': sum(r['object']['bytes'] for r in rows),
        'supplier_objects_must_be_hardlinked': True}
    files = {
        'GenericFloor_verify.py': (HERE / 'GenericFloor_verify.py').read_bytes(),
        'Cell00OriginalFloor_continue.py': (REPO / 'tools/p26/Cell00OriginalFloor_continue.py').read_bytes(),
        'export_cell01_row000.py': (REPO / 'tools/p26/export_cell01_row000.py').read_bytes(),
        'REGISTRY.json': (json.dumps(registry, indent=2) + '\n').encode(),
        'SOURCE_CLOSURE.json': (HERE / 'SOURCE_MANIFEST.json').read_bytes(),
        'README.md': (HERE / 'VERIFIER_README.md').read_bytes(),
        source_member: source, audit_member: audit}
    for name, data in files.items():
        if name.endswith('.py'):
            ast.parse(data.decode())
    output.mkdir()
    for name, data in files.items():
        path = output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as stream:
            stream.write(data)
    manifest = {'schema': 'p26_generic_floor_frozen_source_package_v1', 'target': TARGET,
        'status': 'SOURCE_PACKAGE_ONLY_NOT_EXECUTED',
        'files': [{'member': name, **fp_bytes(data)} for name, data in sorted(files.items())],
        'new_Lean_owners': 1, 'old_supplier_count': 233, 'supplier_objects_included': False,
        'old_evidence_bodies_included': False, 'Lean_execution_by_preparer': False}
    manifest_bytes = (json.dumps(manifest, indent=2) + '\n').encode()
    with (output / 'PACKAGE_MANIFEST.json').open('xb') as stream:
        stream.write(manifest_bytes)
    files['PACKAGE_MANIFEST.json'] = manifest_bytes
    tar_path = output.with_suffix('.tar.xz')
    with tar_path.open('xb') as raw, tarfile.open(fileobj=raw, mode='w:xz', format=tarfile.PAX_FORMAT) as tar:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name); info.size = len(data); info.mode = 0o644
            tar.addfile(info, io.BytesIO(data))
    with tarfile.open(tar_path, 'r:xz') as tar:
        assert len(tar.getmembers()) == len(files)
        for member in tar.getmembers():
            assert member.isfile() and tar.extractfile(member).read() == files[member.name]
    summary = {'package': str(tar_path), **fp_bytes(tar_path.read_bytes()), 'members': len(files),
               'target_source': fp_bytes(source), 'supplier_count': len(rows),
               'supplier_source_bytes': registry['supplier_source_bytes'],
               'supplier_object_bytes_hardlink_only': registry['supplier_object_bytes'],
               'external_module_count': len(registry['external_modules']),
               'Lean_invoked': False, 'cloud_jobs_submitted': 0}
    with output.with_suffix('.metadata.json').open('x') as stream:
        stream.write(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
