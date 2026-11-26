#!/usr/bin/env python3
"""Freeze local source/audit/supplier manifests for the finite row000 P3 run.

Reads existing packages and receipts. Generates no proofs, invokes no Lean,
and submits no cloud jobs. The last analytical bridge stays outside the run.
"""
from pathlib import Path
import ast
import hashlib
import json
import re
import tarfile


REPO = Path(__file__).resolve().parents[2]
PACKAGES = Path('/dev/shm/p26-59264dd64286')
REPORT = REPO / 'docs/verification/20261126-p26/cell01-row000-pilot'
TOOLS = REPO / 'tools/p26'


def identity(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def fp(path):
    return {'path': str(path), **identity(path.read_bytes())}


def same(a, b):
    return all(a[key] == b[key] for key in ['bytes', 'sha256'])


def write_new(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as out:
        out.write(text)


def json_new(path, data):
    write_new(path, json.dumps(data, ensure_ascii=False, indent=2) + '\n')


def main():
    source_manifest = json.loads((REPORT / 'SOURCE_MANIFEST.json').read_text())
    targets = source_manifest['new_owners'][:-1]
    assert len(targets) == 22
    held = source_manifest['new_owners'][-1]
    assert held['module'].endswith('OriginalFloorBridge')
    new_names = {row['module'] for row in targets}
    closure = {}
    external = set()

    def visit(module):
        if module in closure:
            return
        path = REPO / Path(module.replace('.', '/') + '.lean')
        text = path.read_text()
        imports = re.findall(r'^import\s+([\w.]+)\s*$', text, re.M)
        closure[module] = {'source': fp(path), 'imports': imports}
        for dep in imports:
            if dep.startswith('ImbalancedChen.'):
                visit(dep)
            else:
                external.add(dep)

    for target in targets:
        visit(target['module'])
    assert len(closure) == 420
    assert 'ImbalancedChen.P2OriginalSaving19HigherMomentsPrefix' not in closure
    assert 'ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge' not in closure
    assert 'ImbalancedChen.P2OriginalSaving19CharacterCore00' not in closure
    available = {}
    packages = []

    def offer(label, module, source, obj, source_member, object_member, status):
        entry = available.setdefault(module, {'module': module, 'source': source, 'object': obj,
                                              'locations': [], 'supplier_states': {}})
        assert same(entry['source'], source), ('Conflicting supplier source', module, label)
        assert same(entry['object'], obj), ('Conflicting supplier object', module, label)
        location = {'relative_root': '../' + label, 'source_member': source_member,
                    'object_member': object_member}
        if location not in entry['locations']:
            entry['locations'].append(location)
        entry['supplier_states'][label] = status

    with tarfile.open(PACKAGES / 'cell00-480-suppliers.tar.xz') as archive:
        raw = archive.extractfile('MANIFEST.json').read()
        manifest = json.loads(raw)
        packages.append({'label': 'cell00', 'relative_root': '../cell00',
                         'manifest': {'archive_member': 'MANIFEST.json', **identity(raw)},
                         'package': fp(PACKAGES / 'cell00-480-suppliers.tar.xz')})
        sources = {row['module']: row for row in manifest['files'] if row['role'] == 'project_source'}
        objects = {row['module']: row for row in manifest['files'] if row['role'] == 'project_object'}
        for module, source in sources.items():
            obj = objects[module]
            status = 'normal_only' if module in manifest['normal_only_modules'] else 'normal_and_kernel'
            offer('cell00', module, source, obj, source['archive_path'], obj['archive_path'], status)

    with tarfile.open(PACKAGES / 'geometry01-suppliers.tar.xz') as archive:
        raw = archive.extractfile('Geometry01Decoding_SUPPLIERS.json').read()
        manifest = json.loads(raw)
        packages.append({'label': 'geometry01', 'relative_root': '../geometry01',
                         'manifest': {'archive_member': 'Geometry01Decoding_SUPPLIERS.json', **identity(raw)},
                         'package': fp(PACKAGES / 'geometry01-suppliers.tar.xz'),
                         'completion_evidence': []})
        for status, rows in [('normal_and_kernel', manifest['accepted']), ('normal_only', manifest['normal_only'])]:
            for row in rows:
                offer('geometry01', row['module'], row['source'], row['object'],
                      row['source']['archive_member'], row['object']['archive_member'], status)

    with tarfile.open(PACKAGES / 'geometry01-completed-evidence.tar.xz') as archive:
        names = archive.getnames()
        successes = [name for name in names if name.endswith('/SUCCESS.json')]
        assert len(successes) == 1
        success = json.loads(archive.extractfile(successes[0]).read())
        assert success['status'] == 'succeeded' and success['accepted_targets'] == 33
        evidence_members = {successes[0]}
        receipt_modes = {}
        for name in names:
            if not name.endswith('-result.json'):
                continue
            raw = archive.extractfile(name).read()
            receipt = json.loads(raw)
            if receipt.get('status') != 'succeeded' or receipt.get('exit_code') != 0:
                continue
            module, mode = receipt['module'], receipt['mode']
            receipt_modes.setdefault(module, set()).add(mode)
            obj_member = 'objects/' + module.replace('.', '/') + '.olean'
            assert same(identity(archive.extractfile(obj_member).read()), receipt['object'])
            offer('geometry01', module, receipt['source'], receipt['object'],
                  'project/' + module.replace('.', '/') + '.lean', obj_member,
                  'normal_kernel_and_owned_completed')
            evidence_members.add(name)
            for key in ['log', 'owned_declarations']:
                if key in receipt:
                    member = receipt[key]['path'].split('/geometry01/', 1)[1]
                    assert same(identity(archive.extractfile(member).read()), receipt[key])
                    evidence_members.add(member)
        assert len(receipt_modes) == 33
        for module, modes in receipt_modes.items():
            assert {'kernel', 'owned'} <= modes
            assert 'normal' in modes or module.endswith('Geometry01DirectDecodedRows066')
        packages[-1]['completion_package'] = fp(PACKAGES / 'geometry01-completed-evidence.tar.xz')
        packages[-1]['completion_evidence'] = [
            {'archive_member': member, **identity(archive.extractfile(member).read())}
            for member in sorted(evidence_members)]

    with tarfile.open(PACKAGES / 'moment01-suppliers.tar.xz') as archive:
        raw = archive.extractfile('Moment01_SUPPLIERS.json').read()
        manifest = json.loads(raw)
        packages.append({'label': 'moment01', 'relative_root': '../moment01',
                         'manifest': {'archive_member': 'Moment01_SUPPLIERS.json', **identity(raw)},
                         'package': fp(PACKAGES / 'moment01-suppliers.tar.xz')})
        assert manifest['project_closure_count'] == 88
        for row in manifest['accepted']:
            offer('moment01', row['module'], row['source'], row['object'],
                  row['source']['archive_member'], row['object']['archive_member'], 'normal_and_kernel')

    suppliers = []
    normal_only = []
    for module in sorted(set(closure) - new_names):
        assert module in available, ('Missing supplier object', module)
        row = available[module]
        assert same(row['source'], closure[module]['source']), ('Repository/source mismatch', module)
        row['project_imports'] = [dep for dep in closure[module]['imports'] if dep.startswith('ImbalancedChen.')]
        if all(state == 'normal_only' for state in row['supplier_states'].values()):
            normal_only.append(module)
        suppliers.append(row)
    assert len(suppliers) == 398
    assert normal_only == ['ImbalancedChen.P2Winner9HomogeneousRecurrence']
    supplier_path = REPORT / 'Cell01Row000_SUPPLIERS.json'
    supplier = {'schema': 'cell01_row000_finite_supplier_boundary_v1',
                'packages': packages, 'suppliers': suppliers, 'project_closure_count': 420,
                'new_targets': 22, 'existing_supplier_count': 398,
                'normal_only_suppliers': normal_only,
                'pending_supplier_kernel_job': 'job_cb696e722e044d6a8e95470d4290c441',
                'pending_supplier_policy': 'Do not rerun generic owners on P3; full supplier-kernel closure awaits the P1 receipt for the same object SHA.',
                'external_imports': sorted(external), 'source_generation_on_cloud': False,
                'same_name_source_and_object_conflicts': [],
                'held_analytic_bridge': held['module']}
    json_new(supplier_path, supplier)

    template_path = TOOLS / 'geometry01-owned-audits/P2OriginalSaving19Geometry01Shape.lean'
    template = template_path.read_text()
    verifier_targets = []
    for row in targets:
        module = row['module']
        audit_path = TOOLS / 'cell01-row000-owned-audits' / (module.split('.')[-1] + '.lean')
        text = template.replace('ImbalancedChen.P2OriginalSaving19Geometry01Shape', module)
        write_new(audit_path, text)
        assert same(fp(REPO / Path(module.replace('.', '/') + '.lean')), row['source'])
        verifier_targets.append({'module': module, 'source': row['source'], 'audit': fp(audit_path),
                                 'audit_relative_path': audit_path.relative_to(TOOLS).as_posix()})
    driver = TOOLS / 'Cell01Row000_verify.py'
    helper = TOOLS / 'Geometry01Decoding_verify.py'
    ast.parse(driver.read_text())
    ast.parse(helper.read_text())
    verifier_path = TOOLS / 'Cell01Row000_VERIFIER.json'
    verifier = {'schema': 'cell01_row000_frozen_finite_verifier_v1', 'driver': fp(driver),
                'mature_helper': fp(helper), 'supplier_manifest': fp(supplier_path),
                'full_owned_inventory_template': fp(template_path), 'targets': verifier_targets,
                'held_targets': [{'module': held['module'], 'source': held['source'],
                                  'reason': 'Wait for P1 HigherMomentsPrefix and analytical supplier closure.'}],
                'preserved_failed_job': '09da80e59b7f4b828b851df45f033d4c',
                'project_object_installation': 'One complete stage objects tree; same-SHA supplier hardlinks or exclusive cross-filesystem copies, no recompilation.',
                'cloud_source_generation': False, 'local_Lean_calls': False,
                'modes': ['normal', 'kernel', 'owned'], 'stop_on_failure': True}
    json_new(verifier_path, verifier)
    finite_order = REPORT / 'cloud_order_finite.txt'
    write_new(finite_order, '\n'.join(row['module'] for row in targets) + '\n')

    package = PACKAGES / 'cell01-row000-verifier-v3.tar.xz'
    assert not package.exists()
    with tarfile.open(package, 'w:xz', preset=6) as archive:
        for row in targets:
            path = REPO / Path(row['module'].replace('.', '/') + '.lean')
            archive.add(path, arcname='project/' + path.relative_to(REPO).as_posix(), recursive=False)
        for path in [driver, helper, verifier_path, Path(__file__).resolve()]:
            archive.add(path, arcname=path.relative_to(REPO).as_posix(), recursive=False)
        for item in verifier_targets:
            path = TOOLS / item['audit_relative_path']
            archive.add(path, arcname=path.relative_to(REPO).as_posix(), recursive=False)
        archive.add(supplier_path, arcname='Cell01Row000_SUPPLIERS.json', recursive=False)
        archive.add(finite_order, arcname='cloud_order.txt', recursive=False)
        for name in ['SOURCE_MANIFEST.json', 'CANDIDATE_WITNESSES.json', 'README.md']:
            archive.add(REPORT / name, arcname='evidence/source-pilot/' + name, recursive=False)
        empty_objects = tarfile.TarInfo('objects')
        empty_objects.type = tarfile.DIRTYPE
        empty_objects.mode = 0o755
        archive.addfile(empty_objects)
    print(json.dumps({'package': fp(package), 'targets': len(targets),
                      'existing_suppliers': len(suppliers), 'pending_supplier_kernel': normal_only,
                      'supplier_manifest': fp(supplier_path), 'verifier_manifest': fp(verifier_path),
                      'driver': fp(driver), 'audit_sources': len(verifier_targets),
                      'Lean_run': False, 'cloud_jobs_submitted': False}, indent=2))


if __name__ == '__main__':
    main()
