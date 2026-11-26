#!/usr/bin/env python3
"""Compare the family supplier source pins with the accepted P1 23rd context.

Reads the published local row000-original-floor evidence only. It does not
access the blocked row001 archive, query the cloud, or execute a proof.
Acceptance of later suppliers is explicitly a coordinating-agent report.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUT = HERE / 'cell01-family'
ORIGIN = '/workspace/p26-continuation-59264dd64286/cell01-row000-original-floor'
ATTEMPT = '20261126T045413255133Z-03f42f40'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def fingerprint(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    family = load('supplier_delta_family', HERE / 'prepare_cell01_transport_family.py')
    generator = load('supplier_delta_generator', HERE / 'generate_cell01_transport_blocks.py')
    family.verify_authored_inputs(generator)
    targets = [family.INTERFACE] + [generator.block_module(b) for b in range(9)] + [family.FINAL]
    closure = {}
    def visit(module):
        if module in closure:
            return
        path = family.module_path(module)
        closure[module] = {'module': module, **family.pin(path)}
        for line in path.read_text().splitlines():
            if line.startswith('import '):
                for dependency in line.split()[1:]:
                    if dependency.startswith('ImbalancedChen.'):
                        visit(dependency)
    for target in targets:
        visit(target)
    suppliers = {module: row for module, row in closure.items() if module not in targets}
    need(len(closure) == 802 and len(suppliers) == 791, 'Unexpected full-family supplier boundary')
    archive = REPO / 'docs/verification/20261126-p26/cell01-row000-original-floor/evidence.tar.xz'
    prefix = 'attempts/' + ATTEMPT + '/'
    with tarfile.open(archive, 'r:xz') as tar:
        members = {member.name: member for member in tar.getmembers()}
        def payload(member):
            need(member in members and members[member].isfile(), 'Missing regular original evidence member')
            return tar.extractfile(members[member]).read()
        def read_pin(pin):
            path = Path(pin['path'])
            need(path.is_relative_to(ORIGIN), 'Original receipt path escapes original stage')
            data = payload(str(path.relative_to(ORIGIN)))
            need(fingerprint(data) == {k: pin[k] for k in ('bytes', 'sha256')},
                 'Original receipt member pin differs')
            return json.loads(data)
        input_bytes = payload(prefix + 'INPUT_FINGERPRINTS.json')
        inputs = json.loads(input_bytes)
        need(fingerprint(input_bytes) == {'bytes': 3816105, 'sha256':
             '67ac94afd5e2c3466b0b728c7cc95a574e8b840d5cc5d92fc3bf6f96f5c40e32'},
             'Published original INPUT differs')
        run_bytes, result_bytes = payload(prefix + 'RUN.json'), payload(prefix + 'RESULT.json')
        run, result = json.loads(run_bytes), json.loads(result_bytes)
        need(run['canonical_project_suppliers'] == len(inputs['canonical_modules']) == 1111,
             'Original canonical module count differs')
        need(result['module'] == generator.ROW000 and result['status'] == 'PASS_CELL01_ROW000_ORIGINAL_FLOOR',
             'Original target was not the accepted row000 bridge')
        need(read_pin(result['context']) == run and read_pin(run['inputs']) == inputs,
             'Original target context link differs')
        old_target_records = []
        for record in result['records']:
            seal = read_pin(record['receipt'])
            need(seal['mode'] == record['mode'] and seal['source'] == result['source'] and
                 seal['object'] == result['object'], 'Original target seal identity differs')
            old_target_records.append({'mode': record['mode'], 'receipt': record['receipt']})
        need([record['mode'] for record in old_target_records] == ['normal', 'kernel', 'owned'],
             'Original target is missing a complete three-mode index')
    matched, missing, conflicts = [], [], []
    union = inputs['project_object_union']
    for module, row in sorted(suppliers.items()):
        canonical = inputs['canonical_modules'].get(module)
        if canonical is None:
            missing.append(row)
            continue
        if not all(row[k] == canonical['source'][k] for k in ('bytes', 'sha256')):
            conflicts.append({'module': module, 'family_source': row, 'canonical': canonical})
            continue
        objects = [entry for entry in union if entry['module'] == module and entry['path'].endswith('.olean')]
        need(len(objects) == 1 and all(objects[0][k] == canonical['object'][k]
                                      for k in ('bytes', 'sha256')), 'Original object union conflict')
        matched.append({'module': module, 'family_source': row,
            'canonical_source_provider': canonical['source'],
            'canonical_object_provider': canonical['object'],
            'accepted_object_union': objects[0],
            'accepted_object_sidecars': [entry for entry in union
                if entry['module'] == module and entry['path'] != objects[0]['path']],
            'canonical_origin': canonical['origin']})
    need(not conflicts, 'Same-module source SHA conflict must be resolved before staging')
    need(all(suppliers[generator.ROW000][k] == result['source'][k] for k in ('bytes', 'sha256')),
         'Current row000 original bridge differs from its accepted target source')
    classified = []
    for row in missing:
        module = row['module']
        if module == generator.ROW000:
            item = {'category': 'ACCEPTED_ORIGINAL_TARGET_OUTSIDE_ITS_IMPORT_REGISTRY',
                    'acceptance_authority': 'Published original RESULT and all three accepted seal identities',
                    'source_provider': result['source'], 'object_provider': result['object'],
                    'records': old_target_records}
        elif module == family.GENERIC:
            item = {'category': 'ACCEPTED_GENERIC_REPORTED_BY_COORDINATOR',
                    'acceptance_authority': 'Coordinating-agent actual job report; exact runtime receipts still to be installed',
                    'job_id': '2bb6e4af6d9e49f78cf6f7026a7fb90b',
                    'source_sha256': family.GENERIC_SHA,
                    'cloud_evidence_archive': {'bytes': 2296688, 'sha256':
                        '9a4e340fdedd97aebffc2c042bde7c9dc14111ca18cc956eaa67e6f65f1c2278'}}
        else:
            prefix_name, suffix = family.PREFIX + 'Cell01Row', 'Finite'
            need(module.startswith(prefix_name) and module.endswith(suffix),
                 'Unclassified additional supplier owner')
            ordinal = int(module[len(prefix_name):-len(suffix)])
            need(1 <= ordinal < 144, 'Unexpected finite source ordinal')
            item = {'category': 'ACCEPTED_FINITE_REPORTED_BY_COORDINATOR' if ordinal <= 106 else
                                  'PENDING_FINITE_107_TO143_REPORTED_RUNNING_ON_P3',
                    'acceptance_authority': 'Coordinating-agent snapshot; not inferred from source',
                    'ordinal': ordinal, 'exact_object_and_receipt_installation_required': True}
        classified.append({**row, **item})
    counts = {}
    for row in classified:
        counts[row['category']] = counts.get(row['category'], 0) + 1
    need(len(matched) == 646 and len(missing) == 145 and counts == {
        'ACCEPTED_ORIGINAL_TARGET_OUTSIDE_ITS_IMPORT_REGISTRY': 1,
        'ACCEPTED_GENERIC_REPORTED_BY_COORDINATOR': 1,
        'ACCEPTED_FINITE_REPORTED_BY_COORDINATOR': 106,
        'PENDING_FINITE_107_TO143_REPORTED_RUNNING_ON_P3': 37}, 'Supplier delta classification differs')
    outside_bridges = [family.PREFIX + 'Cell00ArchiveBridge', family.PREFIX + 'Geometry01ArchiveBridge']
    need(not any(module in closure for module in outside_bridges), 'Archive bridge unexpectedly entered family closure')
    value = {'schema': 'p26_cell01_family_vs_accepted_p1_canonical1111_v1',
        'status': 'EXACT_SOURCE_PIN_COMPARISON_NOT_A_NEW_PROOF_ACCEPTANCE',
        'family_new_owner_count': 11, 'family_source_closure_count': 802, 'supplier_count': 791,
        'accepted_canonical_module_count': 1111, 'exact_canonical_source_matches': 646,
        'same_module_source_conflicts': [], 'missing_from_canonical_import_registry': 145,
        'classification_counts': counts, 'known_accepted_supplier_count_including_reports': 754,
        'pending_supplier_count_at_coordinator_snapshot': 37, 'other_unclassified_or_unverified_owner_count': 0,
        'accepted_archive_bridges_outside_this_closure': outside_bridges,
        'original_evidence_archive': family.pin(archive),
        'original_INPUT': {'member': prefix + 'INPUT_FINGERPRINTS.json', **fingerprint(input_bytes)},
        'original_RUN': {'member': prefix + 'RUN.json', **fingerprint(run_bytes)},
        'original_RESULT': {'member': prefix + 'RESULT.json', **fingerprint(result_bytes)},
        'matched_canonical_suppliers': matched, 'additional_suppliers': classified,
        'staging_note': 'Use each canonical_source_provider path, not an assumed source path under the old attempt project. '
                        'Use accepted_object_union paths and exact sidecars; validate live pins before hardlinking.',
        'physical_cloud_cache_presence_verified_by_this_script': False,
        'later_acceptance_inferred_from_source': False, 'new_Lean_commands': 0,
        'cloud_jobs_submitted': 0, 'blocked_row001_completed_archive_accessed': False}
    output = OUT / 'SUPPLIER_DELTA.json'
    family.write(output, family.encoded(value))
    summary = {'supplier_count': 791, 'canonical_source_matches': 646, 'source_conflicts': 0,
        'additional_accepted_old_target': 1, 'accepted_generic_reported': 1,
        'accepted_finite_001_106_reported': 106, 'pending_finite_107_143_reported': 37,
        'other_unclassified_or_unverified_suppliers': 0,
        'two_archive_bridges_in_closure': False, 'exact_delta': family.pin(output)}
    family.write(OUT / 'SUPPLIER_DELTA_SUMMARY.json', family.encoded(summary))
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
