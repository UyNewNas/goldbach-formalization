#!/usr/bin/env python3
"""Check six-owner receipts; supplier context compatibility is a separate addendum."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import tarfile

from Geometry01Decoding_verify import parse_owned


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def matches(data, expected):
    return pin(data) == {key: expected[key] for key in ('bytes', 'sha256')}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('archive', type=Path)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--extract-to', type=Path)
    args = ap.parse_args()
    with tarfile.open(args.archive, 'r:xz') as archive:
        members = {}
        for item in archive.getmembers():
            name = PurePosixPath(item.name)
            assert item.isfile() and not name.is_absolute() and '..' not in name.parts
            assert item.name not in members
            members[item.name] = archive.extractfile(item).read()
    manifest = json.loads(members['ACCEPTED_EXPORT_MANIFEST.json'])
    assert manifest['status'] == 'SIX_NEW_OWNERS_NORMAL_KERNEL_FULL_OWNED_PASSED'
    assert manifest['step_counts'] == {'normal': 6, 'kernel': 6, 'owned': 6}
    assert manifest['row_interval'] == [0, 16]
    assert manifest['full_supplier_kernel_closed']
    assert not manifest['whole_geometry_decoded'] and not manifest['P2_6_complete']
    assert not manifest['suppliers_recompiled'] and not manifest['Lean_executed_for_export']
    names = {row['member'] for row in manifest['members']}
    assert len(names) == len(manifest['members'])
    assert names | {'ACCEPTED_EXPORT_MANIFEST.json'} == set(members)
    for row in manifest['members']:
        assert matches(members[row['member']], row), row['member']
    success = json.loads(members[manifest['success_member']])
    assert success['phase'] == 'cell05' and success['status'] == 'succeeded'
    assert success['accepted_targets'] == 6 and success['frozen_inputs_unchanged']
    assert success['full_supplier_kernel_closed'] and success['pending_supplier_kernel'] == []
    assert not success['cloud_source_generation'] and not success['suppliers_recompiled']
    stage = PurePosixPath(success['stage'])

    def checked(identity):
        member = str(PurePosixPath(identity['path']).relative_to(stage))
        data = members[member]
        assert matches(data, identity), member
        return data

    verifier = json.loads(checked(success['verifier_manifest']))
    suppliers = json.loads(checked(success['supplier_manifest']))
    checked(success['driver'])
    checked(success['mature_helper'])
    checked(success['supplier_installation'])
    targets = {row['module']: row for row in verifier['targets'] if row['cell'] == 5}
    assert len(targets) == 6
    local_repo = Path(__file__).resolve().parents[3]
    for module, row in targets.items():
        relative = module.replace('.', '/') + '.lean'
        assert matches(members['project/' + relative], row['source'])
        assert members['project/' + relative] == (local_repo / relative).read_bytes()
        audit_member = 'tools/p26/scalable/' + row['audit_relative_path']
        assert matches(members[audit_member], row['audit'])
        assert members[audit_member] == (Path(__file__).parent / row['audit_relative_path']).read_bytes()
    reused = [row for row in suppliers['suppliers'] if 5 in row['cells']]
    assert len(reused) == 9 and all(row['independent_kernel_receipt_pinned'] for row in reused)
    for row in reused:
        base = row['module'].replace('.', '/')
        assert matches(members['project/' + base + '.lean'], row['source'])
        assert matches(members['objects/' + base + '.olean'], row['object'])
    steps, seen, total_owned, all_axioms = [], set(), 0, set()
    for record in success['records']:
        identity = record.get('receipt') or record['reused_successful_receipt']
        step = json.loads(checked(identity))
        key = step['module'], step['mode']
        assert key not in seen and key[0] in targets and key[1] in ('normal', 'kernel', 'owned')
        seen.add(key)
        assert step['status'] == 'succeeded' and step['exit_code'] == 0
        assert step['lean_version'] == success['lean_version']
        assert step['mathlib_commit'] == success['mathlib_commit']
        checked(step['source'])
        checked(step['object'])
        log = checked(step['log']).decode()
        assert matches(checked(step['source']), targets[key[0]]['source'])
        row = {'module': key[0], 'mode': key[1], 'elapsed_seconds': step['elapsed_seconds'],
               'peak_rss_bytes': step['peak_rss_bytes'], 'source': step['source'], 'object': step['object'],
               'receipt_member': str(PurePosixPath(identity['path']).relative_to(stage)), **pin(checked(identity))}
        if key[1] == 'kernel':
            assert step['argv'][1:] == ['--verbose', key[0]]
        elif key[1] == 'owned':
            checked(step['audit_source'])
            owned = json.loads(checked(step['owned_declarations']))
            assert parse_owned(log, key[0]) == owned
            assert owned['owned_declaration_count'] == step['owned_declaration_count']
            row['owned_declaration_count'] = step['owned_declaration_count']
            row['axioms_union'] = owned['axioms_union']
            total_owned += step['owned_declaration_count']
            all_axioms.update(owned['axioms_union'])
        steps.append(row)
    assert seen == {(module, mode) for module in targets for mode in ('normal', 'kernel', 'owned')}
    assert total_owned == manifest['owned_declaration_count']
    report = {'schema': 'cell05_export_locally_rechecked_v2_context_join_required', 'status': 'PASS',
              'archive': {'path': str(args.archive), **pin(args.archive.read_bytes())},
              'listed_members_verified': len(names), 'source_and_audit_equal_local_bytes': True,
              'new_modules': 6, 'normal_steps': 6, 'independent_kernel_steps': 6, 'full_owned_steps': 6,
              'owned_declaration_count': total_owned, 'axioms_union': sorted(all_axioms),
              'suppliers_reused': 9, 'historical_independent_supplier_receipts_pinned': True,
              'full_supplier_kernel_closed_flag_in_original_run': True,
              'raw05_current_context_requires_separate_kernel_addendum': True,
              'full_supplier_kernel_closed_in_combined_evidence': None,
              'elapsed_seconds_sum': sum(row['elapsed_seconds'] for row in steps),
              'peak_rss_bytes_max': max(row['peak_rss_bytes'] for row in steps),
              'verified_steps': steps, 'row_interval': [0, 16],
              'whole_geometry_decoded': False, 'P2_6_complete': False,
              'Lean_executed_for_local_recheck': False}
    if args.extract_to:
        for name, data in members.items():
            output = args.extract_to / name
            output.parent.mkdir(parents=True, exist_ok=True)
            if output.exists():
                assert output.read_bytes() == data, ('Refusing overwrite', str(output))
            else:
                with output.open('xb') as stream:
                    stream.write(data)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({key: value for key, value in report.items() if key != 'verified_steps'}, indent=2))


if __name__ == '__main__':
    main()
