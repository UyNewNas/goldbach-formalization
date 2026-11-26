#!/usr/bin/env python3
"""Locally verify raw05's separate context-kernel addendum without Lean."""
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import tarfile


def pin(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def same(data, expected):
    return pin(data) == {key: expected[key] for key in ('bytes', 'sha256')}


def unpack(path):
    members = {}
    with tarfile.open(path, 'r:xz') as archive:
        for item in archive.getmembers():
            name = PurePosixPath(item.name)
            assert item.isfile() and not name.is_absolute() and '..' not in name.parts
            assert item.name not in members
            members[item.name] = archive.extractfile(item).read()
    return members


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('archive', type=Path)
    ap.add_argument('--main-archive', type=Path, required=True)
    ap.add_argument('--historical-archive', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--extract-to', type=Path, required=True)
    args = ap.parse_args()
    files, baseline, historical = unpack(args.archive), unpack(args.main_archive), unpack(args.historical_archive)
    manifest = json.loads(files['EXPORT_MANIFEST.json'])
    names = {item['member'] for item in manifest['members']}
    assert names | {'EXPORT_MANIFEST.json'} == set(files) and len(names) == len(manifest['members']) == 9
    for item in manifest['members']:
        assert same(files[item['member']], item), item['member']
    assert same(args.main_archive.read_bytes(), manifest['original_six_owner_evidence_archive'])
    assert same(args.historical_archive.read_bytes(), manifest['original_raw05_historical_archive'])
    result, command, plan = (json.loads(files[name]) for name in ['RESULT.json', 'COMMAND.json', 'PLAN.json'])
    before, after = json.loads(files['BEFORE.json']), json.loads(files['AFTER.json'])
    assert before == after
    assert result['status'] == manifest['status'] == 'PASS_RAW05_KERNEL_IN_PILOT_CONTEXT'
    assert result['exit_code'] == 0
    for record in [result, command, manifest]:
        assert record['normal_commands'] == 0 and record['kernel_commands'] == 1
        assert not record['six_new_owners_replayed']
    assert result['frozen_sources_objects_sidecars_context_unchanged']
    assert result['baseline_18_steps_and_archive_unchanged'] and not result['historical_evidence_rewritten']
    assert not result['whole_geometry_decoded'] and not result['P2_6_complete']
    for name, field in [('COMMAND.json', 'command'), ('kernel.log', 'log'), ('BEFORE.json', 'before'), ('AFTER.json', 'after')]:
        assert same(files[name], result[field])
    run = json.loads(files['RUN.json'])
    assert files['RUN.json'] == baseline[plan['baseline_run_member']]
    assert files['BASELINE_KERNEL_COMMAND.json'] == baseline[plan['baseline_command_member']]
    assert command['complete_baseline_run'] == run == plan['baseline_run_content']
    old_command = json.loads(files['BASELINE_KERNEL_COMMAND.json'])
    target = 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData05'
    assert command['argv'] == [old_command['argv'][0], '--verbose', target]
    assert command['cwd'] == old_command['cwd'] == run['cwd']
    assert command['LEAN_PATH'] == old_command['LEAN_PATH'] == run['LEAN_PATH']
    assert command['LEAN_NUM_THREADS'] == command['OMP_NUM_THREADS'] == '1'
    assert files['kernel.log'].decode().strip() == 'replaying ' + target
    stage = PurePosixPath(run['stage'])
    baseline_manifest = json.loads(baseline['ACCEPTED_EXPORT_MANIFEST.json'])
    expected = {item['member']: item for item in baseline_manifest['members']}
    seen = set()
    for item in before['protected_baseline_files']:
        member = str(PurePosixPath(item['path']).relative_to(stage))
        assert member not in seen and same(baseline[member], item)
        seen.add(member)
    assert seen == set(expected) and len(seen) == 111
    assert same(args.main_archive.read_bytes(), before['baseline_archive'])
    groups = before['nine_supplier_sources_objects_and_sidecars']
    assert len(groups) == 18 and len({group['module'] for group in groups}) == 9
    pairs = set()
    for group in groups:
        assert group['kind'] in ['source', 'object'] and len(group['files']) == 1
        pairs.add((group['module'], group['kind']))
        for item in group['files']:
            member = str(PurePosixPath(item['path']).relative_to(stage))
            assert same(baseline[member], item)
    assert len(pairs) == 18
    assert before['leanchecker_binary']['path'] == command['argv'][0]
    assert before['lean_binary']['path'] == str(PurePosixPath(command['argv'][0]).with_name('lean'))
    local_tools = Path(__file__).parent
    assert files['DRIVER.py'] == (local_tools / 'verify_raw05_context.py').read_bytes()
    assert files['PLAN.json'] == (local_tools / 'RAW05_CONTEXT_CHECK_PLAN.json').read_bytes()
    assert same(files['DRIVER.py'], before['driver']) and same(files['PLAN.json'], before['plan'])
    historical_context_name = 'previous-p1-evidence/runs/attempt-00000/P1_DEPENDENCY_CONTEXT_BEFORE.json'
    historical_context = json.loads(historical[historical_context_name])['context']
    changes = plan['historical_to_current_dependency_changes']
    assert changes == result['context_object_differences'] and len(changes) == 2
    for change in changes:
        relative = change['module'].replace('.', '/')
        assert historical_context['dependency_objects_and_traces']['.lake/build/lib/lean/' + relative + '.olean'] == change['historical_object']
        assert historical_context['project_sources'][change['module']] == change['source_sha256_unchanged']
        assert pin(baseline['project/' + relative + '.lean'])['sha256'] == change['source_sha256_unchanged']
        assert same(baseline['objects/' + relative + '.olean'], change['current_object'])
    for name, data in files.items():
        output = args.extract_to / name
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.exists():
            assert output.read_bytes() == data
        else:
            with output.open('xb') as stream:
                stream.write(data)
    report = {'schema': 'raw05_context_addendum_local_recheck_v1', 'status': 'PASS',
              'archive': {'path': str(args.archive), **pin(args.archive.read_bytes())},
              'listed_members_verified': len(names), 'baseline_members_unchanged': len(seen),
              'suppliers_with_source_object_and_sidecar_inventory': 9,
              'before_equals_after': True, 'cwd_LEAN_PATH_checker_match_original_context': True,
              'exit_code': 0, 'normal_commands': 0, 'independent_kernel_commands': 1,
              'six_new_owners_replayed': False, 'old_18_steps_and_archive_unchanged': True,
              'historical_archive_unchanged': True, 'historical_dependency_object_changes_checked': changes,
              'kernel_elapsed_seconds': result['elapsed_seconds'], 'kernel_peak_rss_bytes': result['peak_rss_bytes'],
              'full_supplier_kernel_closed_in_combined_evidence': True,
              'original_run_closed_boolean_insufficient_without_addendum': True,
              'new_owner_count_remains': 6, 'whole_geometry_decoded': False, 'P2_6_complete': False}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
