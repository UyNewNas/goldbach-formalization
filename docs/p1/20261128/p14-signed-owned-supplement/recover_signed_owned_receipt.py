#!/usr/bin/env python3
"""Postprocess one completed Signed audit without replaying any proof operation.

The original caller failed after writing its exact journal tail: Lake had first
queried the unchanged Lean runtime with --githash, then invoked the one intended
audit.  This independent caller recognizes only those two frozen events.  It
leaves the original failed lane, missing result, and pipeline status untouched.
All results are written to a separate postprocess root.  No compiler, checker,
audit, normal-provenance creator, source installer, or build output is invoked.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError('P1.4 receipt postprocessing forbids optimized Python')

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PREFIX = 'docs/p1/20261128/p14-signed-owned-supplement/'
DRIVER = PREFIX + 'recover_signed_owned_receipt.py'
PLAN = PREFIX + 'SIGNED_RECEIPT_RECOVERY_PLAN.json'
PLAN_SHA = 'd0b2e0497c78d2bc1da31f7d3eea9220fc60fdb93009a34ee39829d4d6ddd0ff'
ORIGINAL_SOURCE = 'd14ca4c2360ee55fd9361381a4358c7054c881cd'
ORIGINAL_DRIVER = PREFIX + 'run_signed_owned_supplement.py'
ORIGINAL_DRIVER_SHA = '6bdf8ae872d037c65d761f44ea6a02f1a0e58a6217b8b2489e864f2f7df78d35'
ORIGINAL_MANIFEST_SHA = 'c10e5f299fce6257c25e5745a5c3a71ac7aaf1ce55ee4e1b5fcc69455032d6df'
MODULE = 'ImbalancedChen.P5OriginalSignedMidpoint'
SHORT = MODULE.split('.')[-1]
SOURCE = MODULE.replace('.', '/') + '.lean'
ORIGINAL_ROOT = Path('/workspace/p1-complete-proof/20261128-p14-signed-owned-supplement')
ORIGINAL_PIPELINE = Path('/workspace/p1-complete-proof/20261125-p14-continuation-bootstrap') / ORIGINAL_SOURCE / 'signed-recorded-owned-supplements'
ROOT = Path('/workspace/p1-complete-proof/20261128-p14-signed-owned-postprocess')
FAILURE = 'the serialized audit must produce exactly one actual guard event'
RESULT_NAME = 'SIGNED_RECEIPT_POSTPROCESS_RESULT.json'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def load(raw, name):
    module = types.ModuleType(name)
    module.__file__ = '<unchanged pinned source: ' + name + '>'
    exec(compile(raw, module.__file__, 'exec'), module.__dict__)
    return module


def read_file(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), 'missing or symlinked original: ' + str(path))
    return path.read_bytes()


def read_original_receipts(plan):
    """Read the fixed original files; never make a missing receipt or directory."""
    need(plan['original_root'] == str(ORIGINAL_ROOT) and
         plan['original_pipeline_root'] == str(ORIGINAL_PIPELINE) and
         plan['new_postprocess_root'] == str(ROOT), 'receipt roots differ')
    rows = plan['original_receipts']
    need(len(rows) == 22 and len({row['path'] for row in rows}) == 22,
         'exact original receipt set required')
    result = {}
    for row in rows:
        group, relative = row['path'].split('/', 1)
        need(group in {'signed', 'pipeline'} and '..' not in Path(relative).parts and
             not Path(relative).is_absolute(), 'invalid original receipt path')
        root = ORIGINAL_ROOT if group == 'signed' else ORIGINAL_PIPELINE
        path = root / relative
        need(str(path) == row['original_path'], 'original absolute receipt path differs')
        raw = read_file(path)
        need({'bytes': len(raw), 'sha256': sha(raw)} ==
             {key: row[key] for key in ('bytes', 'sha256')},
             'original receipt bytes changed: ' + str(path))
        result[row['path']] = raw
    expected = {row['path'].removeprefix('signed/') for row in rows
                if row['path'].startswith('signed/')}
    paths = list(ORIGINAL_ROOT.rglob('*'))
    need(not ORIGINAL_ROOT.is_symlink() and not any(path.is_symlink() for path in paths),
         'original supplement directory contains a symlink')
    actual = {str(path.relative_to(ORIGINAL_ROOT)) for path in paths if path.is_file()}
    need(actual == expected, 'original supplement gained or lost files; hold for separate review')
    for name in plan['original_required_absences']:
        need(not (ORIGINAL_ROOT / name).exists(), 'original absent result was created: ' + name)
    return result


def exact_events(tail, plan, old):
    """No filtering: the entire ordered event list must equal both frozen rows."""
    events = [json.loads(line) for line in tail.splitlines()]
    need(len(events) == 2 and events == plan['expected_guard_events_exactly_in_order'],
         'exact original metadata query then sole audit event required')
    query, audit = events
    input_args = ['-DmaxRecDepth=100000', '-DmaxHeartbeats=4000000',
                  '--root=' + str(ORIGINAL_ROOT / 'inputs'),
                  str(ORIGINAL_ROOT / 'inputs/OwnedOnlyAudit.lean')]
    for event in events:
        need(set(event) == {'pid', 'tool', 'command', 'input_args', 'slot_owner', 'cwd', 'sysroot'} and
             type(event['pid']) is int and event['pid'] > 0 and event['slot_owner'] == str(event['pid']) and
             event['tool'] == 'lean' and event['cwd'] == str(old.PROJECT) and
             event['sysroot'] == str(Path(old.LEAN_RUNTIME).parent.parent),
             'original event runtime, slot ownership or schema differs')
    need(query['input_args'] == ['--githash'] and
         query['command'] == [old.LEAN_RUNTIME, '-t0', '-j2', '-M12288', '--githash'],
         'first event is not the exact original runtime metadata query')
    need(audit['input_args'] == input_args and
         audit['command'] == [old.LEAN_RUNTIME] + old.RESOURCES + input_args[2:] and
         query['pid'] != audit['pid'], 'second event is not the sole original audit')
    return events


def validate_receipts(plan, raw, old, manifest, legacy, original_driver, manifest_raw):
    """Pure receipt verification, reusing the unmodified complete-owned parser."""
    need(set(raw) == {row['path'] for row in plan['original_receipts']},
         'provided receipt set differs')
    for row in plan['original_receipts']:
        data = raw[row['path']]
        need(len(data) == row['bytes'] and sha(data) == row['sha256'],
             'raw receipt digest differs: ' + row['path'])
    get = lambda name: json.loads(raw[name])
    need(raw['signed/executed-driver.py'] == original_driver == raw['pipeline/signed-owned-only.py'] and
         sha(original_driver) == ORIGINAL_DRIVER_SHA and
         raw['signed/inputs/MANIFEST.json'] == manifest_raw and sha(manifest_raw) == ORIGINAL_MANIFEST_SHA and
         raw['signed/inputs/OwnedOnlyAudit.lean'] == legacy['audit_bytes'],
         'original executing driver, manifest or audit body differs')
    for kind in ('normal', 'kernel'):
        for suffix in ('-command.json', '.log'):
            name = SHORT + '-' + kind + suffix
            need(raw['signed/inputs/legacy/' + name] == legacy['raw'][old.LEGACY_PREFIX + name],
                 'original primary evidence copy differs: ' + name)
    binding = get('signed/BINDING.json')
    before = get('signed/run/LIVE_BEFORE.json')
    after = get('signed/run/LIVE_AFTER.json')
    need(before == after == binding['live_before'] and before['source_plus_five'] == legacy['snapshot'],
         'original live source-plus-five/runtime/configuration/protected roots changed')
    need(binding == {
        'schema': 'p14_signed_owned_only_execution_binding_v1',
        'source_commit': ORIGINAL_SOURCE, 'module': MODULE,
        'driver_sha256': sha(original_driver), 'manifest_sha256': sha(manifest_raw),
        'audit_sha256': sha(legacy['audit_bytes']), 'legacy_evidence_commit': old.LEGACY_COMMIT,
        'legacy_review_sha256': old.LEGACY_REVIEW_SHA, 'live_before': before,
        'normal_kernel_reexecution_permitted': False, 'whole_P1_4_complete': False,
    }, 'original execution binding differs')
    need(raw['signed/run/GIT_BEFORE.json'] == raw['signed/run/GIT_AFTER.json'],
         'original Git state changed across its failed wrapper')
    lane = get('signed/run/VALIDATION_LANE.json')
    need(lane['status'] == 'VALIDATION_LANE_FINISHED' and lane['exit_code'] == 1 and
         lane['state'] == old.STATE and lane['state_sha256'] == before['runtime'][old.STATE]['sha256'] and
         lane['argv'] == ['python3', '-B', str(ORIGINAL_ROOT / 'executed-driver.py'),
                          '--source-commit', ORIGINAL_SOURCE, '--run', '--worker'] and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'original failed serialized execution was changed')
    events = exact_events(raw['signed/run/ACTUAL_GUARD_JOURNAL_TAIL.jsonl'], plan, old)
    command = get('signed/run/audit-command.json')
    started = get('signed/run/audit-started.json')
    expected_argv = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', old.STATE,
                     'lake', 'env', 'lean'] + events[1]['input_args']
    need(command['argv'] == expected_argv and command['cwd'] == str(old.PROJECT) and
         command['exit_code'] == 0 and command['actual_built_modules'] == [] and
         command['log'] == str(ORIGINAL_ROOT / 'run/audit.log') and
         command['log_sha256'] == sha(raw['signed/run/audit.log']) and
         started == {key: command[key] for key in ('argv', 'cwd', 'started_utc')},
         'original sole audit command, successful exit or log differs')
    failure_log = raw['pipeline/outputs/signed-owned-only.log'].decode()
    need(failure_log.endswith('RuntimeError: ' + FAILURE + '\n') and
         "need(len(events) == 1, '" + FAILURE + "')" in failure_log,
         'original wrapper failure point differs')
    check = get('pipeline/checks/signed-owned-only.log')
    need(check == {'status': 'READ_ONLY_LEGACY_IDENTITY_CHECK_PASS_NOT_ACCEPTANCE',
                   **binding, 'existing_execution_present': False},
         'original read-only identity check differs')
    pipeline = get('pipeline/PIPELINE_RESULT.json')
    candidate = get('pipeline/CANDIDATE_BINDING.json')
    need(pipeline['source_commit'] == candidate['source_commit'] == ORIGINAL_SOURCE and
         pipeline['checks'] == candidate['checks'] and
         pipeline['whole_P1_4_complete'] is False and candidate['whole_P1_4_complete'] is False and
         pipeline['new_normal_invocations'] == 0 and MODULE not in pipeline['accepted_owners'],
         'original pipeline source or failed-owner boundary differs')
    signed_checks = [row for row in pipeline['checks'] if row['name'] == 'signed-owned-only']
    need(signed_checks == [{'name': 'signed-owned-only', 'exit_code': 0,
                            'log_sha256': sha(raw['pipeline/checks/signed-owned-only.log'])}],
         'original pipeline check linkage differs')
    signed_stages = [row for row in pipeline['stages'] if row['name'] == 'signed-owned-only']
    need(signed_stages == [{
        'name': 'signed-owned-only', 'module': MODULE, 'exit_code': 1,
        'caller_log_sha256': sha(raw['pipeline/outputs/signed-owned-only.log']),
        'accepted_owners': [], 'status': 'HELD_OR_FAILED_NO_SUPPLEMENT_RESULT',
    }], 'original failed stage or missing-result status was changed')
    signed_specs = [row for row in candidate['specs'] if row['name'] == 'signed-owned-only']
    need(signed_specs == [{
        'name': 'signed-owned-only', 'path': ORIGINAL_DRIVER, 'sha256': ORIGINAL_DRIVER_SHA,
        'module': MODULE, 'source_sha256': legacy['snapshot'][SOURCE]['sha256'],
        'check_status': 'READ_ONLY_LEGACY_IDENTITY_CHECK_PASS_NOT_ACCEPTANCE',
        'result_path': str(ORIGINAL_ROOT / 'run/SIGNED_COMPLETE_OWNED_SUPPLEMENT_RESULT.json'),
        'result_status': 'PASS_LEGACY_NORMAL_KERNEL_PLUS_COMPLETE_OWNED_SUPPLEMENT',
        'new_kernel_invocations': 0,
    }], 'original pipeline caller specification differs')
    records = old.read_owned(raw['signed/run/audit.log'].decode(), legacy['public'])
    return {'records': records, 'original_live': before, 'original_binding': binding,
            'audit_command': command, 'original_lane': lane, 'actual_guard_events': events}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    need(re.fullmatch(r'[0-9a-f]{40}', source) is not None, 'full published recovery source commit required')
    driver = Path(__file__).read_bytes()
    need(driver == git(source, DRIVER), 'executing postprocessor differs from published source')
    plan_raw = git(source, PLAN)
    need(sha(plan_raw) == PLAN_SHA, 'fixed receipt recovery plan differs')
    plan = json.loads(plan_raw)
    need(plan['schema'] == 'p14_signed_exact_two_event_receipt_postprocess_plan_v1' and
         plan['module'] == MODULE and plan['original_supplement_source_commit'] == ORIGINAL_SOURCE and
         plan['whole_P1_4_complete'] is False and plan['preparation_is_acceptance'] is False,
         'postprocess scope changed')
    original_driver = git(ORIGINAL_SOURCE, ORIGINAL_DRIVER)
    need(sha(original_driver) == ORIGINAL_DRIVER_SHA and len(original_driver) == 20392,
         'unchanged original Signed caller required')
    old = load(original_driver, 'unchanged_original_signed_supplement')
    manifest_raw = git(ORIGINAL_SOURCE, old.MANIFEST)
    need(sha(manifest_raw) == ORIGINAL_MANIFEST_SHA, 'original supplement manifest changed')
    manifest = json.loads(manifest_raw)
    legacy = old.legacy_inputs(REPO, manifest)
    need(git(ORIGINAL_SOURCE, SOURCE) == git(source, SOURCE) == legacy['raw'][SOURCE],
         'original or claimed recovery source changed the Signed theorem module')
    need(old.pinned(REPO, ORIGINAL_SOURCE, manifest['audit_template']) == legacy['audit_bytes'],
         'original audit template changed')
    helpers = [old.pinned(REPO, old.TOOLS_COMMIT, row) for row in manifest['immutable_helpers']]
    need([row['path'] for row in manifest['immutable_helpers']] == list(old.HELPERS),
         'original helper order changed')
    h, d = [old.load(raw, name) for raw, name in zip(helpers, ('unchanged_batch5', 'unchanged_batch10'))]
    review_raw = read_file(old.REVIEW)
    need(sha(review_raw) == old.REVIEW_SHA, 'original runtime review differs')
    review = json.loads(review_raw)
    raw = read_original_receipts(plan)
    validated = validate_receipts(plan, raw, old, manifest, legacy, original_driver, manifest_raw)
    current = old.live_binding(h, d, review, legacy)
    need(current == validated['original_live'], 'live binding no longer equals the original completed audit')
    binding = {
        'schema': 'p14_signed_receipt_postprocess_execution_binding_v1',
        'source_commit': source, 'module': MODULE, 'driver_sha256': sha(driver),
        'plan_sha256': sha(plan_raw), 'original_supplement_source_commit': ORIGINAL_SOURCE,
        'original_driver_sha256': sha(original_driver),
        'original_receipts': plan['original_receipts'], 'live_before': current,
        'new_normal_invocations': 0, 'new_kernel_invocations': 0, 'new_full_owned_audit_invocations': 0,
        'whole_P1_4_complete': False,
    }
    run = ROOT / 'run'
    if args.check:
        need(not args.worker, '--worker is unavailable for the read-only check')
        print(json.dumps({'status': 'READ_ONLY_EXACT_RECEIPT_POSTPROCESS_CHECK_PASS_NOT_ACCEPTANCE',
                          **binding, 'existing_postprocess_present': run.exists()}), flush=True)
        return 0
    if not args.worker:
        need(not run.exists(), 'existing postprocess held for receipt review; no overwrite or repetition')
        before_git = d.original_git_state(REPO)
        d.save(ROOT / 'BINDING.json', binding)
        d.write_frozen(ROOT / 'inputs/RECOVERY_PLAN.json', plan_raw)
        d.write_frozen(ROOT / 'inputs/ORIGINAL_CALLER.py', original_driver)
        executed = ROOT / 'executed-driver.py'
        d.write_frozen(executed, driver)
        run.mkdir()
        d.save(run / 'GIT_BEFORE.json', before_git)
        child = ['python3', '-B', str(executed), '--source-commit', source, '--run', '--worker']
        try:
            return subprocess.run(h.serialize(0, run / 'VALIDATION_LANE.json', child)).returncode
        finally:
            after_git = d.original_git_state(REPO)
            d.save(run / 'GIT_AFTER.json', after_git)
            need(before_git == after_git, 'Git checkout changed during receipt postprocessing')
            need(read_original_receipts(plan) == raw, 'original receipts changed during postprocessing')
    d.verify_lane(h)
    lane = json.loads(read_file(run / 'VALIDATION_LANE.json'))
    need(lane['status'] == 'VALIDATION_LANE_ACQUIRED' and lane['state'] == old.STATE,
         'original serializer did not acquire lane 0')
    need(json.loads(read_file(ROOT / 'BINDING.json')) == binding and
         read_file(ROOT / 'inputs/RECOVERY_PLAN.json') == plan_raw and
         read_file(ROOT / 'inputs/ORIGINAL_CALLER.py') == original_driver,
         'frozen postprocess inputs changed during lane acquisition')
    state_raw = read_file(old.STATE)
    need(sha(state_raw) == current['runtime'][old.STATE]['sha256'], 'runtime state changed')
    journal = Path(json.loads(state_raw)['log'])
    stat_before = journal.stat()
    d.save(run / 'LIVE_BEFORE.json', current)
    records = validated['records']
    d.save(run / 'OWNED_EXPORTS.json', records)
    d.save(run / 'PUBLIC_EXPORTS.json', [row for row in records if not row['is_private']])
    after = old.live_binding(h, d, review, legacy)
    d.save(run / 'LIVE_AFTER.json', after)
    need(after == current and read_original_receipts(plan) == raw,
         'current objects, runtime, protected roots or original receipts changed')
    stat_after = journal.stat()
    need((stat_before.st_dev, stat_before.st_ino, stat_before.st_size) ==
         (stat_after.st_dev, stat_after.st_ino, stat_after.st_size),
         'postprocessing must produce zero new guard events')
    d.save(run / 'POSTPROCESS_RUNTIME_EVIDENCE.json', {
        'state': old.STATE, 'state_sha256': sha(state_raw), 'journal': str(journal),
        'postprocess_before_byte_offset': stat_before.st_size,
        'postprocess_after_byte_offset': stat_after.st_size, 'new_guard_events': 0,
        'reused_original_tail_path': str(ORIGINAL_ROOT / 'run/ACTUAL_GUARD_JOURNAL_TAIL.jsonl'),
        'reused_original_tail_sha256': sha(raw['signed/run/ACTUAL_GUARD_JOURNAL_TAIL.jsonl']),
        'reused_original_events': validated['actual_guard_events'],
        'original_journal_byte_offsets_unavailable_not_reconstructed': True,
    })
    result = {
        'schema': 'p14_signed_existing_audit_receipt_postprocess_result_v1',
        'status': 'PASS_POSTPROCESSED_EXISTING_AUDIT_LEGACY_NORMAL_KERNEL_COMPLETE_OWNED',
        'source_commit': source, 'module': MODULE, 'source_sha256': legacy['snapshot'][SOURCE]['sha256'],
        'original_supplement_source_commit': ORIGINAL_SOURCE,
        'original_failed_task_id': plan['original_task_id'],
        'original_task_exit_code': 1, 'original_validation_lane_exit_code': 1,
        'original_pipeline_signed_status': 'HELD_OR_FAILED_NO_SUPPLEMENT_RESULT',
        'original_result_absence_preserved': True, 'original_failure_preserved': True,
        'legacy_evidence_commit': old.LEGACY_COMMIT, 'legacy_primary_commands': legacy['commands'],
        'legacy_primary_evidence': manifest['frozen_primary_evidence'],
        'original_receipts': plan['original_receipts'], 'audit_command_reused': validated['audit_command'],
        'new_normal_invocations': 0, 'new_kernel_invocations': 0, 'new_full_owned_audit_invocations': 0,
        'existing_full_owned_audit_invocations_reused': 1,
        'exact_original_guard_events': 2, 'original_runtime_metadata_queries': 1,
        'owned_total': len(records), 'public_total': sum(not row['is_private'] for row in records),
        'private_total': sum(row['is_private'] for row in records),
        'full_owned_including_private_generated': True, 'full_types_AST_universes_std3_axioms': True,
        'original_seven_public_AST_universes_axioms_unchanged': True,
        'source_plus_five_exact_original_and_unchanged': True,
        'original_read_owned_function_unchanged': True,
        'accepted_owners_by_this_independent_postprocess': [MODULE], 'whole_P1_4_complete': False,
    }
    d.save(run / RESULT_NAME, result)
    print(json.dumps(result), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
