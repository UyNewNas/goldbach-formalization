#!/usr/bin/env python3
"""Resume one strictly unstarted receipt-only wait in a separate output root.

The original timed-out postprocessor and its missing outputs remain untouched.
The published predecessor's pure receipt checks and the original Signed
legacy/owned/live validators are called without replacing their globals.
Only the unchanged serializer may start this new worker. No normal build,
kernel replay, full-owned audit, source installation or outer lock is used.
"""
import argparse
import base64
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError('P1.4 receipt-only resume forbids optimized Python')

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PREFIX = 'docs/p1/20261128/p14-signed-owned-supplement/'
RESUME_DRIVER = PREFIX + 'resume_signed_owned_receipt.py'
RESUME_PLAN = PREFIX + 'SIGNED_RECEIPT_RESUME_PLAN.json'
RESUME_PLAN_SHA = '035d08906f5c3f9e3aa302deb6e009e274eb6246a1fc16612d8086e746b69cb0'
RESUME_ROOT = Path('/workspace/p1-complete-proof/20261128-p14-signed-owned-postprocess-resume')
RESULT_NAME = 'SIGNED_RECEIPT_RESUME_RESULT.json'
PREDECESSOR_SOURCE = '9aa63b9a82b25f03ea12f622a718aafb65d551cb'
WAIT_ROOT = Path('/workspace/p1-complete-proof/20261128-p14-signed-owned-postprocess')
MODULE = 'ImbalancedChen.P5OriginalSignedMidpoint'
SOURCE = MODULE.replace('.', '/') + '.lean'


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


def check_pin(raw, specification, label):
    need(len(raw) == specification['bytes'] and sha(raw) == specification['sha256'], label)


def unwrap_original_tool(value):
    if isinstance(value.get('structuredContent'), dict):
        return value['structuredContent']
    text = [row['text'] for row in value['content'] if row['type'] == 'text']
    need(len(text) == 1 and value.get('isError') is not True, 'original tool response differs')
    return json.loads(text[0])


def complete_original_output(transport, group, pin):
    task = unwrap_original_tool(transport[group + '_task'])
    pages = [unwrap_original_tool(row) for row in transport[group + '_pages']]
    need(task['task_id'] == pin['task_id'] and not task['output_truncated'] and
         sha(task['command'].encode()) == pin['command_sha256'] and len(pages) == pin['complete_pages'],
         'original task or complete page scope differs: ' + group)
    chunks, offset = [], 0
    for number, page in enumerate(pages):
        raw = base64.b64decode(page['data_base64'], validate=True)
        need(page['task_id'] == task['task_id'] and page['offset'] == offset and
             page['next_offset'] == offset + len(raw) and page['bytes'] == len(raw) and
             page['eof'] is (number == len(pages) - 1) and not page['output_truncated'],
             'original output page chain differs: ' + group)
        chunks.append(raw)
        offset = page['next_offset']
    output = b''.join(chunks)
    need(len(output) == task['output_bytes'] == pin['stdout_bytes'] and sha(output) == pin['stdout_sha256'],
         'original complete output bytes differ: ' + group)
    return task, output


def validate_observation(raw, plan):
    """Read the historical timeout/probe evidence; infer no present lock state."""
    specification = plan['observation_transport']
    check_pin(raw, specification, 'fixed original observation transport differs')
    transport = json.loads(raw)
    need(transport['schema'] == specification['schema'] and transport['whole_P1_4_complete'] is False and
         transport['observation_is_time_specific_not_global_lock_owner_evidence'] is True,
         'historical observation scope differs')
    task, output = complete_original_output(transport, 'signed_postprocess', specification['signed_postprocess'])
    probe, probe_output = complete_original_output(transport, 'read_only_observation', specification['read_only_observation'])
    wait = plan['original_wait']
    need(task['task_id'] == wait['task_id'] and task['status'] == wait['task_status'] == 'timed_out' and
         task['exit_code'] == wait['task_exit_code'] == -9 and
         task['timeout_seconds'] == wait['timeout_seconds'] == 300 and
         task['runtime_seconds'] == wait['runtime_seconds'] and task['cancel_requested'] is False,
         'original postprocessor terminal timeout observation differs')
    need(probe['status'] == 'succeeded' and probe['exit_code'] == 0, 'original observation task was not successful')
    checks = [json.loads(line) for line in output.decode().splitlines() if line.startswith('{')]
    need(len(checks) == 1 and checks[0]['status'] ==
         'READ_ONLY_EXACT_RECEIPT_POSTPROCESS_CHECK_PASS_NOT_ACCEPTANCE' and
         checks[0]['source_commit'] == PREDECESSOR_SOURCE and
         checks[0]['existing_postprocess_present'] is False and
         all(checks[0][key] == 0 for key in
             ('new_normal_invocations', 'new_kernel_invocations', 'new_full_owned_audit_invocations')),
         'original receipt-only preflight observation differs')
    observed = json.loads(probe_output)
    rows = observed['signed_postprocess_original_files']
    present = [row for row in rows if row['exists']]
    expected_observed = {row['path']: row for row in wait['expected_files']
                         if row['pin_basis'] == 'original read-only observation task raw-file size and SHA256'}
    need(len(present) == len(expected_observed) == 3 and
         {row['path'].removeprefix(str(WAIT_ROOT) + '/') for row in present} == set(expected_observed),
         'original three waiting-file observations differ')
    for row in present:
        relative = row['path'].removeprefix(str(WAIT_ROOT) + '/')
        need({key: row[key] for key in ('bytes', 'sha256')} ==
             {key: expected_observed[relative][key] for key in ('bytes', 'sha256')},
             'original waiting-file raw pin differs: ' + relative)
    absent = [row['path'].removeprefix(str(WAIT_ROOT) + '/') for row in rows if not row['exists']]
    need(absent == wait['observed_absences'] and
         next(row['original_receipt'] for row in present if row['path'].endswith('/VALIDATION_LANE.json')) ==
         wait['exact_original_lane_receipt'] and observed['no_lock_source_compiler_or_receipt_modified'] is True and
         observed['whole_P1_4_complete'] is False, 'original waiting status or absences differ')
    # observed['validation_lane'] is a past probe result, not an execution gate.
    # The unchanged serializer is solely responsible for acquiring the new lane.
    return {'task': task, 'original_check_binding': {key: value for key, value in checks[0].items()
            if key not in {'status', 'existing_postprocess_present'}}}


def read_waiting_originals(plan, predecessor):
    """Require all original frozen inputs and the strict never-started state."""
    wait = plan['original_wait']
    need(wait['root'] == str(WAIT_ROOT) == str(predecessor.ROOT) and
         len(wait['expected_files']) == 6 and len({row['path'] for row in wait['expected_files']}) == 6,
         'original waiting root or exact frozen-input scope differs')
    need(WAIT_ROOT.is_dir() and all(not path.is_symlink() for path in (WAIT_ROOT, *WAIT_ROOT.parents)),
         'original waiting root is missing or symlinked')
    paths = list(WAIT_ROOT.rglob('*'))
    need(not any(path.is_symlink() for path in paths), 'original waiting root contains a symlink')
    expected = {row['path'] for row in wait['expected_files']}
    need({str(path.relative_to(WAIT_ROOT)) for path in paths if path.is_file()} == expected,
         'original waiting root gained or lost files; resume is not authorized for a started worker')
    raw = {}
    for row in wait['expected_files']:
        relative = Path(row['path'])
        need(not relative.is_absolute() and '..' not in relative.parts, 'invalid original waiting-file path')
        data = predecessor.read_file(WAIT_ROOT / relative)
        check_pin(data, row, 'original waiting-file changed: ' + row['path'])
        raw[row['path']] = data
    for relative in wait['required_absences']:
        path = WAIT_ROOT / relative
        need(not path.exists() and not path.is_symlink(), 'original waiting worker output now exists: ' + relative)
    return raw


def validate_waiting_bytes(plan, raw, observation, predecessor, predecessor_driver, predecessor_plan_raw,
                           original_driver, original_receipts, current, current_git):
    """Bind the original timeout to the exact live objects, Git state and inputs."""
    get = lambda name: json.loads(raw[name])
    for row in plan['original_wait']['expected_files']:
        check_pin(raw[row['path']], row, 'original waiting raw bytes differ: ' + row['path'])
    need(set(raw) == {row['path'] for row in plan['original_wait']['expected_files']},
         'original waiting raw file set differs')
    need(raw['executed-driver.py'] == predecessor_driver and
         raw['inputs/RECOVERY_PLAN.json'] == predecessor_plan_raw and
         raw['inputs/ORIGINAL_CALLER.py'] == original_driver, 'original waiting frozen source inputs differ')
    recovery_plan = json.loads(predecessor_plan_raw)
    expected_binding = {
        'schema': 'p14_signed_receipt_postprocess_execution_binding_v1',
        'source_commit': PREDECESSOR_SOURCE, 'module': MODULE, 'driver_sha256': sha(predecessor_driver),
        'plan_sha256': sha(predecessor_plan_raw),
        'original_supplement_source_commit': predecessor.ORIGINAL_SOURCE,
        'original_driver_sha256': sha(original_driver),
        'original_receipts': recovery_plan['original_receipts'], 'live_before': current,
        'new_normal_invocations': 0, 'new_kernel_invocations': 0, 'new_full_owned_audit_invocations': 0,
        'whole_P1_4_complete': False,
    }
    need(get('BINDING.json') == expected_binding == observation['original_check_binding'],
         'original wait binding, original check and current live identity differ')
    need(get('run/GIT_BEFORE.json') == current_git and
         raw['run/GIT_BEFORE.json'] == original_receipts['signed/run/GIT_BEFORE.json'] ==
         original_receipts['signed/run/GIT_AFTER.json'], 'current/original waiting/legacy Git state differs')
    lane = get('run/VALIDATION_LANE.json')
    need(lane == plan['original_wait']['exact_original_lane_receipt'] and
         lane['status'] == 'WAITING_VALIDATION_LANE' and lane['state'] ==
         '/workspace/blue-build-tools/member-runtime-evidence/state.json' and
         lane['state_sha256'] == current['runtime'][lane['state']]['sha256'] and
         lane['argv'] == ['python3', '-B', str(WAIT_ROOT / 'executed-driver.py'),
                          '--source-commit', PREDECESSOR_SOURCE, '--run', '--worker'] and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'original exact never-acquired lane receipt differs')
    return {'source_commit': PREDECESSOR_SOURCE, 'root': str(WAIT_ROOT),
            'task_id': plan['original_wait']['task_id'], 'task_status': 'timed_out', 'task_exit_code': -9,
            'lane_status': 'WAITING_VALIDATION_LANE',
            'original_files': {name: {'bytes': len(data), 'sha256': sha(data)} for name, data in raw.items()},
            'required_absences': plan['original_wait']['required_absences'],
            'worker_never_started_receipt_condition_verified': True,
            'current_live_and_git_equal_original_wait': True,
            'original_git_after_absence_preserved': True,
            'historical_probe_is_not_current_availability_or_owner_evidence': True}


def prepare(source, driver, plan_raw):
    plan = json.loads(plan_raw)
    need(plan['schema'] == 'p14_signed_strict_unstarted_wait_resume_plan_v1' and plan['module'] == MODULE and
         plan['driver_path'] == RESUME_DRIVER and plan['resume_root'] == str(RESUME_ROOT) and
         plan['result_name'] == RESULT_NAME and plan['predecessor_source_commit'] == PREDECESSOR_SOURCE and
         plan['preparation_is_acceptance'] is False and plan['whole_P1_4_complete'] is False,
         'strict resume plan scope differs')
    previous_raw = git(PREDECESSOR_SOURCE, plan['predecessor_driver']['path'])
    check_pin(previous_raw, plan['predecessor_driver'], 'unchanged original postprocessor differs')
    predecessor = load(previous_raw, 'unchanged_signed_receipt_postprocessor')
    need(str(predecessor.ROOT) == str(WAIT_ROOT) and predecessor.DRIVER == plan['predecessor_driver']['path'] and
         predecessor.PLAN == plan['predecessor_plan']['path'] and predecessor.PLAN_SHA ==
         plan['predecessor_plan']['sha256'], 'original postprocessor globals differ')
    previous_plan_raw = git(PREDECESSOR_SOURCE, predecessor.PLAN)
    check_pin(previous_plan_raw, plan['predecessor_plan'], 'unchanged original postprocessor plan differs')
    need(git(source, predecessor.DRIVER) == previous_raw and git(source, predecessor.PLAN) == previous_plan_raw,
         'resume source changed the original postprocessor or its plan')
    for row in plan['immutable_original_files']:
        original = git(PREDECESSOR_SOURCE, row['path'])
        check_pin(original, row, 'original five-file Signed bundle changed')
        need(git(source, row['path']) == original, 'resume source changed the original Signed bundle')
    observation_raw = git(source, plan['observation_transport']['path'])
    observation = validate_observation(observation_raw, plan)
    recovery_plan = json.loads(previous_plan_raw)
    need(recovery_plan['schema'] == 'p14_signed_exact_two_event_receipt_postprocess_plan_v1' and
         recovery_plan['module'] == MODULE and len(recovery_plan['original_receipts']) == 22 and
         recovery_plan['original_supplement_source_commit'] == predecessor.ORIGINAL_SOURCE ==
         plan['original_supplement_source_commit'] and recovery_plan['whole_P1_4_complete'] is False and
         recovery_plan['preparation_is_acceptance'] is False, 'original pure-receipt plan scope differs')
    original_driver = git(predecessor.ORIGINAL_SOURCE, predecessor.ORIGINAL_DRIVER)
    need(sha(original_driver) == predecessor.ORIGINAL_DRIVER_SHA and len(original_driver) == 20392,
         'unchanged original Signed caller required')
    old = predecessor.load(original_driver, 'unchanged_original_signed_supplement')
    manifest_raw = git(predecessor.ORIGINAL_SOURCE, old.MANIFEST)
    need(sha(manifest_raw) == predecessor.ORIGINAL_MANIFEST_SHA, 'original supplement manifest differs')
    manifest = json.loads(manifest_raw)
    legacy = old.legacy_inputs(REPO, manifest)
    need(git(predecessor.ORIGINAL_SOURCE, SOURCE) == git(PREDECESSOR_SOURCE, SOURCE) ==
         git(source, SOURCE) == legacy['raw'][SOURCE], 'Signed theorem source changed')
    need(old.pinned(REPO, predecessor.ORIGINAL_SOURCE, manifest['audit_template']) == legacy['audit_bytes'],
         'original audit template changed')
    helpers = [old.pinned(REPO, old.TOOLS_COMMIT, row) for row in manifest['immutable_helpers']]
    need([row['path'] for row in manifest['immutable_helpers']] == list(old.HELPERS), 'original helper order changed')
    h, d = [old.load(raw, name) for raw, name in zip(helpers, ('unchanged_batch5', 'unchanged_batch10'))]
    review_raw = predecessor.read_file(old.REVIEW)
    need(sha(review_raw) == old.REVIEW_SHA, 'original runtime review differs')
    review = json.loads(review_raw)
    original_receipts = predecessor.read_original_receipts(recovery_plan)
    validated = predecessor.validate_receipts(recovery_plan, original_receipts, old, manifest, legacy,
                                              original_driver, manifest_raw)
    current = old.live_binding(h, d, review, legacy)
    need(current == validated['original_live'], 'live binding no longer equals the completed original audit')
    current_git = d.original_git_state(REPO)
    waiting = read_waiting_originals(plan, predecessor)
    wait_summary = validate_waiting_bytes(plan, waiting, observation, predecessor, previous_raw,
        previous_plan_raw, original_driver, original_receipts, current, current_git)
    binding = {
        'schema': 'p14_signed_strict_receipt_resume_execution_binding_v1',
        'source_commit': source, 'module': MODULE, 'driver_sha256': sha(driver), 'plan_sha256': sha(plan_raw),
        'predecessor_source_commit': PREDECESSOR_SOURCE, 'predecessor_driver_sha256': sha(previous_raw),
        'predecessor_plan_sha256': sha(previous_plan_raw),
        'original_supplement_source_commit': predecessor.ORIGINAL_SOURCE,
        'original_receipts': recovery_plan['original_receipts'], 'original_wait': wait_summary,
        'live_before': current, 'original_git_before': current_git,
        'new_normal_invocations': 0, 'new_kernel_invocations': 0, 'new_full_owned_audit_invocations': 0,
        'whole_P1_4_complete': False,
    }
    return {'plan': plan, 'predecessor': predecessor, 'previous_raw': previous_raw,
            'previous_plan_raw': previous_plan_raw, 'recovery_plan': recovery_plan,
            'observation_raw': observation_raw, 'observation': observation, 'original_driver': original_driver,
            'old': old, 'manifest': manifest, 'legacy': legacy, 'h': h, 'd': d, 'review': review,
            'original_receipts': original_receipts, 'validated': validated, 'current': current,
            'current_git': current_git, 'waiting': waiting, 'wait_summary': wait_summary, 'binding': binding}


def check_preserved(context):
    predecessor, old = context['predecessor'], context['old']
    need(predecessor.read_original_receipts(context['recovery_plan']) == context['original_receipts'],
         'one of the 22 original Signed receipts or original required absences changed')
    waiting = read_waiting_originals(context['plan'], predecessor)
    need(waiting == context['waiting'], 'original timed-out waiting files changed')
    current = old.live_binding(context['h'], context['d'], context['review'], context['legacy'])
    current_git = context['d'].original_git_state(REPO)
    need(current == context['current'] and current_git == context['current_git'],
         'original live objects, runtime, protected roots or Git changed')
    summary = validate_waiting_bytes(context['plan'], waiting, context['observation'], predecessor,
        context['previous_raw'], context['previous_plan_raw'], context['original_driver'],
        context['original_receipts'], current, current_git)
    need(summary == context['wait_summary'], 'original waiting state was reclassified')
    return current, current_git, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--worker', action='store_true', help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    need(re.fullmatch(r'[0-9a-f]{40}', source) is not None, 'full published resume source commit required')
    driver = Path(__file__).read_bytes()
    need(driver == git(source, RESUME_DRIVER), 'executing resume caller differs from published source')
    plan_raw = git(source, RESUME_PLAN)
    need(sha(plan_raw) == RESUME_PLAN_SHA, 'fixed strict resume plan differs')
    context = prepare(source, driver, plan_raw)
    d, h, old = context['d'], context['h'], context['old']
    binding, current = context['binding'], context['current']
    run = RESUME_ROOT / 'run'
    if args.check:
        need(not args.worker, '--worker is unavailable for the read-only resume check')
        print(json.dumps({'status': 'READ_ONLY_STRICT_UNSTARTED_WAIT_RESUME_CHECK_PASS_NOT_ACCEPTANCE',
                          **binding, 'existing_resume_present': RESUME_ROOT.exists()}), flush=True)
        return 0
    if not args.worker:
        need(not RESUME_ROOT.exists(), 'existing independent resume output must be inspected, never overwritten or repeated')
        # Exclusive new output directory, not a lock and never the old waiting directory.
        RESUME_ROOT.mkdir()
        d.save(RESUME_ROOT / 'BINDING.json', binding)
        inputs = {'RESUME_PLAN.json': plan_raw, 'PREDECESSOR_RECOVERY_PLAN.json': context['previous_plan_raw'],
                  'PREDECESSOR_RECOVERY_CALLER.py': context['previous_raw'],
                  'ORIGINAL_SIGNED_CALLER.py': context['original_driver'],
                  'ORIGINAL_WAIT_OBSERVATIONS.json': context['observation_raw']}
        for name, raw in inputs.items():
            d.write_frozen(RESUME_ROOT / 'inputs' / name, raw)
        for relative, raw in context['waiting'].items():
            d.write_frozen(RESUME_ROOT / 'inputs/original-wait' / relative, raw)
        executed = RESUME_ROOT / 'executed-driver.py'
        d.write_frozen(executed, driver)
        run.mkdir()
        d.save(run / 'GIT_BEFORE.json', context['current_git'])
        d.save(run / 'OLD_WAIT_BEFORE.json', context['wait_summary'])
        child = ['python3', '-B', str(executed), '--source-commit', source, '--run', '--worker']
        try:
            return subprocess.run(h.serialize(0, run / 'VALIDATION_LANE.json', child)).returncode
        finally:
            after, after_git, summary = check_preserved(context)
            d.save(run / 'GIT_AFTER.json', after_git)
            d.save(run / 'OLD_WAIT_AFTER.json', summary)
    d.verify_lane(h)
    read = context['predecessor'].read_file
    lane = json.loads(read(run / 'VALIDATION_LANE.json'))
    need(lane['status'] == 'VALIDATION_LANE_ACQUIRED' and lane['state'] == old.STATE and
         lane['state_sha256'] == current['runtime'][old.STATE]['sha256'] and
         lane['argv'] == ['python3', '-B', str(RESUME_ROOT / 'executed-driver.py'),
                          '--source-commit', source, '--run', '--worker'] and
         lane['no_compiler_guard_runtime_or_memory_limit_changes'] is True and
         lane['whole_chain_including_original_checker_serialized'] is True,
         'unchanged serializer did not acquire the exact new resume lane')
    need(json.loads(read(RESUME_ROOT / 'BINDING.json')) == binding and
         read(RESUME_ROOT / 'inputs/RESUME_PLAN.json') == plan_raw and
         read(RESUME_ROOT / 'inputs/PREDECESSOR_RECOVERY_PLAN.json') == context['previous_plan_raw'] and
         read(RESUME_ROOT / 'inputs/PREDECESSOR_RECOVERY_CALLER.py') == context['previous_raw'] and
         read(RESUME_ROOT / 'inputs/ORIGINAL_SIGNED_CALLER.py') == context['original_driver'] and
         read(RESUME_ROOT / 'inputs/ORIGINAL_WAIT_OBSERVATIONS.json') == context['observation_raw'] and
         json.loads(read(run / 'GIT_BEFORE.json')) == context['current_git'] and
         json.loads(read(run / 'OLD_WAIT_BEFORE.json')) == context['wait_summary'],
         'new frozen resume inputs changed while acquiring the lane')
    for relative, raw in context['waiting'].items():
        need(read(RESUME_ROOT / 'inputs/original-wait' / relative) == raw, 'frozen copy of original wait differs')
    state_raw = read(old.STATE)
    need(sha(state_raw) == current['runtime'][old.STATE]['sha256'], 'original runtime state changed')
    journal = Path(json.loads(state_raw)['log'])
    journal_before = journal.stat()
    d.save(run / 'LIVE_BEFORE.json', current)
    records = context['validated']['records']
    d.save(run / 'OWNED_EXPORTS.json', records)
    d.save(run / 'PUBLIC_EXPORTS.json', [row for row in records if not row['is_private']])
    after, after_git, summary = check_preserved(context)
    d.save(run / 'LIVE_AFTER.json', after)
    d.save(run / 'OLD_WAIT_AFTER.json', summary)
    journal_after = journal.stat()
    need((journal_before.st_dev, journal_before.st_ino, journal_before.st_size) ==
         (journal_after.st_dev, journal_after.st_ino, journal_after.st_size),
         'strict receipt-only resume must produce zero new guard events')
    d.save(run / 'POSTPROCESS_RUNTIME_EVIDENCE.json', {
        'state': old.STATE, 'state_sha256': sha(state_raw), 'journal': str(journal),
        'postprocess_before_byte_offset': journal_before.st_size,
        'postprocess_after_byte_offset': journal_after.st_size, 'new_guard_events': 0,
        'reused_original_tail_path': str(context['predecessor'].ORIGINAL_ROOT / 'run/ACTUAL_GUARD_JOURNAL_TAIL.jsonl'),
        'reused_original_tail_sha256': sha(context['original_receipts']['signed/run/ACTUAL_GUARD_JOURNAL_TAIL.jsonl']),
        'reused_original_events': context['validated']['actual_guard_events'],
        'original_journal_byte_offsets_unavailable_not_reconstructed': True,
        'old_waiting_lane_receipt_preserved_sha256': sha(context['waiting']['run/VALIDATION_LANE.json']),
        'outer_lock_used': False,
    })
    result = {
        'schema': 'p14_signed_strict_receipt_resume_result_v1',
        'status': 'PASS_RESUMED_POSTPROCESS_EXISTING_AUDIT_LEGACY_NORMAL_KERNEL_COMPLETE_OWNED',
        'source_commit': source, 'module': MODULE,
        'source_sha256': context['legacy']['snapshot'][SOURCE]['sha256'],
        'predecessor_postprocess_source_commit': PREDECESSOR_SOURCE,
        'original_postprocess_wait': summary,
        'original_supplement_source_commit': context['predecessor'].ORIGINAL_SOURCE,
        'original_failed_supplement_task_id': context['recovery_plan']['original_task_id'],
        'original_supplement_task_exit_code': 1, 'original_supplement_validation_lane_exit_code': 1,
        'original_pipeline_signed_status': 'HELD_OR_FAILED_NO_SUPPLEMENT_RESULT',
        'original_supplement_result_absence_and_failure_preserved': True,
        'original_postprocess_wait_timeout_and_all_absences_preserved': True,
        'legacy_evidence_commit': old.LEGACY_COMMIT, 'legacy_primary_commands': context['legacy']['commands'],
        'legacy_primary_evidence': context['manifest']['frozen_primary_evidence'],
        'original_receipts': context['recovery_plan']['original_receipts'],
        'audit_command_reused': context['validated']['audit_command'],
        'new_normal_invocations': 0, 'new_kernel_invocations': 0, 'new_full_owned_audit_invocations': 0,
        'existing_full_owned_audit_invocations_reused': 1,
        'exact_original_guard_events': 2, 'original_runtime_metadata_queries': 1,
        'owned_total': len(records), 'public_total': sum(not row['is_private'] for row in records),
        'private_total': sum(row['is_private'] for row in records),
        'full_owned_including_private_generated': True, 'full_types_AST_universes_std3_axioms': True,
        'original_seven_public_AST_universes_axioms_unchanged': True,
        'source_plus_five_exact_original_and_unchanged': True,
        'original_pure_receipt_legacy_owned_live_functions_unchanged': True,
        'original_ROOT_PLAN_DRIVER_globals_not_monkeypatched': True,
        'old_wait_original_files_unchanged': True, 'original_git_before_after_equal': True,
        'new_guard_events': 0, 'outer_lock_used': False,
        'accepted_owners_by_this_independent_postprocess': [MODULE], 'whole_P1_4_complete': False,
    }
    d.save(run / RESULT_NAME, result)
    print(json.dumps(result), flush=True)
    result_raw = read(run / RESULT_NAME)
    print(json.dumps({'original_new_resume_result': {'path': str(run / RESULT_NAME),
        'bytes': len(result_raw), 'sha256': sha(result_raw)}, 'whole_P1_4_complete': False}), flush=True)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
