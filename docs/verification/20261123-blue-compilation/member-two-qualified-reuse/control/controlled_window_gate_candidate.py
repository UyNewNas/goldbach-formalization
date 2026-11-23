"""DRAFT library gate for a separately reviewed owner-only controlled window.

No installer, subprocess, source/object writes, signals or default execution.
Not a drop-in wrapper around df27: integration must replace (not duplicate)
its aggregate/Member lock scopes and preserve its qualification/no-clobber core.
"""
from contextlib import contextmanager
from pathlib import Path
import datetime
import errno
import fcntl
import hashlib
import json
import os

ROOT = Path('/workspace/p1-complete-proof')
BASE = ROOT / 'prototype-two-proposed-post-object-qualification'
MEMBER = Path('/workspace/blue-member-build')
PRODUCER = Path('/workspace/blue-reindex-build')
MODULES = ('ImbalancedChen.P5RealTruncatedMobiusSupport', 'ImbalancedChen.P5RealCutoffHeathBrownThree')
QUALIFIED_SHA = '373e844976c6509847657f78552b97aea06c74dee6b9869f22eb797d602a61e7'
PRODUCTION_SHA = 'df27c6de42360859fedee0b8eca2df9f12085fc97bdd170ec87d2374863cd1f9'
COMPLETION = ROOT / 'modern-p1-build/attempt-1-build-COMMAND.json'
COMPLETION_SHA = '0163342c488f450b76fba7f7542284b6d124c7db7cb854fcea2e61bb4e331ac9'
CHECKPOINT = ROOT / 'modern-p1-build/checkpoint-after-block070'
HISTORICAL = {
    'OWNER_STOP_RECEIPT.json': '98ccaf49cd895ad1a50dc4518c93b3bd6eb1947f1e17c7b4ea749584b0adb31e',
    'VERIFIED_GATE_OWNER.json': 'efdec78423785f24b9c323785a07ba9f2134077786dc3dc816ccdfee9fac7e16',
    'OLD_TREE_AT_ZERO_ACTIVE_SOURCE.json': 'b7101b0f1f4204983053892a298fabe616d02925c1bd17c7a164d54a5fe30d75',
    'SUCCESSFUL_GROUPS_BEFORE_OWNER_STOP.json': '86d7cbafcf057fc1a14a820478c64194587d2ba496c8586128c5af54a662efc4',
    'SUCCESSFUL_GROUPS_AFTER_OWNER_STOP.json': '86d7cbafcf057fc1a14a820478c64194587d2ba496c8586128c5af54a662efc4',
}
STATES = (
    (Path('/workspace/blue-build-tools/member-runtime-evidence/state.json'), '9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'),
    (Path('/workspace/blue-build-tools/runtime-evidence/state.json'), 'e474b9cb4b9e4d9cc4cc0c3ba58b29b0096f1bdec6f104d2e41a17f521ca232b'),
)
FIVE_TARGETS = [
    'ImbalancedChen.P4AOriginalFiniteAll22Nineteen:olean',
    'ImbalancedChen.P4AOriginalEarlyFinitePayment:olean',
    'ImbalancedChen.P1OriginalFinalPolicyRawBound:olean',
    'ImbalancedChen.P1OriginalFinalPolicyStructure:olean',
    'ImbalancedChen.P1OriginalFinalPolicyAncestorReads:olean',
]
REQUIRED_QUEUE_RECEIPTS = {
    '/workspace/blue-member-repair-batch70/VALIDATION_LANE.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch71/VALIDATION_LANE.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch72/VALIDATION_LANE.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch73/VALIDATION_LANE_PRIORITY_REQUEUE.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch74/VALIDATION_LANE_PRIORITY_REQUEUE.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch66/VALIDATION_LANE_REVISION3.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch66/VALIDATION_LANE_REVISION4_P6.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch66/VALIDATION_LANE_REVISION5_P6.json': 'LANE_FINISHED',
    '/workspace/blue-member-repair-batch56/VALIDATION_LANE_AFFINE_REUSE_REVISION4.json': 'LANE_FINISHED',
    '/workspace/p1-complete-proof/validation-lane-correction/LEGACY_P6_LANE.json': 'FINISHED_UTC',
}


def sha(path):
    with Path(path).open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


def read_pinned(path, expected):
    raw = Path(path).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == expected, ('pinned_metadata_changed', str(path))
    return json.loads(raw)


def current_related_jobs(proc_root=Path('/proc')):
    """Read only process identities; unknown identities fail closed.

    proc_root is injectable only for isolated fake-/proc regression fixtures.
    A failed read is a disappearance race only for ENOENT/ESRCH and a
    confirming absent PID directory. Access/decoding failures remain blockers.
    """
    result = []
    roots = (str(MEMBER), str(PRODUCER), '/workspace/goldbach-formalization/.lake/packages')
    tools = {'lean', 'lean-runtime', 'leanchecker', 'lake', 'clang', 'leanc', 'llvm-ar'}

    def disappeared(entry, error):
        if not isinstance(error, OSError) or error.errno not in (errno.ENOENT, errno.ESRCH):
            return False
        try:
            entry.stat()
        except OSError as probe_error:
            return probe_error.errno in (errno.ENOENT, errno.ESRCH)
        return False

    for entry in Path(proc_root).iterdir():
        if not entry.name.isdigit() or int(entry.name) == os.getpid():
            continue
        try:
            stat = (entry / 'stat').read_text().rsplit(')', 1)[1].split()
            if len(stat) < 20:
                raise ValueError('malformed_proc_stat')
            if stat[0] == 'Z':
                continue
            comm = (entry / 'comm').read_text().strip()
        except (OSError, UnicodeError, ValueError, IndexError) as error:
            if disappeared(entry, error):
                continue
            result.append({'pid': int(entry.name), 'unknown_process_identity': type(error).__name__})
            continue
        try:
            argv = [a for a in (entry / 'cmdline').read_text().split('\0') if a]
        except (OSError, UnicodeError) as error:
            if disappeared(entry, error):
                continue
            # Without argv even Python's comm cannot distinguish a pending
            # controller/guard from an unrelated interpreter. Never omit it.
            result.append({'pid': int(entry.name), 'state': stat[0], 'comm': comm,
                           'unknown_argv': type(error).__name__})
            continue
        if not argv:
            result.append({'pid': int(entry.name), 'state': stat[0], 'comm': comm,
                           'unknown_argv': 'EMPTY'})
            continue
        executable = Path(argv[0]).name
        python = executable.startswith('python')
        compiler = executable in tools or (python and len(argv) > 1 and '/p0-ci-shadow-toolchain/bin/' in argv[1])
        controller = python and any(
            a == '/workspace/blue-build-tools/run_guarded.py' or
            a.endswith('/serialize_validation_lane.py') or a.endswith('/resume_legacy_p6_lane.py') or
            a.endswith('/prepare_and_run_attempt1.py') or
            (a.endswith('/run_validation.py') and '/blue-member-repair-batch' in a) or
            ('install_two_qualified' in Path(a).name)
            for a in argv[1:])
        try:
            cwd, cwd_error = str((entry / 'cwd').resolve(strict=True)), None
        except (OSError, UnicodeError) as error:
            if disappeared(entry, error):
                continue
            cwd, cwd_error = None, type(error).__name__
        related = any((cwd is not None and cwd.startswith(r)) or any(a.startswith(r) for a in argv) for r in roots)
        # A compiler without a readable cwd cannot be proved unrelated just
        # because it is between source arguments (e.g. Lake/githash/checker).
        if controller or (compiler and (related or cwd is None)):
            result.append({'pid': int(entry.name), 'ppid': int(stat[1]), 'state': stat[0],
                'starttime': stat[19], 'argv': argv, 'cwd': cwd, 'cwd_read_error': cwd_error})
    return result

def assert_no_related_jobs():
    jobs = current_related_jobs()
    assert not jobs, ('related_active_or_queued_controller_Lake_source_kernel_or_unknown_job', jobs)


@contextmanager
def lock_existing(paths):
    held = []
    try:
        for path in sorted(set(map(Path, paths)), key=str):
            # No runtime/lock-file creation or rewrite. Busy means fail now;
            # this candidate never waits behind or signals current valid work.
            f = path.open('rb')
            held.append(f)
            fcntl.flock(f, fcntl.LOCK_EX | fcntl.LOCK_NB)
        yield
    finally:
        for f in reversed(held):
            f.close()


def validate_historical_controlled_stop():
    completed = read_pinned(COMPLETION, COMPLETION_SHA)
    expected = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', str(STATES[0][0]), 'lake', 'build'] + FIVE_TARGETS
    assert completed['argv'] == expected and completed['cwd'] == str(MEMBER)
    assert completed['exit_code'] == 241 and completed['finished_utc']
    records = {name: read_pinned(CHECKPOINT / name, digest) for name, digest in HISTORICAL.items()}
    stop = records['OWNER_STOP_RECEIPT.json']
    assert stop['completion_kind'] == 'OWNER_AUTHORIZED_RESOURCE_CHECKPOINT_CONTROLLED_STOP'
    assert stop['not_natural_aggregate_completion'] is True and stop['actual_old_command_exit'] == 241
    assert stop['actual_old_command_sha256'] == COMPLETION_SHA
    assert stop['Member_active_sources_after'] == []
    assert stop['successful_groups_preserved'] == 22 and stop['source_plus_five_outputs_unchanged'] is True
    assert records['SUCCESSFUL_GROUPS_BEFORE_OWNER_STOP.json'] == records['SUCCESSFUL_GROUPS_AFTER_OWNER_STOP.json']
    assert records['VERIFIED_GATE_OWNER.json']['Member_source_runtimes'] == []
    assert records['OLD_TREE_AT_ZERO_ACTIVE_SOURCE.json']['Member_source_runtime_processes'] == []
    # This intentionally does not change or deny the original df27 policy.
    assert stop['portable_installer_natural_completion_gate_not_waived'] is True
    return completed



PRIORITY_REQUEUE_RECEIPT = Path('/workspace/p1-complete-proof/validation-lane-correction/PRIORITIZE_PENDING_SIXTH_REMAINING_OVER_UNEXECUTED_FAMILY.json')
PRIORITY_REQUEUE_SHA = '85e528cca2908b0805fb151017bcd9d1dcff8be9d04f6d5be39044192c28b9da'
CANCELLED_WAITING_PINNED = {
    73: {'old': 'a755f4f21d4193eb440cf928cfbe681deb88f8401959380e994ceefe1045e095',
         'cancel': '1905ee960f68434d4eff080704cc34eed006691754119ca58eec95d9a3e9fc95',
         'tool': 'b9ac7270fc3b9e8a9add86c3ffb19de721c42f48338b18eff9122eaa77edfafa'},
    74: {'old': 'ee1351aed52c0c7c23f549fce9969e9336dec67c026eadc5862a33595d531b23',
         'cancel': '6384a95b451ca5258a683f2afeeb1210795879650a421acd805996cb17c3754e',
         'tool': '81801de2aa5c25cb0c8a29eaea4a3ed8a4fb12d59b1abe9d92d4b49e3744981b'},
}


def validate_exact_waiting_requeue_cancellations():
    """Only two pinned no-child queue cancellations; never generic CANCELLED acceptance."""
    root = read_pinned(PRIORITY_REQUEUE_RECEIPT, PRIORITY_REQUEUE_SHA)
    for batch, pins in CANCELLED_WAITING_PINNED.items():
        packet = Path(f'/workspace/blue-member-repair-batch{batch}')
        old = read_pinned(packet / 'VALIDATION_LANE.json', pins['old'])
        cancel = read_pinned(packet / 'UNEXECUTED_FAMILY_PRIORITY_REQUEUE.json', pins['cancel'])
        tool = read_pinned(packet / 'CANCELLED_QUEUE_TOOL_COMPLETION.json', pins['tool'])
        assert old['status'] == 'WAITING_VALIDATION_LANE' and 'child_pid' not in old
        assert cancel['batch'] == batch and cancel['pid'] == old['pid']
        assert cancel['status'] == 'UNEXECUTED_WAITING_SCHEDULER_CANCELLED_FOR_PRIORITY_REQUEUE'
        assert cancel['no_child_at_stop_and_cancel_via_complete_proc_ppid_scan'] is True
        assert cancel['no_normal_source_stage_started'] is True and cancel['compiler_checker_signals'] == []
        assert cancel in root['events']
        assert tool['classification'] == 'OWNER_CANCELLED_UNEXECUTED_WAITING_SERIALIZER_THEN_REQUEUED'
        assert tool['actual_outer_tool_exit_code'] == 143
        assert tool['not_a_source_compiler_or_proof_failure'] is True
        assert tool['no_compiler_checker_child_existed_at_cancel'] is True
        assert tool['fresh_requeue_receipt'] == 'VALIDATION_LANE_PRIORITY_REQUEUE.json'
        # The replacement must really finish on the same lane with the same
        # original validation command. Its hash/status is also bound in the
        # fresh owner release; an old WAITING or143 cannot satisfy this check.
        replacement = json.loads((packet / 'VALIDATION_LANE_PRIORITY_REQUEUE.json').read_text())
        assert replacement['status'] == 'VALIDATION_LANE_FINISHED'
        assert replacement['finished_utc'] and isinstance(replacement['exit_code'], int)
        assert replacement['argv'] == old['argv']
        assert replacement['original_compiler_slot'] == old['original_compiler_slot']
        assert replacement['state'] == old['state'] and replacement['state_sha256'] == old['state_sha256']
        assert replacement['validation_lane_lock'] == old['validation_lane_lock']


SIXTH_MOVE_RECEIPT = Path('/workspace/blue-member-repair-batch66/REVISION4_UNEXECUTED_MEMBER_TO_P6_MOVE.json')
SIXTH_MOVE_SHA = '993d37b38c8bad1edfd6d3a6972b1b834fe7fbefb69bbaa0e4e4fe674cfd02b1'
SIXTH_CANCELLED_MEMBER_RECEIPT = Path('/workspace/blue-member-repair-batch66/VALIDATION_LANE_REVISION4.json')
SIXTH_CANCELLED_MEMBER_SHA = '73dbe70118ef31268304b86599dc2c32b50a915bb9903e465d6da7011907563c'


def validate_sixth_exact_unexecuted_lane_move():
    """One pinned no-child Member cancellation; replacement must really finish on P6."""
    moved = read_pinned(SIXTH_MOVE_RECEIPT, SIXTH_MOVE_SHA)
    old = read_pinned(SIXTH_CANCELLED_MEMBER_RECEIPT, SIXTH_CANCELLED_MEMBER_SHA)
    assert moved['status'] == 'UNEXECUTED_REVISION4_MEMBER_QUEUE_CANCELLED_TO_MOVE_TO_FREE_ORIGINAL_P6_LANE'
    assert moved['old_receipt'] == str(SIXTH_CANCELLED_MEMBER_RECEIPT)
    assert moved['old_pid'] == old['pid']
    assert moved['no_child_or_normal_stage_at_cancel'] is True
    assert moved['source_compiler_checker_signals'] == []
    assert moved['only_scheduler_parent_signals'] == ['SIGSTOP', 'SIGTERM', 'SIGCONT']
    assert moved['P6_fullchain_lock_obtained_nonblocking_after_H3_natural_failure'] is True
    assert moved['source_guard_M12288_t0_j2_100k4m_unchanged'] is True
    assert moved['next_receipt'] == 'VALIDATION_LANE_REVISION4_P6.json'
    assert old['status'] == 'WAITING_VALIDATION_LANE' and 'child_pid' not in old
    assert old['state'] == str(STATES[0][0]) and old['state_sha256'] == STATES[0][1]
    replacement_path = SIXTH_CANCELLED_MEMBER_RECEIPT.with_name(moved['next_receipt'])
    replacement = json.loads(replacement_path.read_text())
    assert replacement['status'] == 'VALIDATION_LANE_FINISHED'
    assert replacement['finished_utc'] and isinstance(replacement['exit_code'], int)
    assert replacement['argv'] == old['argv']
    state = read_pinned(*STATES[1])
    assert replacement['state'] == str(STATES[1][0]) and replacement['state_sha256'] == STATES[1][1]
    assert replacement['original_compiler_slot'] == state['slot']
    assert replacement['validation_lane_lock'] == state['slot'] + '.validation-lane.lock'


class ControlledOwnerWindow:
    """Outer validation-lane leases must remain held through post-copy stock."""
    def __init__(self, slots, immutable_inputs):
        self.slots = slots
        self.immutable_inputs = immutable_inputs
        self.mutation_open = False

    def assert_receipts_immutable(self):
        for path, digest in self.immutable_inputs.items():
            assert sha(path) == digest, ('window_or_review_receipt_changed', str(path))

    @contextmanager
    def compiler_mutation_window(self):
        assert not self.mutation_open
        with lock_existing(self.slots):
            self.assert_receipts_immutable()
            assert_no_related_jobs()
            self.mutation_open = True
            try:
                yield self
            finally:
                self.mutation_open = False

    def assert_stock_phase_ready(self):
        assert not self.mutation_open, 'Compiler locks must be released before Lake stock/githash'
        self.assert_receipts_immutable()
        assert_no_related_jobs()

    def assert_before_each_write(self):
        assert self.mutation_open, 'Must hold both original compiler slots during each source/facet write'
        self.assert_receipts_immutable()
        assert_no_related_jobs()


@contextmanager
def controlled_owner_window(root_review_path, owner_release_path, *, caller_path):
    """Future reviewed installer integration only. No copying or stock here."""
    review_raw = Path(root_review_path).read_bytes()
    owner_raw = Path(owner_release_path).read_bytes()
    immutable_inputs = {str(root_review_path): hashlib.sha256(review_raw).hexdigest(),
                        str(owner_release_path): hashlib.sha256(owner_raw).hexdigest()}
    review = json.loads(review_raw)
    assert review['status'] == 'APPROVED_CONTROLLED_WINDOW_GATE_FOR_OWNER_INTEGRATION'
    assert review['candidate_gate_sha256'] == sha(__file__)
    assert review['candidate_caller_sha256'] == sha(caller_path)
    immutable_inputs[str(Path(__file__).resolve(strict=True))] = review['candidate_gate_sha256']
    immutable_inputs[str(Path(caller_path).resolve(strict=True))] = review['candidate_caller_sha256']
    assert review['qualified_manifest_sha256'] == QUALIFIED_SHA
    assert review['historical_completion_sha256'] == COMPLETION_SHA
    assert review['not_natural_completion_or_full_proof_credit'] is True
    owner = json.loads(owner_raw)
    assert owner['status'] == 'OWNER_RELEASED_CONTROLLED_CHECKPOINT_TARGET_WINDOW'
    assert set(owner['modules']) == set(MODULES)
    assert owner['qualified_manifest_sha256'] == QUALIFIED_SHA
    assert owner['historical_completion_sha256'] == COMPLETION_SHA
    assert owner['root_review_sha256'] == sha(root_review_path)
    attest = owner['owner_attestations']
    for key in ['all_related_controllers_and_queues_drained', 'no_new_validation_or_staging_until_stock_receipt',
                'no_other_installer_or_source_writer', 'both_original_lane_owners_released_window']:
        assert attest[key] is True
    created = datetime.datetime.fromisoformat(owner['created_utc'])
    assert created.tzinfo is not None
    age = (datetime.datetime.now(datetime.timezone.utc) - created).total_seconds()
    assert 0 <= age <= 60, ('stale_owner_release_receipt_seconds', age)
    provided = {record['path']: record for record in owner['finished_queue_receipts']}
    assert set(REQUIRED_QUEUE_RECEIPTS) <= set(provided)
    for path, record in provided.items():
        assert str(Path(path).resolve(strict=True)).startswith('/workspace/')
        data = read_pinned(path, record['sha256'])
        immutable_inputs[path] = record['sha256']
        predicate = REQUIRED_QUEUE_RECEIPTS.get(path) or record['completion_predicate']
        assert data.get('finished_utc')
        if predicate == 'LANE_FINISHED':
            assert data['status'] == 'VALIDATION_LANE_FINISHED' and isinstance(data['exit_code'], int)
        else:
            assert predicate == 'FINISHED_UTC'
    validate_historical_controlled_stop()
    validate_exact_waiting_requeue_cancellations()
    validate_sixth_exact_unexecuted_lane_move()
    manifest = read_pinned(BASE / 'MANIFEST.json', QUALIFIED_SHA)
    for name, digest in manifest['additional_files'].items():
        assert Path(name).name == name
        assert sha(BASE / name) == digest
    assert sha(ROOT / 'install_two_qualified_project_groups.py') == PRODUCTION_SHA
    slots = []
    for state_path, digest in STATES:
        state = read_pinned(state_path, digest)
        slots.append(Path(state['slot']))
    for module in MODULES:
        group = manifest['groups'][module]
        assert sha(group['actual_current_source_identity_key']) == group['actual_current_source_pre_sha256']
        assert sha(group['proposed_source_identity_key']) == group['proposed_source_post_sha256']
    aggregate = ROOT / 'modern-p1-build/controller.lock'
    lanes = [Path(str(slot) + '.validation-lane.lock') for slot in slots]
    # Integrator must replace df27's separate aggregate lock with this scope,
    # not reacquire the same flock through another file description.
    with lock_existing(lanes + [aggregate]):
        assert_no_related_jobs()
        window = ControlledOwnerWindow(slots, immutable_inputs)
        window.assert_receipts_immutable()
        yield window
        assert not window.mutation_open
        window.assert_receipts_immutable()
        # Installer must release compiler_mutation_window BEFORE any Lake
        # --githash/--no-build stock call, while these lane leases remain held.


if __name__ == '__main__':
    raise SystemExit('SOURCE-ONLY GATE CANDIDATE: no default execution, installer, copy, stock or Lean action')
