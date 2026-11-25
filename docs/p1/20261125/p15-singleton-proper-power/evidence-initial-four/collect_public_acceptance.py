#!/usr/bin/env python3
"""Read retained P1 receipts and emit only public identities, counts and hashes."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
os.environ['GIT_OPTIONAL_LOCKS'] = '0'
COMMIT = 'd20acdf13882e17d97833064f5e7c54f3192b03c'
REPO = Path('/workspace/goldbach-formalization')
DRIVER = 'docs/p1/20261125/p15-singleton-proper-power/run_selected.py'
DRIVER_SHA = 'f260f575ed6f8a7998fd901d42f0f1cd87115c879c0dc3b2c10f04a7f9b35313'
TARGETS = ['ImbalancedChen.P1OriginalSingletonPointwiseData',
           'ImbalancedChen.P1Full87TrueDPolicyDelta',
           'ImbalancedChen.P1Full87TrueDUnitBound',
           'ImbalancedChen.P1OriginalHistoricalMiddlePointwiseData']
ALLOWED_AXIOMS = {'Classical.choice', 'Quot.sound', 'propext'}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def raw(path):
    need(path.is_file() and path.resolve() == path, 'not a regular retained file')
    return path.read_bytes()


def main():
    code = subprocess.check_output(['git', 'show', COMMIT + ':' + DRIVER], cwd=REPO)
    need(sha(code) == DRIVER_SHA, 'unchanged driver pin differs')
    runner = ModuleType('fixed_p15_driver')
    runner.__file__ = DRIVER
    exec(compile(code, DRIVER, 'exec'), runner.__dict__)
    s = runner.helpers()
    git_before = s.d.original_git_state(REPO)
    spec = runner.preflight(s, COMMIT, TARGETS)
    base = runner.ROOT / COMMIT
    run = base / 'runs/attempt-00000'
    original_result_raw = raw(run / 'RESULT.json')
    original_result = json.loads(original_result_raw)
    need(original_result['source_commit'] == COMMIT and
         original_result['targets'] == TARGETS and
         original_result['accepted_owners'] == TARGETS and
         original_result['all_selected_owners_accepted'] is True and
         original_result['failures'] == {} and original_result['worker_exit_code'] == 0 and
         original_result['whole_P1_complete'] is False, 'four-owner job result differs')
    need(raw(run / 'CONTEXT_BEFORE.json') == raw(run / 'CONTEXT_AFTER.json'),
         'retained compile context changed')
    need(raw(run / 'GIT_BEFORE.json') == raw(run / 'GIT_AFTER.json'),
         'retained Git metadata changed')
    observed_axioms, owners = set(), {}
    all_bindings = {}
    for owner in TARGETS:
        folder = base / owner
        normal_path = folder / 'normal' / owner / 'NORMAL_PASS.json'
        paths = list((folder / 'audits').glob('*/lane-0/VALIDATION_RESULTS.json'))
        need(len(paths) == 1, 'ambiguous or missing retained audit: ' + owner)
        result_path = paths[0]
        audit = result_path.parent.parent
        need(re.fullmatch('[0-9a-f]{20}', audit.name), 'unexpected audit path')
        lane = audit / 'lane-0'
        plan_path = audit / 'AUDIT_PLAN.json'
        normal, plan = json.loads(raw(normal_path)), json.loads(raw(plan_path))
        accepted = s.api.audit_valid(COMMIT, runner.PROJECT, audit, plan, {owner: normal},
                                     spec.graph, spec.sources, s.h, s.d)
        need(accepted == {owner}, 'retained audit scope differs')
        result = json.loads(raw(result_path))
        exports_raw = raw(lane / 'OWNED_EXPORTS.json')
        exports = json.loads(exports_raw)
        axioms = {a for entry in exports for a in entry['axioms']}
        need(axioms <= ALLOWED_AXIOMS and all(entry['kind'] != 'axiom' for entry in exports),
             'unexpected owned axiom')
        observed_axioms |= axioms
        refs = {'normal': normal_path, 'audit_plan': plan_path, 'audit_result': result_path,
                'owned_exports': lane / 'OWNED_EXPORTS.json',
                'owned_log': lane / 'all-owned-types-axioms.log'}
        bindings = {k: {'bytes': len(raw(p)), 'sha256': sha(raw(p))} for k, p in refs.items()}
        all_bindings.update({str(p): bindings[k] for k, p in refs.items()})
        owners[owner] = {
            'source_sha256': spec.sources[owner], 'source_commit': COMMIT,
            'status': result['status'], 'receipt_bindings': bindings,
            'owned_count': result['total_owned_exports'],
            'public_count': result['total_public_exports'],
            'kernel_exit_code': result['kernel_commands'][owner]['exit_code'],
            'kernel_log_sha256': result['kernel_commands'][owner]['log_sha256'],
            'observed_axioms': sorted(axioms)}
    need(runner.current_snapshot(s, spec) == spec.baseline, 'current source/runtime/cache context changed')
    need(s.d.original_git_state(REPO) == git_before, 'current Git metadata changed')
    for path, expected in all_bindings.items():
        data = raw(Path(path))
        need(expected == {'bytes': len(data), 'sha256': sha(data)}, 'retained receipt changed')
    need(raw(run / 'RESULT.json') == original_result_raw, 'original result changed')
    summary = {
        'schema': 'p15_initial_four_retained_acceptance_public_summary_v1',
        'repository': 'UyNewNas/goldbach-formalization', 'source_commit': COMMIT,
        'compiler_job': 'job_1ed0e0c8d4ee466f8444aff044abe510',
        'unchanged_driver_sha256': DRIVER_SHA,
        'collector_sha256': sha(Path(__file__).read_bytes()),
        'original_result_sha256': sha(original_result_raw),
        'owners': owners, 'accepted_owner_count': len(owners),
        'owned_count': sum(r['owned_count'] for r in owners.values()),
        'public_count': sum(r['public_count'] for r in owners.values()),
        'observed_axioms': sorted(observed_axioms),
        'full_committed_source_count': len(spec.graph),
        'active_selected_source_count': len(s.h.closure(spec.graph, TARGETS)),
        'normal_kernel_full_owned_receipts_revalidated_without_execution': True,
        'source_runtime_and_fixed_cache_unchanged': True, 'git_metadata_unchanged': True,
        'dependency_rebuilds_requested': False, 'raw_logs_or_private_types_exported': False,
        'whole_P1_complete': False, 'whole_P1_5_complete': False}
    encoded = (json.dumps(summary, sort_keys=True, separators=(',', ':')) + '\n').encode()
    output = runner.ROOT / 'reviews/initial-four-d20acdf-public.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    if output.exists():
        need(raw(output) == encoded, 'existing public summary differs')
    else:
        with output.open('xb') as stream:
            stream.write(encoded)
    print('PUBLIC_ACCEPTANCE_SUMMARY ' + encoded.decode().strip())


if __name__ == '__main__':
    main()
