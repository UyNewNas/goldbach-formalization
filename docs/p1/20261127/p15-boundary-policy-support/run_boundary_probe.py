#!/usr/bin/env python3
"""Probe the unchanged Boundary source after actual Coefficient acceptance.

Reuse the 56 existing dependency inputs. This is one guarded, serialized Lean
elaboration with no output object; it creates no new owner acceptance. The
subsequent formal adapter must bind these actual probe files and retain the
normal/kernel/full-owned audit for Boundary itself.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
PACKET = 'docs/p1/20261127/p15-boundary-policy-support'
TARGET = 'ImbalancedChen.P1HistoricalBoundaryPolicyDifferenceSupport'
NAME = 'P1HistoricalBoundaryPolicyDifferenceSupport.lean'
SOURCE_PIN = {'bytes': 20316, 'sha256': '7ac7742c3a9ada5d3a8f1e5c6e37526b5acc7d6d89d791cd61387f06fcb9b9c2'}
CONTEXT_PIN = {'bytes': 12433, 'sha256': '02ca05be83bec874115f4280f9d86f3db33f2a00545ad63dc4c435d94b6a1ef5'}
RUN = (Path('/workspace/p1-complete-proof/20261127-p15-boundary-policy-probe-v1') /
       SOURCE_PIN['sha256'] / 'attempt-00000')


def need(ok, message):
    if not ok:
        raise ValueError(message)


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def regular(path):
    need(path.is_file() and not path.is_symlink() and path.resolve() == path,
         'expected original regular file: ' + str(path))
    return path.read_bytes()


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def load(commit):
    need(isinstance(commit, str) and re.fullmatch('[0-9a-f]{40}', commit), 'exact source publication required')
    runner = git(commit, PACKET + '/run_boundary_probe.py')
    need(runner == regular(Path(__file__)), 'probe entrypoint differs from exact publication')
    helper_raw = git(commit, PACKET + '/boundary_context.py')
    need(fingerprint(helper_raw) == CONTEXT_PIN, 'reviewed Boundary dependency loader differs')
    helper = ModuleType('bound_boundary_context')
    helper.__file__ = PACKET + '/boundary_context.py'
    exec(compile(helper_raw, helper.__file__, 'exec'), helper.__dict__)
    binding = json.loads(git(commit, PACKET + '/COEFFICIENT_BINDING.json'))
    c = helper.load(binding, commit)
    need((helper.REPO, helper.PROJECT, helper.TARGET, helper.NAME, helper.SOURCE_PIN) ==
         (REPO, PROJECT, TARGET, NAME, SOURCE_PIN), 'fixed Boundary environment/source differs')
    c.helper, c.runner, c.helper_raw = helper, runner, helper_raw
    c.ident = {'source_commit': commit, 'target': TARGET, 'source': SOURCE_PIN,
        'source_path': helper.LIVE, 'original_source_unchanged': True,
        'adapter': fingerprint(runner), 'context_helper': CONTEXT_PIN,
        'coefficient_original_acceptance_binding': binding,
        'old_dictionary_module_count': 53, 'additional_old_module_count': 13,
        'project_dependency_count': 56, 'direct_imports': helper.IMPORTS,
        'new_owner_accepted': False, 'new_formal_credit': 0, 'whole_P1_5_complete': False}
    return c


def worker(c):
    c.s.d.verify_lane(c.s.h)
    need(Path(__file__) == RUN / 'probe_driver.py' and RUN.resolve() == RUN, 'unexpected Boundary probe worker route')
    need(c.s.api.read_json(RUN / 'GIT_BEFORE.json') == c.s.d.original_git_state(REPO), 'Git changed before probe')
    need(regular(RUN / NAME) == c.source, 'frozen original Boundary source differs')
    before = c.helper.retained(c)
    target_before = c.helper.fresh(c)
    c.s.d.save(RUN / 'PRESERVED_BEFORE.json', before)
    c.s.d.save(RUN / 'TARGET_BEFORE.json', target_before)
    result = {'schema': 'p15_boundary_policy_no_output_probe_v1', 'identity': c.ident,
        'direct_import_readiness': None, 'command': None, 'exit_code': 3,
        'probe_passed': False, 'preservation_passed': False, 'output_object_requested': False,
        'new_owner_accepted': False, 'new_formal_credit': 0, 'whole_P1_5_complete': False}
    try:
        result['direct_import_readiness'] = c.g.direct_import_readiness(c.s, c.spec, TARGET, RUN)
        need(c.helper.retained(c) == before and c.helper.fresh(c) == target_before,
             'no-build readiness changed existing inputs or target')
        command = c.s.ops.run(RUN, 'probe',
            c.s.h.guard(0, ['lake', '--no-build', 'env', 'lean', str(RUN / NAME)]), cwd=PROJECT, relay=True)
        result['command'] = command
        need(not command['actual_built_modules'] and not command['actual_failed_modules'],
             'no-output probe attempted a build')
        result['exit_code'] = command['exit_code']
    except Exception as error:
        result['probe_error'] = str(error)
    finally:
        try:
            after, target_after = c.helper.retained(c), c.helper.fresh(c)
            c.s.d.save(RUN / 'PRESERVED_AFTER.json', after)
            c.s.d.save(RUN / 'TARGET_AFTER.json', target_after)
            need(before == after and target_before == target_after, 'probe changed retained dependencies or target')
            need(all(not list(RUN.glob(pattern)) for pattern in
                     ('*.olean*', '*.ilean*', '*.c', '*.o', '*.bc', '*.ir', '*.trace*')),
                 'no-output probe produced an object')
            result['preservation_passed'] = True
        except Exception as error:
            result['preservation_error'] = str(error)
    result['probe_passed'] = (result['exit_code'] == 0 and result['preservation_passed'] and
                              not result.get('probe_error') and not result.get('preservation_error'))
    if not result['probe_passed'] and result['exit_code'] == 0:
        result['exit_code'] = 3
    c.s.d.save(RUN / 'PROBE_RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return result['exit_code']


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--worker', action='store_true')
    args = parser.parse_args()
    c = load(args.source_commit)
    if args.worker:
        return worker(c)
    c.helper.fresh(c)
    need(RUN.resolve() == RUN, 'unexpected Boundary probe route')
    RUN.mkdir(parents=True, exist_ok=False)
    c.s.d.write_frozen(RUN / 'probe_driver.py', c.runner)
    c.s.d.write_frozen(RUN / NAME, c.source)
    before = c.s.d.original_git_state(REPO)
    c.s.d.save(RUN / 'GIT_BEFORE.json', before)
    worker_argv = ['python3', '-B', str(RUN / 'probe_driver.py'), '--source-commit', c.commit, '--worker']
    outer_argv = c.s.h.serialize(0, RUN / 'LANE.json', worker_argv)
    try:
        outer = c.s.ops.run(RUN, 'serialized-probe', outer_argv, cwd=PROJECT, relay=True)
    finally:
        after = c.s.d.original_git_state(REPO)
        c.s.d.save(RUN / 'GIT_AFTER.json', after)
        need(before == after, 'original Git state changed')
    result = c.s.api.read_json(RUN / 'PROBE_RESULT.json')
    need(not outer['actual_built_modules'] and not outer['actual_failed_modules'] and
         result['identity'] == c.ident and result['exit_code'] == outer['exit_code'], 'outer probe scope/status differs')
    if outer['exit_code'] == 0:
        state = outer_argv[outer_argv.index('--state') + 1]
        c.pc.x.parent.verify_finished_lane(c.s.api.read_json(RUN / 'LANE.json'), worker_argv, state,
                                          fingerprint(regular(Path(state)))['sha256'])
        need(result['probe_passed'] is True and result['preservation_passed'] is True,
             'successful outer probe lacks completed preservation')
    print(json.dumps({'identity': c.ident, 'exit_code': outer['exit_code'],
        'probe_passed': result['probe_passed'], 'result': fingerprint(regular(RUN / 'PROBE_RESULT.json')),
        'new_formal_credit': 0, 'whole_P1_5_complete': False}, sort_keys=True), flush=True)
    return outer['exit_code']


if __name__ == '__main__':
    raise SystemExit(main())
