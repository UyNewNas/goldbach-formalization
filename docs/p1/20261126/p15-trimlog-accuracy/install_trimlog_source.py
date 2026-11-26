#!/usr/bin/env python3
"""Install only the exact AD TrimLogAccuracy canonical source before its owner starts."""
from pathlib import Path
from types import ModuleType
import argparse
import json
import os
import subprocess
import sys
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
PACKAGE = 'docs/p1/20261126/p15-trimlog-accuracy/'
SCRIPT = PACKAGE + 'install_trimlog_source.py'
ADAPTER = PACKAGE + 'run_trimlog.py'


def load(commit, executed):
    raw = subprocess.check_output(['git', 'show', commit + ':' + ADAPTER], cwd=REPO)
    adapter = ModuleType('published_independent_trimlog'); adapter.__file__ = ADAPTER
    exec(compile(raw, ADAPTER, 'exec'), adapter.__dict__)
    c = adapter.load(commit, raw)
    adapter.require(executed == adapter.git_file(commit, SCRIPT) and SCRIPT == adapter.INSTALLER,
                    'executed source installer differs from publication')
    c.installer = executed
    return adapter, c


def install_exclusive(adapter, source, payload):
    adapter.require(source.parent.is_dir() and source.parent.resolve() == source.parent and
                    source.resolve() == source, 'canonical source parent traverses a symlink')
    if os.path.lexists(source):
        adapter.require(adapter.fp(source) == adapter.SOURCE_FP and source.read_bytes() == payload,
                        'existing canonical source differs; no replacement is allowed')
        return 'IDENTICAL_SOURCE_BEFORE_OWNER_START'
    descriptor = os.open(source, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(payload); stream.flush(); os.fsync(stream.fileno())
    directory = os.open(source.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    adapter.require(adapter.fp(source) == adapter.SOURCE_FP and source.read_bytes() == payload,
                    'new source bytes differ; preserve the file for inspection')
    return 'EXCLUSIVE_NEW_CANONICAL_SOURCE'


def worker(a, c, run):
    c.ag.d.verify_lane(c.ag.h)
    state = a.prepare_base(c)
    source = a.PROJECT / a.SOURCE
    a.require_new_slot(a.fp(source), c.g.module_artifacts(c.ag, a.TARGET), a.owner_history(c.commit), installed=False)
    before = a.preservation_summary(state)
    c.ag.d.save(run / 'OLD_CONTEXT_BEFORE.json', before)
    result = {'schema': 'p15_independent_trimlog_source_install_v1', 'identity': c.identity,
        'installer': {'path': SCRIPT, **a.raw_fp(c.installer)}, 'source_installed': False,
        'normal_or_kernel_commands_executed': 0, 'new_owner_accepted': False, 'whole_P1_5_complete': False}
    try:
        result['source_before'] = a.fp(source)
        result['installation_action'] = install_exclusive(a, source, c.source)
        a.require_new_slot(a.fp(source), c.g.module_artifacts(c.ag, a.TARGET), a.owner_history(c.commit), installed=True)
        a.unchanged_old(c, state)
        result['source_after'] = a.fp(source)
        result['source_installed'] = True
    except Exception as error:
        result['installation_error'] = str(error)
    finally:
        try:
            a.unchanged_old(c, state)
            a.require(not a.owner_history(c.commit) and
                all(value is None for value in c.g.module_artifacts(c.ag, a.TARGET).values()),
                'new owner started or produced artifacts during source installation')
            after = a.preservation_summary(state)
            c.ag.d.save(run / 'OLD_CONTEXT_AFTER.json', after)
            a.require(before == after, 'old source/artifact/evidence/runtime context changed')
        except Exception as error:
            result['preservation_error'] = str(error)
    result['preservation'] = before
    c.ag.d.save(run / 'WORKER_RESULT.json', result)
    return int(not result['source_installed'] or bool(result.get('installation_error') or result.get('preservation_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--install', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    path = Path(__file__)
    if not path.is_file() or path.is_symlink():
        raise RuntimeError('installer must be a regular file')
    a, c = load(args.source_commit, path.read_bytes())
    if args.check:
        a.require(args.inside_lane is None, 'read-only check cannot enter a worker lane')
        state = a.prepare_base(c)
        source = a.fp(a.PROJECT / a.SOURCE)
        a.require_new_slot(source, c.g.module_artifacts(c.ag, a.TARGET), a.owner_history(c.commit), installed=False)
        a.unchanged_old(c, state)
        print(json.dumps({'status': 'EXACT_SOURCE_READY_FOR_INSTALL' if source is None else 'EXACT_SOURCE_INSTALLED_BEFORE_OWNER_START',
            'identity': c.identity, 'source': source, 'new_owner_accepted': False, 'whole_P1_5_complete': False}, sort_keys=True), flush=True)
        return 0
    runs = a.INSTALL_ROOT / c.commit / 'runs'
    if args.inside_lane:
        run = args.inside_lane
        a.require(run.is_absolute() and run.resolve() == run and run.parent == runs and
            a.re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(), 'unexpected installer worker path')
        return worker(a, c, run)
    a.require(runs.resolve() == runs, 'installer evidence parent traverses a symlink')
    run = c.ag.d.attempt(runs)
    git = c.ag.d.original_git_state(REPO); c.ag.d.save(run / 'GIT_BEFORE.json', git)
    executed = run / 'executed-installer.py'; c.ag.d.write_frozen(executed, c.installer)
    result = {'schema': 'p15_independent_trimlog_source_install_v1', 'identity': c.identity,
        'source_installed': False, 'source_install_complete': False, 'worker_exit_code': 3,
        'new_owner_accepted': False, 'whole_P1_5_complete': False}
    try:
        command = c.ag.ops.run(run, 'serialized-trimlog-install', c.ag.h.serialize(0, run / 'TRIMLOG_INSTALL_LANE.json',
            ['python3', '-B', str(executed), '--source-commit', c.commit, '--install', '--inside-lane', str(run)]), relay=True)
        result['worker_exit_code'] = command['exit_code']
        a.require(command['actual_built_modules'] == command['actual_failed_modules'] == [], 'installer ran a build')
        a.require(a.fp(run / 'WORKER_RESULT.json') is not None, 'installer worker stopped before its result')
        result.update(c.ag.api.read_json(run / 'WORKER_RESULT.json'))
    except Exception as error:
        result['dispatch_error'] = str(error)
    finally:
        try:
            after = c.ag.d.original_git_state(REPO); c.ag.d.save(run / 'GIT_AFTER.json', after)
            a.require(after == git, 'original dirty Git state changed')
        except Exception as error:
            result['git_error'] = str(error)
    success = result.get('worker_exit_code') == 0 and result.get('source_installed') is True and not any(
        result.get(key) for key in ('installation_error', 'preservation_error', 'dispatch_error', 'git_error'))
    result['source_install_complete'] = success
    c.ag.d.save(run / 'SOURCE_INSTALL_RESULT.json', result)
    print(json.dumps({'path': str(run / 'SOURCE_INSTALL_RESULT.json'), **result}, sort_keys=True), flush=True)
    return 0 if success else max(1, int(result.get('worker_exit_code', 3)))


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
        'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'TRIMLOG_SOURCE_INSTALL_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_accepted': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
