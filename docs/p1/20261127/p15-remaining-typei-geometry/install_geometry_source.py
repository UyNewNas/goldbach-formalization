#!/usr/bin/env python3
"""Install the exact reviewed Geometry source before its independent owner starts.

The only replacement permitted is the pinned AJ source by its exact notation
and escaped-parameter repair. Original bytes are retained in evidence first.
"""
from pathlib import Path
from types import ModuleType
import argparse
import json
import os
import subprocess
import sys
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
PACKAGE = 'docs/p1/20261127/p15-remaining-typei-geometry/'
SCRIPT = PACKAGE + 'install_geometry_source.py'
ADAPTER = PACKAGE + 'run_geometry.py'


def load(commit, executed):
    raw = subprocess.check_output(['git', 'show', commit + ':' + ADAPTER], cwd=REPO)
    adapter = ModuleType('published_independent_geometry'); adapter.__file__ = ADAPTER
    exec(compile(raw, ADAPTER, 'exec'), adapter.__dict__)
    c = adapter.load(commit, raw)
    adapter.require(executed == adapter.git_file(commit, SCRIPT) and SCRIPT == adapter.INSTALLER,
                    'executed Geometry source installer differs from publication')
    c.installer = executed
    return adapter, c


def write_exclusive(path, payload):
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(payload); stream.flush(); os.fsync(stream.fileno())


def install_exact(a, source, payload, backup):
    a.require(a.raw_fp(payload) == a.SOURCE_FP, 'only the exact repaired source payload is authorized')
    a.require(source.parent.is_dir() and source.parent.resolve() == source.parent and
              source.resolve() == source, 'canonical source parent traverses a symlink')
    before = a.fp(source)
    action = a.installation_action(before)
    if before == a.SOURCE_FP:
        a.require(source.read_bytes() == payload, 'existing repaired source bytes differ')
        return action
    if before is None:
        write_exclusive(source, payload)
    else:
        a.require(backup is not None and backup.is_absolute() and backup.resolve() == backup and
                  a.fp(backup) == a.ORIGINAL_SOURCE_FP, 'exact original source backup required before replacement')
        original = source.read_bytes()
        a.require(backup.read_bytes() == original, 'source backup does not match the original canonical bytes')
        a.require_corrected_source(original, payload)
        stat = source.stat(follow_symlinks=False)
        temporary = source.with_name(source.name + '.geometry-r-repair.tmp')
        write_exclusive(temporary, payload)
        a.require(a.fp(temporary) == a.SOURCE_FP and temporary.read_bytes() == payload,
                  'staged repaired source differs; preserve it for inspection')
        current = source.stat(follow_symlinks=False)
        a.require((current.st_dev, current.st_ino, current.st_size, current.st_mtime_ns) ==
                  (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns) and
                  a.fp(source) == a.ORIGINAL_SOURCE_FP and source.read_bytes() == original,
                  'canonical original changed during its serialized exact repair')
        os.replace(temporary, source)
    directory = os.open(source.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    a.require(a.fp(source) == a.SOURCE_FP and source.read_bytes() == payload,
              'installed source differs; preserve the file for inspection')
    return action


def worker(a, c, run):
    result = {'schema': 'p15_independent_geometry_source_install_v1', 'identity': c.identity,
        'installer': {'path': SCRIPT, **a.raw_fp(c.installer)}, 'source_installed': False,
        'normal_or_kernel_commands_executed': 0, 'new_owner_accepted': False, 'whole_P1_5_complete': False}
    state = before = None
    try:
        c.ag.d.verify_lane(c.ag.h)
        state = a.prepare(c)
        before = a.preservation_summary(c, state)
        c.ag.d.save(run / 'OLD_CONTEXT_BEFORE.json', before)
        source = a.PROJECT / a.SOURCE
        a.require_new_attempt(a.ROOT / c.commit / 'runs')
        a.require_new_slot(a.fp(source), c.g.module_artifacts(c.ag, a.TARGET), a.owner_history(), installed=False)
        result['source_before'] = a.fp(source)
        backup = None
        result['source_backup'] = None
        if result['source_before'] is not None:
            backup = run / 'canonical-source-before.lean'
            c.ag.d.write_frozen(backup, source.read_bytes())
            a.require(a.fp(backup) == result['source_before'], 'canonical source changed before its evidence backup')
            result['source_backup'] = {'path': str(backup), **result['source_before']}
        result['installation_action'] = install_exact(a, source, c.source, backup)
        a.require_new_slot(a.fp(source), c.g.module_artifacts(c.ag, a.TARGET), a.owner_history(), installed=True)
        a.unchanged(c, state)
        result.update(source_after=a.fp(source), source_installed=True)
    except Exception as error:
        result['installation_error'] = str(error)
    finally:
        try:
            if state is not None:
                a.unchanged(c, state)
                a.require_new_slot(a.fp(a.PROJECT / a.SOURCE), c.g.module_artifacts(c.ag, a.TARGET),
                                   a.owner_history(), installed=result['source_installed'])
                after = a.preservation_summary(c, state)
                c.ag.d.save(run / 'OLD_CONTEXT_AFTER.json', after)
                a.require(before is not None and after == before, 'original context preservation differs')
                result['preservation'] = after
        except Exception as error:
            result['preservation_error'] = str(error)
    c.ag.d.save(run / 'WORKER_RESULT.json', result)
    return int(not result['source_installed'] or
               bool(result.get('installation_error') or result.get('preservation_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true'); mode.add_argument('--install', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args(); path = Path(__file__)
    if not path.is_file() or path.is_symlink():
        raise RuntimeError('installer must be a regular file')
    a, c = load(args.source_commit, path.read_bytes())
    runs = a.INSTALL_ROOT / c.commit / 'runs'
    if args.check:
        a.require(args.inside_lane is None, 'read-only installation check has no worker lane')
        state = a.prepare(c)
        source = a.fp(a.PROJECT / a.SOURCE)
        a.require_new_slot(source, c.g.module_artifacts(c.ag, a.TARGET), a.owner_history(), installed=False)
        a.require_new_attempt(a.ROOT / c.commit / 'runs')
        if runs.exists() and any(runs.iterdir()):
            installation, _ = a.read_installation(c, state)
            a.require(source == a.SOURCE_FP, 'installed source differs from the original installer receipt')
            status = 'ORIGINAL_GEOMETRY_SOURCE_INSTALL_REVALIDATED_WITHOUT_EXECUTION'
        else:
            installation = None
            status = 'EXACT_GEOMETRY_SOURCE_READY_FOR_INSTALL'
        a.unchanged(c, state)
        print(json.dumps({'status': status, 'identity': c.identity, 'source': source,
            'installation': installation, 'normal_or_kernel_commands_executed': 0,
            'new_owner_accepted': False, 'whole_P1_5_complete': False}, sort_keys=True), flush=True)
        return 0
    if args.inside_lane:
        run = args.inside_lane
        a.require(run.is_absolute() and run.resolve() == run and run.parent == runs and
                  a.re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                  'unexpected Geometry installer worker path')
        a.require(a.unique_run(runs) == run, 'nonunique Geometry installer attempt')
        return worker(a, c, run)
    state = a.prepare(c)
    a.require_new_attempt(a.ROOT / c.commit / 'runs')
    a.require_new_slot(a.fp(a.PROJECT / a.SOURCE), c.g.module_artifacts(c.ag, a.TARGET),
                       a.owner_history(), installed=False)
    a.unchanged(c, state)
    return a.dispatch(c, installation=True)


if __name__ == '__main__':
    os.environ.update({'GIT_OPTIONAL_LOCKS': '0', 'GIT_NO_LAZY_FETCH': '1',
                       'GIT_TERMINAL_PROMPT': '0', 'PYTHONDONTWRITEBYTECODE': '1'})
    try:
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status': 'GEOMETRY_SOURCE_INSTALL_HOLD', 'error_type': type(error).__name__,
            'error': str(error), 'new_owner_accepted': False, 'whole_P1_5_complete': False}), flush=True)
        raise SystemExit(3)
