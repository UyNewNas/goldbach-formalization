#!/usr/bin/env python3
"""Install only the exact dictionary source. Unbound INPUTS prohibit any I/O."""
from pathlib import Path
from types import ModuleType
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PACKAGE = 'docs/p1/20261127/p15-historical-coefficient-dictionary/'
SCRIPT = PACKAGE + 'install_dictionary_source.py'
ADAPTER = PACKAGE + 'run_dictionary.py'
SOURCE_FP = {'bytes':9107, 'sha256':'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'}
AM = '45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c'
INPUTS = {'canonical_source': {'bytes': 9107,
                      'sha256': 'eb78b1ba6ced1f441b8b923210ef1fc32c107b307be69c0c3f6d2b8fd91d97ff'},
 'geometry': {'mode': 'accepted',
              'reader': {'bytes': 43509,
                         'sha256': 'e52e170a0d06b40b3d52020a2f2627df48dbd621c53099c696a8a0caac5703ff'},
              'reader_path': 'docs/p1/20261127/p15-remaining-typei-geometry/run_geometry.py',
              'readonly_report': {'bytes': 39914,
                                  'sha256': '6b83cb528cc7310f103650ddf4f3c01e14ef8851dd5d709d424894305d7f564b'},
              'source_commit': '938a761761f0e8a96404f843488f0a733818b156'},
 'probe_document': {'bytes': 88316,
                    'sha256': '01236d55c4b7d0434066be11b504aaae013ccdfebb6388f5c587e2ab4906561c'},
 'probe_job': 'job_d2088f6dcc48496082022225e68d2920',
 'probe_publication': '74926278c913d45401225c1b7e08185c9eec57e9'}


def require_bound_inputs():
    def pin(p):
        return (isinstance(p, dict) and set(p) == {'bytes','sha256'} and
                type(p['bytes']) is int and p['bytes'] >= 0 and isinstance(p['sha256'],str) and
                re.fullmatch('[0-9a-f]{64}',p['sha256']) is not None)
    if not (isinstance(INPUTS,dict) and INPUTS.get('canonical_source') == SOURCE_FP and
            isinstance(INPUTS.get('probe_publication'),str) and
            re.fullmatch('[0-9a-f]{40}',INPUTS['probe_publication']) and INPUTS['probe_publication'] != AM and
            pin(INPUTS.get('probe_document')) and
            INPUTS['probe_document']['bytes'] > 0 and
            isinstance(INPUTS.get('probe_job'),str) and re.fullmatch('job_[0-9a-f]{32}',INPUTS['probe_job']) and
            isinstance(INPUTS.get('geometry'),dict) and INPUTS['geometry'].get('mode') in ('unaccepted','accepted')):
        raise RuntimeError('dictionary installer INPUTS are unbound; no file or process operation permitted')
    geometry = INPUTS['geometry']
    if geometry['mode'] == 'unaccepted':
        complete = 'source' in geometry and (geometry['source'] is None or pin(geometry['source']))
    else:
        complete = (isinstance(geometry.get('source_commit'),str) and
            re.fullmatch('[0-9a-f]{40}',geometry['source_commit']) and
            geometry.get('reader_path') == 'docs/p1/20261127/p15-remaining-typei-geometry/run_geometry.py' and
            pin(geometry.get('reader')) and pin(geometry.get('readonly_report')))
    if not complete:
        raise RuntimeError('dictionary installer Geometry preservation INPUTS are unbound')


def load(commit, executed):
    require_bound_inputs()
    if not isinstance(commit,str) or re.fullmatch('[0-9a-f]{40}',commit) is None:
        raise RuntimeError('installer needs an exact formal publication commit')
    raw = subprocess.check_output(['git','show',commit+':'+ADAPTER],cwd=REPO)
    adapter = ModuleType('published_independent_dictionary'); adapter.__file__ = ADAPTER
    exec(compile(raw, ADAPTER, 'exec'), adapter.__dict__)
    adapter.require(adapter.INPUTS == INPUTS, 'installer and adapter actual bindings differ')
    c = adapter.load(commit, raw)
    adapter.require(executed == adapter.git_file(commit,SCRIPT) and SCRIPT == adapter.INSTALLER,
                    'executed dictionary installer differs from publication')
    c.installer = executed
    return adapter,c


def install_exact(a, source, payload, backup):
    require_bound_inputs()
    a.validate_inputs(a.INPUTS)
    a.require(a.raw_fp(payload) == a.SOURCE_FP == SOURCE_FP, 'only frozen dictionary bytes may be installed')
    a.require(source.parent.is_dir() and source.parent.resolve() == source.parent and
              source.resolve() == source, 'canonical source parent traverses a symlink')
    before = a.fp(source); action = a.installation_action(before)
    if before == a.SOURCE_FP:
        a.require(source.read_bytes() == payload, 'identical source has different bytes')
        return action
    write_exclusive(source,payload)
    directory = os.open(source.parent,os.O_RDONLY|os.O_DIRECTORY)
    try:
        os.fsync(directory)
    finally:
        os.close(directory)
    a.require(a.fp(source) == a.SOURCE_FP and source.read_bytes() == payload,
              'installed source differs; preserve it for inspection')
    return action


def write_exclusive(path, payload):
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW, 0o644)
    with os.fdopen(descriptor, 'wb') as stream:
        stream.write(payload); stream.flush(); os.fsync(stream.fileno())



def worker(a, c, run):
    require_bound_inputs()
    a.validate_inputs(a.INPUTS)
    result = {'schema': 'p15_independent_dictionary_source_install_v1', 'identity': c.identity,
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
    require_bound_inputs()
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
            status = 'ORIGINAL_DICTIONARY_SOURCE_INSTALL_REVALIDATED_WITHOUT_EXECUTION'
        else:
            installation = None
            status = 'EXACT_DICTIONARY_SOURCE_READY_FOR_INSTALL'
        a.unchanged(c, state)
        print(json.dumps({'status': status, 'identity': c.identity, 'source': source,
            'installation': installation, 'normal_or_kernel_commands_executed': 0,
            'new_owner_accepted': False, 'whole_P1_5_complete': False}, sort_keys=True), flush=True)
        return 0
    if args.inside_lane:
        run = args.inside_lane
        a.require(run.is_absolute() and run.resolve() == run and run.parent == runs and
                  a.re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                  'unexpected Dictionary installer worker path')
        a.require(a.unique_run(runs) == run, 'nonunique Dictionary installer attempt')
        return worker(a, c, run)
    state = a.prepare(c)
    a.require_new_attempt(a.ROOT / c.commit / 'runs')
    a.require_new_slot(a.fp(a.PROJECT / a.SOURCE), c.g.module_artifacts(c.ag, a.TARGET),
                       a.owner_history(), installed=False)
    a.unchanged(c, state)
    return a.dispatch(c, installation=True)


if __name__ == '__main__':
    try:
        require_bound_inputs()
        os.environ.update({'GIT_OPTIONAL_LOCKS':'0','GIT_NO_LAZY_FETCH':'1',
                           'GIT_TERMINAL_PROMPT':'0','PYTHONDONTWRITEBYTECODE':'1'})
        raise SystemExit(main())
    except Exception as error:
        print(json.dumps({'status':'DICTIONARY_SOURCE_INSTALL_HOLD','error_type':type(error).__name__,
            'error':str(error),'new_owner_accepted':False,'whole_P1_5_complete':False}),flush=True)
        raise SystemExit(3)
