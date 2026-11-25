#!/usr/bin/env python3
"""One new owner only; reuse pinned dependencies, never compile accepted owners."""
from pathlib import Path
import argparse
import hashlib
import json
import os
import signal
import subprocess
import time

import psutil

ROOT = Path(__file__).resolve().parent
TOOLCHAIN = Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux')
MODULE = 'ImbalancedChen.P2OriginalSaving19PositiveBalanceSegments00'
RSS_LIMIT = 4 * 1024**3
WALL_LIMIT = 180


def fp(p):
    p = Path(p)
    b = p.read_bytes()
    return {'path': str(p), 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}


def matches(expected):
    actual = fp(expected['path'])
    assert actual == expected, ('Input/object changed', actual, expected)
    return actual


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['normal', 'kernel'])
    parser.add_argument('--attempt', default='initial')
    args = parser.parse_args()
    assert args.attempt.replace('-', '').replace('_', '').isalnum()
    manifest = json.loads((ROOT/'SOURCE_MANIFEST.json').read_text())
    expected = manifest['files'][0]
    source = ROOT/expected['path']
    source_info = fp(source)
    assert source_info['sha256'] == expected['sha256'] and source_info['bytes'] == expected['bytes']
    assert expected['imports'] == ['ImbalancedChen.P2OriginalSaving19FirstThreeFields00'], \
        'External-child mode requires its own separately reviewed dependency closure.'
    obj = ROOT/'objects'/(MODULE.replace('.', '/') + '.olean')
    stem = args.mode + '-' + args.attempt
    log = ROOT/'logs'/(stem+'.log')
    command = ROOT/'logs'/(stem+'-command.json')
    result = ROOT/'logs'/(stem+'-result.json')
    assert not any(p.exists() for p in [log, command, result]), 'Attempt receipts are immutable.'
    assert args.mode != 'normal' or not obj.exists(), 'Do not overwrite a produced object.'

    dependency_copies = []
    for item in manifest['reused_dependencies']:
        matches(item['source'])
        original = matches(item['object'])
        copy = ROOT/'objects'/(item['module'].replace('.', '/') + '.olean')
        copy.parent.mkdir(parents=True, exist_ok=True)
        if copy.exists():
            assert copy.read_bytes() == Path(original['path']).read_bytes()
        else:
            copy.write_bytes(Path(original['path']).read_bytes())
        copied = fp(copy)
        assert (copied['bytes'], copied['sha256']) == (original['bytes'], original['sha256'])
        dependency_copies.append({'module': item['module'], 'original': original, 'copy': copied})

    def invariants():
        records = [matches(manifest['fixture'])]
        for item in manifest['reused_dependencies']:
            records += [matches(item['source']), matches(item['object'])]
        records += [matches(row['copy']) for row in dependency_copies]
        assert fp(source) == source_info
        return records

    version = subprocess.run([str(TOOLCHAIN/'bin/lean'), '--version'],
                             capture_output=True, text=True, check=True).stdout.strip()
    assert '4.33.0-rc1' in version and '62eed1db4d67327ec8120be05f1a1b0847d74561' in version
    if args.mode == 'kernel':
        normal = json.loads((ROOT/'logs'/('normal-'+args.attempt+'-result.json')).read_text())
        assert normal['status'] == 'succeeded' and normal['exit_code'] == 0
        assert normal['source'] == source_info and normal['object'] == fp(obj)
        argv = [str(TOOLCHAIN/'bin/leanchecker'), '--verbose', MODULE]
    else:
        argv = [str(TOOLCHAIN/'bin/lean'), '-j1', '-DmaxRecDepth=1000000',
                '-DmaxHeartbeats=0', '-o', str(obj), str(source)]
    env = os.environ.copy()
    env['PATH'] = str(TOOLCHAIN/'bin') + os.pathsep + env.get('PATH', '')
    env['LEAN_PATH'] = str(ROOT/'objects')
    env['LEAN_NUM_THREADS'] = env['OMP_NUM_THREADS'] = '1'
    before = invariants()
    record = {'mode': args.mode, 'attempt': args.attempt, 'module': MODULE,
              'source': source_info, 'manifest': fp(ROOT/'SOURCE_MANIFEST.json'),
              'argv': argv, 'cwd': str(ROOT), 'LEAN_PATH': env['LEAN_PATH'],
              'lean_version': version, 'runtime': fp(TOOLCHAIN/'bin/lean'),
              'rss_limit_bytes': RSS_LIMIT, 'wall_seconds': WALL_LIMIT,
              'rss_sample_seconds': 0.02, 'started_unix': time.time(),
              'dependency_copies': dependency_copies, 'invariants_before': before,
              'accepted_dependencies_recompiled': False, 'production_modified': False,
              'remote_jobs_submitted': False, 'old_string_equivalence_claimed': False,
              'whole_parse_success_claimed': False,
              'scope': 'local diagnostic of one new fourth-field original-reader transition owner'}
    command.write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({'mode': args.mode, 'source_sha256': source_info['sha256'],
                      'argv': argv, 'limits': [RSS_LIMIT, WALL_LIMIT]}), flush=True)
    start = time.monotonic()
    peak = 0
    cpu_peak = 0.0
    reason = None
    with log.open('w') as out:
        proc = subprocess.Popen(argv, cwd=ROOT, env=env, stdout=out,
                                stderr=subprocess.STDOUT, start_new_session=True)
        process = psutil.Process(proc.pid)
        while True:
            rc = proc.poll()
            rss = 0
            try:
                procs = [process] + process.children(recursive=True)
                rss = sum(p.memory_info().rss for p in procs if p.is_running())
                cpu = sum(p.cpu_times().user + p.cpu_times().system for p in procs if p.is_running())
                peak = max(peak, rss)
                cpu_peak = max(cpu_peak, cpu)
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                pass
            if rc is not None:
                break
            elapsed = time.monotonic() - start
            if rss > RSS_LIMIT:
                reason = 'memory_limit'
            elif elapsed > WALL_LIMIT:
                reason = 'timeout'
            if reason:
                os.killpg(proc.pid, signal.SIGKILL)
                break
            time.sleep(0.02)
        rc = proc.wait()
    record.update({'status': reason or ('succeeded' if rc == 0 else 'failed'),
                   'exit_code': rc, 'elapsed_seconds': time.monotonic()-start,
                   'peak_rss_bytes': peak, 'sampled_cpu_seconds': cpu_peak,
                   'object': fp(obj) if obj.exists() else None, 'log': fp(log),
                   'invariants_after': invariants()})
    result.write_text(json.dumps(record, indent=2)+'\n')
    print(log.read_text(), end='', flush=True)
    print(json.dumps({k: record[k] for k in ['status', 'exit_code', 'elapsed_seconds',
                                           'peak_rss_bytes', 'source', 'object', 'log']}), flush=True)
    raise SystemExit(0 if record['status'] == 'succeeded' else 1)


if __name__ == '__main__':
    main()
