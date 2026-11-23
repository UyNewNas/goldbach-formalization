#!/usr/bin/env python3
"""Run one normal P6 aggregate with the existing guard and retain every attempt."""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import json
import subprocess
import time

ROOT = Path('/workspace/blue-p6-controller')
TARGETS = {
    'seventh': 'ImbalancedChen.P6OriginalSeventhMeshPrice',
    'eighth': 'ImbalancedChen.P6OriginalEighthMeshPrice',
    'ninth': 'ImbalancedChen.P6OriginalNinthMeshPrice',
    'zero': 'ImbalancedChen.P6OriginalZeroMarkedIntegralCost',
}


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase', choices=TARGETS)
    args = parser.parse_args()
    lock = (ROOT / 'controller.lock').open('a')
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    directory = ROOT / args.phase
    directory.mkdir(exist_ok=True)
    attempt = 1
    while (directory / f'BUILD_PROCESS.attempt{attempt}.json').exists():
        attempt += 1
    target = TARGETS[args.phase]
    command = ['python3', '/workspace/blue-build-tools/run_guarded.py',
               'lake', 'build', '+' + target + ':olean']
    record = {'command': command, 'cwd': '/workspace/blue-p6-build',
              'target': target, 'attempt': attempt,
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'guard_log_start_bytes': Path('/workspace/blue-build-tools/runtime-evidence/compiler-commands.jsonl').stat().st_size}
    state = json.loads((ROOT / 'STATE.json').read_bytes())
    state.update(current_target=target, current_phase=args.phase,
                 status='RUNNING_NORMAL_BUILD', current_attempt=attempt)
    save(directory / 'BUILD_PROCESS.json', record)
    start = time.monotonic()
    with (directory / 'build.log').open('wb') as output:
        child = subprocess.Popen(command, cwd=record['cwd'], stdout=output,
                                 stderr=subprocess.STDOUT)
        record['pid'] = child.pid
        state['child_pid'] = child.pid
        save(directory / 'BUILD_PROCESS.json', record)
        save(ROOT / 'STATE.json', state)
        code = child.wait()
    record.update(exit_code=code, elapsed_seconds=time.monotonic() - start,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  log_sha256=hashlib.sha256((directory / 'build.log').read_bytes()).hexdigest())
    save(directory / 'BUILD_PROCESS.json', record)
    save(directory / f'BUILD_PROCESS.attempt{attempt}.json', record)
    (directory / f'build.attempt{attempt}.log').write_bytes((directory / 'build.log').read_bytes())
    state.update(status='BUILD_PASS_PENDING_KERNEL_AUDIT' if code == 0 else
                 'BUILD_FAILED_PENDING_DIAGNOSIS', last_build=record)
    state.pop('child_pid', None)
    save(ROOT / 'STATE.json', state)
    print(json.dumps(record))
    print((directory / 'build.log').read_text()[-14000:])


if __name__ == '__main__':
    main()
