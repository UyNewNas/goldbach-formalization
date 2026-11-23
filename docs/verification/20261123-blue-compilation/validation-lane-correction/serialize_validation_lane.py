#!/usr/bin/env python3
"""Serialize a whole validation chain on a lane keyed to an existing slot.

This lock is distinct from compiler.lock: Lake may safely invoke its original
wrapped --githash/source tools while the lane covers normal/kernel/audit.
It does not add or change a compiler guard, memory flag, or runtime binary.
"""
from pathlib import Path
import argparse, datetime, fcntl, hashlib, json, os, subprocess, time

ap = argparse.ArgumentParser()
ap.add_argument('--state', type=Path, required=True)
ap.add_argument('--receipt', type=Path, required=True)
ap.add_argument('command', nargs=argparse.REMAINDER)
args = ap.parse_args()
assert args.command
state_bytes = args.state.read_bytes()
state = json.loads(state_bytes)
lane = Path(state['slot'] + '.validation-lane.lock')
record = {'status': 'WAITING_VALIDATION_LANE', 'pid': os.getpid(), 'state': str(args.state),
          'state_sha256': hashlib.sha256(state_bytes).hexdigest(), 'original_compiler_slot': state['slot'],
          'validation_lane_lock': str(lane), 'argv': args.command,
          'requested_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'no_compiler_guard_runtime_or_memory_limit_changes': True,
          'whole_chain_including_original_checker_serialized': True}
def save():
    tmp = args.receipt.with_suffix('.tmp')
    tmp.write_text(json.dumps(record, indent=2) + '\n')
    tmp.replace(args.receipt)
save()
t = time.monotonic()
with lane.open('a') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    record.update(status='VALIDATION_LANE_ACQUIRED', acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  queue_wait_seconds=time.monotonic()-t, lane_device=lane.stat().st_dev, lane_inode=lane.stat().st_ino)
    record['proc_locks_owner_lines'] = [s for s in Path('/proc/locks').read_text().splitlines()
        if 'FLOCK' in s and '->' not in s and (' ' + str(os.getpid()) + ' ') in s and str(lane.stat().st_ino) in s]
    assert record['proc_locks_owner_lines']
    save()
    start = time.monotonic()
    child = subprocess.Popen(args.command)
    record['child_pid'] = child.pid
    save()
    code = child.wait()
    record.update(status='VALIDATION_LANE_FINISHED', exit_code=code, execution_wall_seconds=time.monotonic()-start,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    save()
raise SystemExit(code)
