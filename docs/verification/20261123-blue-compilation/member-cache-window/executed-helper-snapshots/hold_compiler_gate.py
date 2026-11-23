#!/usr/bin/env python3
"""Hold an existing unmodified compiler flock between source processes."""
from pathlib import Path
import argparse
import datetime
import fcntl
import hashlib
import json
import os
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--state', type=Path, required=True)
parser.add_argument('--evidence', type=Path, required=True)
args = parser.parse_args()
state_bytes = args.state.read_bytes()
state = json.loads(state_bytes)
slot = Path(state['slot'])
args.evidence.mkdir(parents=True, exist_ok=False)
release = args.evidence / 'RELEASE_GATE'


def save(name, record):
    target = args.evidence / name
    temporary = target.with_suffix(target.suffix + '.tmp')
    temporary.write_text(json.dumps(record, indent=2) + '\n')
    temporary.replace(target)


with slot.open('a') as handle:
    fcntl.flock(handle, fcntl.LOCK_EX)
    record = dict(pid=os.getpid(), slot=str(slot), lock_kind='fcntl.flock_LOCK_EX',
                  slot_device=slot.stat().st_dev, slot_inode=slot.stat().st_ino,
                  state_path=str(args.state),
                  state_sha256=hashlib.sha256(state_bytes).hexdigest(),
                  acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  policy='Existing guard unchanged; wait for preceding compiler to exit; '
                         'explicit release file required')
    save('GATE_ACQUIRED.json', record)
    print(json.dumps(record), flush=True)
    while not release.exists():
        time.sleep(0.2)
    record['released_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save('GATE_RELEASED.json', record)
print(json.dumps(record), flush=True)
