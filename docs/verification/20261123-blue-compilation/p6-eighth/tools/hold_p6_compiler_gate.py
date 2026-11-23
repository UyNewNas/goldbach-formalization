#!/usr/bin/env python3
"""Take the existing compiler flock between compilers; never alter the guard."""
from pathlib import Path
import datetime
import fcntl
import json
import os
import time

directory = Path('/workspace/blue-p6-controller/eighth/reuse-pause')
directory.mkdir(exist_ok=True)
release = directory / 'RELEASE_GATE'
assert not release.exists(), 'This gate receipt already has a release request'
slot = Path('/workspace/blue-build-tools/runtime-evidence/compiler.lock')
with slot.open('a') as handle:
    fcntl.flock(handle, fcntl.LOCK_EX)
    result = dict(pid=os.getpid(), slot=str(slot), lock_kind='fcntl.flock_LOCK_EX',
                  slot_device=slot.stat().st_dev, slot_inode=slot.stat().st_ino,
                  acquired_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  policy='No guard/source/output edit; acquisition waits for preceding compiler to exit')
    (directory / 'GATE_ACQUIRED.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)
    while not release.exists():
        time.sleep(0.2)
    result['released_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    (directory / 'GATE_RELEASED.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result), flush=True)
