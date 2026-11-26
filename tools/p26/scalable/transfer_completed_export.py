#!/usr/bin/env python3
"""Read-only exact export transport; stdout is base64 payload, no Lean call."""
from pathlib import Path
import base64
import hashlib
import sys

path = Path('/workspace/p26-continuation-59264dd64286/scalable-geometry/exports/cell05-scalable-completed-evidence.tar.xz')
data = path.read_bytes()
assert len(data) == 1462880
assert hashlib.sha256(data).hexdigest() == '1fb3fd544b39648bbcf8511ac559ce3ccce98e9fc6ccffc2b164e464046da505'
sys.stdout.write(base64.b64encode(data).decode('ascii'))
sys.stdout.flush()
