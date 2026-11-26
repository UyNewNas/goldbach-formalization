#!/usr/bin/env python3
"""Read-only transfer of the exact raw05 current-context kernel addendum."""
from pathlib import Path
import base64
import hashlib
import sys

path = Path('/workspace/p26-continuation-59264dd64286/scalable-geometry/raw05-context-compatibility/20261126T050034319756Z/raw05-current-context-kernel-addendum.tar.xz')
data = path.read_bytes()
assert len(data) == 11944
assert hashlib.sha256(data).hexdigest() == 'a37b3796dbc51f9a2b103bb851d0f8e3a4aaf4ca0860c6f0c1f5e53cce849d67'
sys.stdout.write(base64.b64encode(data).decode('ascii'))
sys.stdout.flush()
