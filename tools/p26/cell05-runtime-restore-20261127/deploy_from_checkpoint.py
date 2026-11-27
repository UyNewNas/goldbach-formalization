#!/usr/bin/env python3
"""Deploy and run the reviewed exact-byte restorer from an immutable checkpoint."""
import base64
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import urllib.request

COMMIT = '447127edc4a97db1ebc3fa9c1793e390ef2e3e49'
BASE = 'https://raw.githubusercontent.com/UyNewNas/goldbach-formalization/' + COMMIT + '/'
STAGE = Path('/workspace/p26-runtime-missing-bytes-20261127-v1')
ROWS = [
    ('docs/verification/20261127-p26/runtime-recovery/p1-mathlib-missing-original-bytes.tar.xz',
     'p1-mathlib-missing-original-bytes.tar.xz', 2962644,
     '9d4a34bbd76678005e5c0c8368a2d2509e47705ee76dc7c0d3e279ed512329db'),
    ('tools/p26/cell05-runtime-restore-20261127/restore_missing.py',
     'restore_missing.py', 15467,
     '3861a2ede46a42a8c7949f0624bd926c91d9c531808c934ae61b53ecb23a5023'),
]


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    require(STAGE.resolve(strict=True) == STAGE and STAGE.is_dir(), 'Wrong transport stage')
    # Independent observation requested by the historical context reviewer.
    # It does not modify or replace any original package or context.
    package = Path('/workspace/p26-cell05-shape-repair-stage-557a12f3bcd7/PACKAGE_CONTENTS.json')
    require(package.resolve(strict=True) == package and package.is_file(), 'Missing original ShapeArrays package manifest')
    body = package.read_bytes()
    print(json.dumps({'kind': 'original_shape_package', 'path': str(package), 'bytes': len(body),
                      'sha256': hashlib.sha256(body).hexdigest(), 'body_base64': base64.b64encode(body).decode()}), flush=True)
    for relative, name, size, digest in ROWS:
        request = urllib.request.Request(BASE + relative, headers={'User-Agent': 'P26-exact-byte-restoration'})
        with urllib.request.urlopen(request, timeout=120) as response:
            body = response.read(size + 1)
        require(len(body) == size and hashlib.sha256(body).hexdigest() == digest, 'Checkpoint download differs: ' + relative)
        destination = STAGE / name
        require(destination.resolve() == destination and not destination.is_symlink(), 'Noncanonical deployment path')
        if destination.exists():
            require(destination.is_file() and destination.read_bytes() == body, 'Different existing deployment bytes')
        else:
            with destination.open('xb') as output:
                output.write(body)
        print(json.dumps({'kind': 'exact_checkpoint_file_present', 'commit': COMMIT,
                          'path': str(destination), 'bytes': size, 'sha256': digest}), flush=True)
    result = subprocess.run([sys.executable, '-I', '-S', '-B', str(STAGE / 'restore_missing.py'), 'restore'],
                            cwd='/workspace', check=False, timeout=600)
    require(result.returncode == 0, 'Exact-byte restorer stopped; retain all evidence without retry')
    print(json.dumps({'kind': 'deployment_finished', 'commit': COMMIT, 'new_Lean_commands': 0,
                      'runtime_compatibility_accepted': False, 'P2_6_complete': False}), flush=True)


if __name__ == '__main__':
    main()
