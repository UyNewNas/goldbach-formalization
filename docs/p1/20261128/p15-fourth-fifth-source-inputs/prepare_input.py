#!/usr/bin/env python3
"""Materialize the existing, hash-verified fourth input at the reader's path."""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

EXPECTED = '561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da'
REL = 'proof-continuation-data/fourth-original/FourthRows17LE.bin'

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repository', type=Path, default=Path.cwd())
parser.add_argument('--source', type=Path)
args = parser.parse_args()
repo = args.repository.resolve()
target = repo / 'ImbalancedChen/provenance/original-fourth/FourthRows17LE.bin'
if target.exists():
    assert target.stat().st_size == 62885159 and digest(target) == EXPECTED
else:
    target.parent.mkdir(parents=True, exist_ok=True)
    source = args.source or repo / REL
    with tempfile.NamedTemporaryFile(dir=target.parent, prefix='.p1-fourth-input-', delete=False) as temp:
        temporary = Path(temp.name)
        if source.exists():
            with source.open('rb') as stream:
                shutil.copyfileobj(stream, temp)
        else:
            assert args.source is None
            subprocess.run(['git', 'show', 'HEAD:' + REL], cwd=repo, stdout=temp, check=True)
    try:
        assert temporary.stat().st_size == 62885159 and digest(temporary) == EXPECTED
        try:
            os.link(temporary, target)
        except FileExistsError:
            assert target.stat().st_size == 62885159 and digest(target) == EXPECTED
    finally:
        temporary.unlink()
print('Verified original fourth input: 62885159 bytes, SHA256 ' + EXPECTED)
