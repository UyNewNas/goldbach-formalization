#!/usr/bin/env python3
"""Materialize the existing, hash-verified sixth input at the reader's path."""
import argparse
import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

EXPECTED = '406623527077e0cd424f2098713e70125795eafbee758d21f16d19d89dfb9be8'
REL = 'docs/source-only/20261102-resume-30s/s09_actual_full_sixth/provenance/OriginalSixthCells.npy'

def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repository', type=Path, default=Path.cwd())
parser.add_argument('--source', type=Path)
args = parser.parse_args()
repo = args.repository.resolve()
target = repo / 'ImbalancedChen/provenance/OriginalSixthCells.npy'
if target.exists():
    assert target.stat().st_size == 55625280 and digest(target) == EXPECTED
else:
    target.parent.mkdir(parents=True, exist_ok=True)
    source = args.source or repo / REL
    with tempfile.NamedTemporaryFile(dir=target.parent, prefix='.p1-sixth-input-', delete=False) as temp:
        temporary = Path(temp.name)
        if source.exists():
            with source.open('rb') as stream:
                shutil.copyfileobj(stream, temp)
        else:
            assert args.source is None
            subprocess.run(['git', 'show', 'HEAD:' + REL], cwd=repo, stdout=temp, check=True)
    try:
        assert temporary.stat().st_size == 55625280 and digest(temporary) == EXPECTED
        try:
            os.link(temporary, target)
        except FileExistsError:
            assert target.stat().st_size == 55625280 and digest(target) == EXPECTED
    finally:
        temporary.unlink()
print('Verified original sixth input: 55625280 bytes, SHA256 ' + EXPECTED)
