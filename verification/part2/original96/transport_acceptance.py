#!/usr/bin/env python3
"""Read-only bounded transport of an already completed cloud acceptance."""
from pathlib import Path
import argparse
import base64
import hashlib
import json

ROOT = Path('/workspace/p2-1-original96-20261126')
ARCHIVE = ROOT / 'original96-acceptance-attempt-002.tar.xz'
RECORD = ROOT / 'evidence/original96-acceptance/attempt-002'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--offset', type=int)
    parser.add_argument('--length', type=int, default=900000)
    args = parser.parse_args()
    assert Path.cwd().resolve() == ROOT
    data = ARCHIVE.read_bytes()
    metadata = {'path': str(ARCHIVE), 'bytes': len(data),
                'sha256': hashlib.sha256(data).hexdigest()}
    print('P21_ARCHIVE_META ' + json.dumps(metadata), flush=True)
    if args.offset is None:
        summary = json.loads((RECORD / 'summary.json').read_text())
        print('P21_PROOF_SUMMARY ' + json.dumps(summary), flush=True)
        failure = json.loads((RECORD / 'failure.json').read_text())
        print('P21_TRANSPORT_FAILURE ' + json.dumps(failure), flush=True)
        return
    assert 0 <= args.offset < len(data)
    assert 0 < args.length <= 900000
    part = data[args.offset:args.offset + args.length]
    print('P21_ARCHIVE_PART ' + json.dumps({'offset': args.offset,
          'bytes': len(part), 'sha256': hashlib.sha256(part).hexdigest(),
          'base64': base64.b64encode(part).decode()}), flush=True)

if __name__ == '__main__':
    main()
