#!/usr/bin/env python3
"""Read-only targeted recovery of existing P1 raw05 verification records."""
from pathlib import Path
import hashlib
import json
import os

TOKEN = 'P2OriginalSaving19ArchiveGeometryData05'
ROOT = Path('/workspace')
SKIP = {'.git', '.lake', 'toolchains', 'node_modules', '.compile-home', '.npm',
        'proc', 'sys', 'dev', 'mathlib', 'compile-deps'}
NAMES = {'RESULT.json', 'NORMAL_PASS.json', 'KERNEL_PASS.json', 'kernel-result.json',
         'normal-result.json', 'result.json', 'ACCEPTED_STEP.json'}


def main():
    candidates = []
    for directory, dirs, files in os.walk(ROOT):
        dirs[:] = [d for d in dirs if d not in SKIP]
        if TOKEN not in directory:
            continue
        for name in files:
            if name not in NAMES:
                continue
            path = Path(directory) / name
            data = path.read_bytes()
            try:
                value = json.loads(data)
            except (ValueError, UnicodeDecodeError):
                continue
            candidates.append({'path': str(path), 'bytes': len(data),
                               'sha256': hashlib.sha256(data).hexdigest(),
                               'status': value.get('status'), 'exit_code': value.get('exit_code'),
                               'keys': list(value)})
    print(json.dumps({'target': TOKEN, 'candidate_count': len(candidates), 'candidates': candidates}, indent=2))


if __name__ == '__main__':
    main()
