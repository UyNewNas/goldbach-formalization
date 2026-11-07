#!/usr/bin/env python3
"""Check archived source/receipt identity, without running or certifying Lean.

Use --index before committing to check the exact Git blobs being published.
An identity PASS is not a new compilation, kernel replay, or axiom audit.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[3]
MANIFEST = 'verification/checkpoints/2026-10-13/manifest.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--index', action='store_true')
    args = parser.parse_args()

    def read(path):
        if args.index:
            return subprocess.check_output(['git', 'show', ':' + path], cwd=ROOT)
        return (ROOT / path).read_bytes()

    def require(condition, message):
        if not condition:
            raise ValueError(message)

    manifest = json.loads(read(MANIFEST))
    require(manifest['claim'] == 'archived_component_progress_only', 'Bad scope')
    for path, expected in manifest['files'].items():
        data = read(path)
        require(len(data) == expected['bytes'], 'Size mismatch: ' + path)
        require(hashlib.sha256(data).hexdigest() == expected['sha256'],
                'Hash mismatch: ' + path)
    names = [row['module'] for row in manifest['modules']]
    require(len(names) == len(set(names)), 'Duplicate module')
    for row in manifest['modules']:
        receipt = json.loads(read(row['receipt']))
        source_hash = hashlib.sha256(read(row['source'])).hexdigest()
        require(receipt['status'] == 'PASS' and receipt['exit_code'] == 0,
                'No successful compilation receipt: ' + row['module'])
        require(receipt['module'] == row['module'], 'Module mismatch')
        require(receipt['source_sha256'] == source_hash ==
                receipt['source_sha256_after'], 'Source/receipt mismatch')
        require(receipt['dependencies'] == receipt['dependency_objects_after'],
                'Dependencies changed during compilation')
        require(receipt['object_sha256'] == row['recorded_object_sha256'],
                'Recorded object hash mismatch')
        require(receipt['warnings_as_errors'] == row['warnings_as_errors'],
                'Compilation mode mismatch')
        require(('-t0' in receipt['command']) == row['trust_level_zero'],
                'Trust mode mismatch')
        require(len(read(row['stdout'])) == 0, 'Expected complete empty log')
    print(json.dumps({
        'status': 'PASS_SOURCE_AND_ARCHIVE_IDENTITY_ONLY',
        'storage': 'git-index' if args.index else 'working-tree',
        'files': len(manifest['files']), 'compiled_modules': len(names),
        'new_lean_execution': False, 'unconditional_main_theorem': False,
    }, indent=2))


if __name__ == '__main__':
    main()
