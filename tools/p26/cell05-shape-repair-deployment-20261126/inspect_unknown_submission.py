#!/usr/bin/env python3
"""Read only the new Shape deployment paths after a submission without a job ID."""
from pathlib import Path
import hashlib
import json

roots = [
    Path('/workspace/p26-continuation-557a12f3bcd7/cell05-shape-repair-deploy-v1'),
    Path('/workspace/p26-continuation-557a12f3bcd7/cell05-shape-repair-package-v1'),
    Path('/workspace/p26-cell05-shape-repair-stage-557a12f3bcd7')]
records = []
for root in roots:
    record = {'path': str(root), 'exists': root.exists(), 'symlink': root.is_symlink(), 'files': []}
    if root.is_dir() and not root.is_symlink():
        for path in sorted(root.rglob('*')):
            if path.is_file() and not path.is_symlink():
                data = path.read_bytes()
                record['files'].append({'relative_path': str(path.relative_to(root)),
                                        'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
    records.append(record)
print(json.dumps({'schema': 'cell05_shape_unknown_submission_readonly_v1',
                  'roots': records, 'writes': 0, 'Lean_commands': 0}, indent=2))
