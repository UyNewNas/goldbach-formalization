#!/usr/bin/env python3
"""Fail closed before publishing a CI-triggering ref update.

Feed the exact parent-to-candidate changed-path list from GitHub compare or
an equivalent Git diff. This does not perform any GitHub write or proof run.
"""
import argparse, json
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument('--message', required=True)
p.add_argument('--paths-json', required=True)
a = p.parse_args()
paths = json.loads(Path(a.paths_json).read_text())
assert isinstance(paths, list) and all(isinstance(x, str) for x in paths)
assert len(paths) == len(set(paths)), 'Duplicate changed path'
if '[skip ci]' not in a.message.lower():
    assert paths == ['automation/dispatch.json'], 'Trigger commits may change only automation/dispatch.json; publish all source/config/status changes first with [skip ci]'
print(json.dumps({'status': 'PASS_PUBLICATION_PATH_SCOPE_ONLY', 'skip_ci': '[skip ci]' in a.message.lower(), 'changed_paths': paths}))
