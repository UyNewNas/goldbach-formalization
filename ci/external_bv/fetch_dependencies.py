#!/usr/bin/env python3
"""Fetch only reviewed source commits with system git; do not load Lake or package code."""
import json
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
review = json.loads((HERE / 'closure.json').read_text())
manifest = json.loads((HERE / 'upstream-manifest.json').read_text())
root = Path(sys.argv[1]).resolve()
if json.loads((root / 'lake-manifest.json').read_text()) != manifest:
    raise SystemExit('Root manifest differs from reviewed manifest')
expected = {p['name']: p for p in review['dependencyConfigs']}
if len(expected) != len(manifest['packages']):
    raise SystemExit('Dependency set differs from reviewed set')
if manifest['packagesDir'] != '.lake/packages':
    raise SystemExit('Unexpected dependency destination')
packages = root / '.lake/packages'
packages.mkdir(parents=True, exist_ok=True)

def git(*args):
    subprocess.run(['/usr/bin/git', '-c', 'core.hooksPath=/dev/null',
                    '-c', 'protocol.file.allow=never', *args], check=True)

for item in manifest['packages']:
    name, rev = item['name'], item['rev']
    config = expected.get(name)
    if not re.fullmatch(r'[A-Za-z0-9_-]+', name) or not re.fullmatch(r'[0-9a-f]{40}', rev):
        raise SystemExit('Invalid dependency name or immutable revision')
    if (config is None or rev != config['rev'] or item['type'] != 'git'
            or item['subDir'] is not None
            or item['url'].removesuffix('.git') != 'https://github.com/' + config['repo']
            or item['configFile'] != config['path']):
        raise SystemExit(f'Unreviewed dependency: {name}')
    path = packages / name
    if path.exists() or path.is_symlink():
        raise SystemExit(f'Dependency directory already exists: {name}')
    git('init', '--quiet', str(path))
    git('-C', str(path), 'remote', 'add', 'origin', item['url'])
    git('-C', str(path), 'fetch', '--no-tags', '--depth=1', 'origin', rev)
    git('-C', str(path), 'checkout', '--detach', rev)
    actual = subprocess.check_output(['/usr/bin/git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != rev:
        raise SystemExit(f'Wrong fetched commit: {name}')
    print(f'Fetched {name} at {rev}', flush=True)
