"""Remote-only pinned-package source provenance, without invoking Lean/Lake."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--project', type=Path, required=True)
parser.add_argument('--manifest', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
if os.getenv('GITHUB_ACTIONS') != 'true':
    raise SystemExit('Remote GitHub Actions evidence recording only')
manifest = json.loads(args.manifest.read_text())
lock = json.loads((args.project / 'lake-manifest.json').read_text())
packages = []
for p in lock['packages']:
    path = args.project / lock['packagesDir'] / p['name']
    head = subprocess.check_output(['git', '-C', str(path), 'rev-parse', 'HEAD'], text=True).strip()
    if head != p['rev']:
        raise SystemExit(f'Package commit mismatch: {p["name"]}')
    dirty = subprocess.check_output(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], text=True)
    if dirty:
        changed = subprocess.check_output(['git', '-C', str(path), 'diff', '--name-only', 'HEAD', '--'], text=True).splitlines()
        selected = manifest['native_configuration']['selected']
        if p['name'] != 'goldbach' or changed != ['lakefile.toml'] or hashlib.sha256((path/'lakefile.toml').read_bytes()).hexdigest() != selected['sha256']:
            raise SystemExit(f'Tracked dependency sources changed: {p["name"]}')
    packages.append({'name': p['name'], 'url': p['url'], 'rev': head})
provenance = json.loads((args.project / 'Y18_PROVENANCE.json').read_text())
external = []
runtime = json.loads(Path(os.environ['P0_CI_GUARD_STATE']).read_text())
lean_sources = Path(runtime['realbin']).parent / 'src/lean'
for module in sorted(set(provenance['target']['external_imports'] + json.loads((Path(__file__).parent/'ACTUAL_IMPORT_GRAPH.json').read_text())['true_other_external_modules'] + manifest['audit_external_imports'])):
    relative = Path(*module.split('.')).with_suffix('.lean')
    found = [(p['name'], args.project / lock['packagesDir'] / p['name'] / relative) for p in lock['packages']]
    found = [(name, path) for name, path in found if path.is_file()]
    if module == 'Lean' or module.startswith('Lean.') or module == 'Init' or module.startswith('Init.') or module == 'Std' or module.startswith('Std.'):
        path = lean_sources / relative
        if path.is_file():
            found.append(('leanprover/lean4:v4.33.0-rc1', path))
    if len(found) != 1:
        raise SystemExit(f'External module source is absent or ambiguous: {module}, matches={len(found)}')
    name, path = found[0]
    data = path.read_bytes()
    external.append({'module': module, 'package': name, 'sha256': hashlib.sha256(data).hexdigest(), 'bytes': len(data)})
binaries = {}
for name in ['lean', 'lake', 'leanchecker']:
    path = Path(runtime['realbin']) / name
    binaries[name] = {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()}
args.output.write_text(json.dumps({'packages': packages, 'external_direct_sources': external,
                                 'pinned_toolchain_binaries': binaries}, indent=2) + '\n')
