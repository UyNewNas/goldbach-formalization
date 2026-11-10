"""Remote hash-only binding of all selected sources, data and compiled object parts."""
import argparse
import hashlib
import json
import os
from pathlib import Path

if os.getenv('GITHUB_ACTIONS') != 'true':
    raise SystemExit('Remote GitHub Actions evidence only')
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', type=Path, required=True)
p.add_argument('--manifest', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--compare', type=Path)
args = p.parse_args()
m = json.loads(args.manifest.read_text())


def digest(path):
    with path.open('rb') as f:
        return hashlib.file_digest(f, 'sha256').hexdigest()


sources = {}
for r in m['files'] + m['data_inputs']:
    path = args.project / r['install_path']
    h = digest(path)
    if h != r['sha256'] or path.stat().st_size != r['bytes']:
        raise SystemExit(f'Staged source/data changed: {path}')
    sources[r['install_path']] = h
parts = {}
for module in m['targets'][0]['closure_modules'] + ['T01Audit']:
    path = args.project / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    if not path.is_file() or path.stat().st_size == 0:
        raise SystemExit(f'Missing actual compiled object: {module}')
    parts[module] = {p.relative_to(args.project).as_posix(): digest(p)
                     for p in sorted([path, *path.parent.glob(path.name + '.*')]) if p.is_file()}
result = {'source_commit': os.environ['SOURCE_COMMIT'],
          'manifest_sha256': digest(args.manifest),
          'source_identity_sha256': m['targets'][0]['source_identity_sha256'],
          'staged_inputs_sha256': sources, 'object_parts_sha256': parts}
if args.compare and json.loads(args.compare.read_text()) != result:
    raise SystemExit('Inputs/objects changed across kernel and axiom checks')
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': 'PASS_EXACT_INPUT_AND_OBJECT_IDENTITY',
                  'input_count': len(sources), 'object_modules': len(parts)}))
