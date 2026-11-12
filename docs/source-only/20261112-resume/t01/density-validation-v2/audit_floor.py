"""Remote-only fail-closed nine-declaration type and transitive-axiom receipt."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re

if os.getenv('GITHUB_ACTIONS') != 'true':
    raise SystemExit('Remote GitHub Actions output only')
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--project', type=Path, required=True)
p.add_argument('--log', type=Path, required=True)
p.add_argument('--manifest', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
args = p.parse_args()
prov = json.loads((args.project / 'DENSITY_PROVENANCE.json').read_text())
manifest_raw = args.manifest.read_bytes()
if hashlib.sha256(manifest_raw).hexdigest() != prov['manifest_sha256']:
    raise SystemExit('Floor audit manifest differs from actual staged provenance')
manifest = json.loads(manifest_raw)
raw = args.log.read_bytes()
text = raw.decode('utf-8')
prefix = 'T01_FIFTH_DECL '
records = [json.loads(line[len(prefix):]) for line in text.splitlines() if line.startswith(prefix)]
expected = manifest['floor_target']['declarations']
if len(records) != len(expected) or len({r['name'] for r in records}) != len(expected):
    raise SystemExit('Missing or duplicate compiler type records')
if {r['name'] for r in records} != set(expected):
    raise SystemExit('Unexpected compiler declarations')
if [line for line in text.splitlines() if line.startswith('T01_FIFTH_COUNT ')] != [f'T01_FIFTH_COUNT {len(expected)}']:
    raise SystemExit('Missing exact compiler census')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for r in records:
    if r['kind'] != 'theorem' or r['module'] != manifest['floor_target']['declaration_modules'][r['name']]:
        raise SystemExit(f'Wrong declaration kind or defining module: {r["name"]}')
    if set(r['axioms']) - allowed:
        raise SystemExit(f'Forbidden transitive axioms: {r["name"]}')
    for key in ['type', 'readable_type']:
        if not isinstance(r[key], str) or not r[key].strip() or any(x in r[key] for x in ['⋯', '…']):
            raise SystemExit(f'Missing or elided {key}: {r["name"]}')
    name = re.escape(r['name'])
    deps = re.findall(r"['\"]?" + name + r"['\"]?\s+depends on axioms:\s*\[([^\]]*)\]", text)
    none = re.findall(r"['\"]?" + name + r"['\"]?\s+does not depend on any axioms", text)
    if len(deps) + len(none) != 1:
        raise SystemExit(f'Missing or duplicate #print axioms: {r["name"]}')
    printed = {s.strip() for s in deps[0].split(',') if s.strip()} if deps else set()
    if printed != set(r['axioms']):
        raise SystemExit(f'Independent axiom reports differ: {r["name"]}')
result = {'status': 'PASS_EXACT_NINE_FULL_TYPES_AND_TRANSITIVE_AXIOMS',
          'manifest_sha256': prov['manifest_sha256'], 'source_commit': prov['source_commit'],
          'source_identity_sha256': prov['source_identity_sha256'],
          'log_sha256': hashlib.sha256(raw).hexdigest(), 'allowed_axioms': sorted(allowed),
          'targets': records, 'green_requires_independent_expanded_type_acceptance': True}
if args.output.resolve().is_relative_to(args.project.resolve()) or args.output.exists():
    raise SystemExit('Require a new floor receipt outside the physical source census')
args.output.write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status': result['status'], 'targets': len(records)}, indent=2))
