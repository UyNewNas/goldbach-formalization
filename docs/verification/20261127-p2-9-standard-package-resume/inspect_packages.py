"""Read-only standard package and preserved v4 runtime inspection. No Lean calls."""
from pathlib import Path
import base64, hashlib, json, os, subprocess, zlib

BASE = Path('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77')
V3 = BASE / 'verification-import-order-resume-v3'
V4 = BASE / 'verification-mathlib-path-resume-v4'
ROOT = BASE / 'project'

def stamp(p):
    s = p.stat()
    return [s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns]

def read_exact(p, include=True, limit=30000000):
    before = stamp(p)
    assert before[2] <= limit and p.is_file() and not p.is_symlink()
    data = p.read_bytes()
    assert stamp(p) == before
    row = {'path': str(p), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(), 'stat': before}
    if include:
        row['base64'] = base64.b64encode(data).decode()
    return row, data

report = {'schema': 'p29_all_standard_package_readonly_probe_v1', 'Lean_invocations': 0, 'filesystem_writes': 0, 'files': {}, 'packages': {}, 'source_view': {}}
names = ['FAILURE.json', 'mathlib-package-view-lean-path-process.json', 'mathlib-package-view-lean-path.log', 'omitted-direct-imports-process.json', 'omitted-direct-imports.log', 'ACTUAL_FIRST_NAMESPACE_PATHS.json', 'PACKAGE_VIEW_REPAIR.json', 'runtime-evidence/state.json', 'original-v3-runtime-stage-evidence/runtime-evidence/compiler-commands.jsonl']
for name in names:
    row, _ = read_exact(V4 / name, limit=1000000)
    report['files'][name] = row
for name in ['driver.py', 'INPUT_CONTRACT.json', 'SERVICE_OBSERVATION.json']:
    row, _ = read_exact(V4 / name, include=False, limit=1000000)
    report['files'][name] = row
state = json.loads(base64.b64decode(report['files']['runtime-evidence/state.json']['base64']))
row, _ = read_exact(Path(state['log']), limit=1000000)
report['live_guard_log'] = row
manifest_row, manifest_raw = read_exact(ROOT / 'lake-manifest.json', limit=1000000)
report['manifest'] = manifest_row
manifest = json.loads(manifest_raw)
assert len(manifest['packages']) == 10
for name in ['lean-toolchain', 'lakefile.toml']:
    row, _ = read_exact(ROOT / name, limit=1000000)
    report['source_view'][name] = row
link = ROOT / '.lake/packages'
report['package_view_link'] = {'path': str(link), 'is_symlink': link.is_symlink(), 'target': os.readlink(link) if link.is_symlink() else None}
derived = V3 / 'original-external-derived/P2_DECLARED_FACETS.jsonl'
derived_row, derived_raw = read_exact(derived, include=False)
assert derived_row['bytes'] == 23833463
assert derived_row['sha256'] == 'e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636'
report['original_derived_facet_table'] = derived_row
package_names = {p['name'] for p in manifest['packages']}
groups = {name: [] for name in package_names}
lemma_rows = []
count = 0
for line in derived_raw.splitlines():
    row = json.loads(line)
    count += 1
    module, facet = row['module'], row['facet']
    if module == 'Batteries.Tactic.Lemma':
        lemma_rows.append(row)
    relative = Path(module.replace('.', '/') + facet)
    path = Path(row['identity']['path'])
    assert path.parts[-len(relative.parts):] == relative.parts
    libroot = path.parents[len(relative.parts) - 1]
    if libroot.parts[-4:] != ('.lake', 'build', 'lib', 'lean'):
        continue
    package = libroot.parents[3]
    if package.name in groups:
        groups[package.name].append((row, package, path.relative_to(package)))
assert count == 55560
report['Batteries_Tactic_Lemma_original_rows'] = lemma_rows
for package in manifest['packages']:
    name = package['name']
    old = Path('/workspace/goldbach-p2/.lake/packages') / name
    alternative = Path('/workspace/compile-deps/mathlib') if name == 'mathlib' else Path('/workspace/compile-deps/mathlib/.lake/packages') / name
    roots = sorted({str(p) for _, p, _ in groups[name]})
    candidates = list(dict.fromkeys([str(old), str(alternative), *roots]))
    rec = {'manifest_revision': package['rev'], 'historical_facet_count': len(groups[name]), 'historical_roots': roots, 'candidates': []}
    for candidate in candidates:
        p = Path(candidate)
        entry = {'path': candidate, 'exists': p.exists(), 'is_symlink': p.is_symlink(), 'resolved': str(p.resolve()), 'git': {}, 'lib_exists': (p / '.lake/build/lib/lean').is_dir()}
        if p.is_dir():
            env = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
            for key, args in [('toplevel', ['rev-parse', '--show-toplevel']), ('HEAD', ['rev-parse', 'HEAD'])]:
                result = subprocess.run(['git', '-C', str(p), *args], capture_output=True, text=True, timeout=15, env=env)
                entry['git'][key] = {'exit_code': result.returncode, 'stdout': result.stdout.strip(), 'stderr': result.stderr.strip()[:1000]}
        present, missing = 0, []
        for original, original_root, rel in groups[name]:
            q = p / rel
            if q.is_file():
                present += 1
            elif len(missing) < 10:
                missing.append(str(q))
        entry['historical_facets_present_by_metadata'] = present
        entry['historical_facets_missing_by_metadata'] = len(groups[name]) - present
        entry['first_missing_paths'] = missing
        if name == 'batteries':
            entry['lemma_facets'] = []
            for original in lemma_rows:
                q = p / '.lake/build/lib/lean' / ('Batteries/Tactic/Lemma' + original['facet'])
                if q.is_file() and not q.is_symlink():
                    pin, _ = read_exact(q, include=False)
                    pin['equals_original_bytes_and_sha256'] = pin['bytes'] == original['identity']['bytes'] and pin['sha256'] == original['identity']['sha256']
                    pin['equals_original_resolved_path'] = q.resolve() == Path(original['identity']['path']).resolve()
                    entry['lemma_facets'].append(pin)
        rec['candidates'].append(entry)
    report['packages'][name] = rec
report['interpretation'] = 'Metadata inventory and exact Lemma facet comparison only. Does not replace the actual downstream Lean import/header/facet binding.'
raw = json.dumps(report, sort_keys=True, separators=(',', ':')).encode()
print('P29_PACKAGE_PROBE ' + base64.b64encode(zlib.compress(raw, 9)).decode())
