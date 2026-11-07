#!/usr/bin/env python3
"""Freeze text/hash/import evidence only. Never imports Lean or invokes a compiler."""
from pathlib import Path
import datetime, hashlib, json, re, subprocess
from collections import deque, Counter

ROOT = Path('/workspace/shared/chen-coordination/p1-coarse-policy')
OUT = Path('/workspace/shared/chen-coordination/p1-coarse-policy-evidence')
MODULE = 'ImbalancedChen.HistoricalThirdCoarsePolicy'
REL = Path('ImbalancedChen/HistoricalThirdCoarsePolicy.lean')
BASE = '08899a3f44fa61ea6dfe33d4cb557693cbac1590'
PROVIDERS = {
    'project': ROOT,
    'goldbach': Path('/workspace/shared/chen-coordination/source-dependencies/goldbach'),
    'LeanArchitect': Path('/workspace/shared/chen-coordination/source-dependencies/LeanArchitect'),
}

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def write(name, value):
    (OUT / name).write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

def mask_comments(src):
    out = list(src)
    depth, pos = 0, 0
    while pos < len(src):
        if src[pos:pos+2] == '/-':
            depth += 1
            out[pos:pos+2] = '  '
            pos += 2
        elif depth and src[pos:pos+2] == '-/':
            depth -= 1
            out[pos:pos+2] = '  '
            pos += 2
        elif depth:
            if src[pos] != '\n':
                out[pos] = ' '
            pos += 1
        elif src[pos:pos+2] == '--':
            while pos < len(src) and src[pos] != '\n':
                out[pos] = ' '
                pos += 1
        else:
            pos += 1
    assert depth == 0
    return ''.join(out)

def imports(src):
    return [token for row in re.findall(r'^\s*import ([^\n]+)', mask_comments(src), re.M)
            for token in row.split()]

raw = (ROOT / REL).read_bytes()
src = raw.decode()
masked = mask_comments(src)
snapshot = OUT / REL.name
snapshot.write_bytes(raw)
assert snapshot.read_bytes() == raw
decls = []
pattern = re.compile(r'^(private\s+)?(def|abbrev|theorem)\s+([A-Za-z0-9_]+)\b', re.M)
for match in pattern.finditer(masked):
    end = masked.find(':=', match.end())
    assert end > match.end()
    # Definitions ending in `where` are data constructors, so stop before `where`.
    where = masked.find(' where', match.end(), end)
    if where >= 0:
        end = where
    decls.append({'name': 'ImbalancedChen.HistoricalThirdCoarse.' + match.group(3),
                  'kind': match.group(2), 'private': bool(match.group(1)),
                  'line': src.count('\n', 0, match.start()) + 1,
                  'source_signature': src[match.start():end].strip()})
write('proposed-types.json', {'scope': 'Textual signatures only, not elaborated types or a complete kernel declaration inventory.', 'declarations': decls})

nodes, frontier, queue, paths = {}, set(), deque([(MODULE, [MODULE])]), {}
while queue:
    mod, chain = queue.popleft()
    if mod in nodes or mod in frontier:
        continue
    rel = Path(mod.replace('.', '/') + '.lean')
    found = next(((name, root / rel) for name, root in PROVIDERS.items() if (root / rel).is_file()), None)
    if not found:
        frontier.add(mod)
        continue
    provider, path = found
    data = path.read_bytes()
    deps = imports(data.decode())
    nodes[mod] = {'module': mod, 'provider': provider, 'path': str(rel),
                  'sha256': digest(data), 'bytes': len(data), 'imports': deps}
    paths[mod] = chain
    queue.extend((dep, chain + [dep]) for dep in deps)
heavy = [m for m in nodes if m.startswith('PrimeNumberTheoremAnd.') or 'Wiener' in m or 'ZetaBounds' in m]
assert not heavy, heavy
closure = {'scope': 'Static source import closure. Mathlib/Lean frontiers are pinned opaque dependencies, not newly audited objects.',
           'target': MODULE, 'provider_counts': dict(Counter(n['provider'] for n in nodes.values())),
           'nodes': [nodes[m] for m in sorted(nodes)], 'external_frontier': sorted(frontier),
           'unwanted_heavy_modules': heavy}
write('source-closure.json', closure)
pins = {name: digest((ROOT / name).read_bytes()) for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']}
manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
sources = {m: n['sha256'] for m, n in sorted(nodes.items())}
write('source-manifest.json', {'source_sha256': digest(raw), 'bytes': len(raw), 'line_count': len(src.splitlines()),
     'textual_declaration_count': len(decls), 'source_path': str(ROOT / REL), 'snapshot': str(snapshot),
     'baseline': BASE, 'source_import_closure_fingerprint': digest(json.dumps(sources, sort_keys=True).encode()),
     'pin_files_sha256': pins, 'package_revisions': {p['name']: p['rev'] for p in manifest['packages']}})
forbidden = re.findall(r'\b(?:sorry|axiom|unsafe|partial|native_decide)\b', masked)
assert not forbidden, forbidden
changed = subprocess.check_output(['git', '-C', str(ROOT), 'status', '--porcelain'], text=True).splitlines()
assert changed == ['?? ' + str(REL)], changed
write('static-checks.json', {'source_only': True, 'forbidden_tokens': forbidden, 'unwanted_heavy_modules': heavy,
     'worktree_changes': changed, 'snapshot_identical': True, 'public_root_unchanged': True,
     'no_lean_lake_checker_ci_install_commit_push': True,
     'not_claimed': ['elaboration', 'compilation', 'kernel replay', 'transitive axiom audit', 'full policy coverage', 'C3/C5 uniform approximation']})
print(json.dumps({'source_sha256': digest(raw), 'declarations': len(decls), 'provider_counts': closure['provider_counts'],
                  'heavy_modules': heavy, 'verification_level': 'SOURCE_ONLY'}))
