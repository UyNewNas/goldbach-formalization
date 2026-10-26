#!/usr/bin/env python3
"""Verify/stage only exact pinned Wu research sources needed by production imports.

No Lean/Lake process, fetch, pin change, or compiled-artifact copy is performed.
Default audit requires destinations already present; --stage creates missing files
only after the entire graph, origins and existing destinations have been verified.
"""
from __future__ import annotations
import argparse, hashlib, json, os, subprocess, re
from pathlib import Path
from full_source_inventory import strip_comments_and_strings

GOLDBACH_PIN = '09b97db5764ade1246bfb77206baa1b124760958'
RESEARCH = Path('research/wu2008/src')
PRODUCTION_TARGET_COUNT = 1358

def parse_imports(text):
    result = []
    for line in strip_comments_and_strings(text).splitlines():
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)', line)
        if match:
            result.extend(match.group(1).split())
    return result

class AuditError(ValueError):
    pass

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def blob_id(data):
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()

def blob_map(root, revision):
    rows = git(root, 'ls-tree', '-r', revision).splitlines()
    return {line.split('\t', 1)[1]: line.split()[2] for line in rows if line.split()[1] == 'blob'}

def checked_bytes(path, expected_blob):
    if path.is_symlink():
        raise AuditError(f'Symlink source is not accepted: {path}')
    data = path.read_bytes()
    if blob_id(data) != expected_blob:
        raise AuditError(f'Pinned source bytes differ: {path}')
    return data

def acyclic(graph):
    active, done = set(), set()
    def visit(node):
        if node in active:
            raise AuditError(f'Import cycle at {node}')
        if node in done:
            return
        active.add(node)
        for dep in graph.get(node, []):
            if dep in graph:
                visit(dep)
        active.remove(node); done.add(node)
    for node in graph:
        visit(node)

def stage_verified(rows, root, stage):
    # Complete preflight before creating any destination, including later rows.
    for row in rows:
        origin, dest = root / row['origin_path'], root / row['destination_path']
        data = checked_bytes(origin, row['origin_git_blob'])
        if digest(data) != row['sha256']:
            raise AuditError(f'Origin changed since graph audit: {origin}')
        if any(parent.is_symlink() for parent in dest.parents if parent != root and root in parent.parents):
            raise AuditError(f'Symlink destination parent: {dest}')
        if dest.is_symlink() or (dest.exists() and dest.read_bytes() != data):
            raise AuditError(f'Existing destination differs: {dest}')
        if not dest.exists() and not stage:
            raise AuditError(f'Required pinned source is not staged: {dest}')
    for row in rows:
        origin, dest = root / row['origin_path'], root / row['destination_path']
        if not dest.exists():
            dest.parent.mkdir(parents=True, exist_ok=True)
            # Exclusive create: a concurrent write is never overwritten.
            with dest.open('xb') as stream:
                stream.write(checked_bytes(origin, row['origin_git_blob']))
        if digest(dest.read_bytes()) != row['sha256']:
            raise AuditError(f'Staged bytes failed verification: {dest}')
        row['destination_exists'] = True

def verify(root: Path, *, stage=False, toolchain_source: Path | None = None):
    root = root.resolve()
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    packages = []
    for entry in manifest['packages']:
        if entry['type'] != 'git':
            raise AuditError('Only pinned Git dependencies are supported')
        path = root / manifest['packagesDir'] / entry['name']
        head = git(path, 'rev-parse', 'HEAD')
        if head != entry['rev']:
            raise AuditError(f"Pin mismatch: {entry['name']}")
        if git(path, 'diff', 'HEAD', '--name-only'):
            raise AuditError(f"Tracked dependency changes: {entry['name']}")
        if entry['name'] == 'goldbach' and head != GOLDBACH_PIN:
            raise AuditError('Unsupported goldbach research provenance pin')
        packages.append((entry['name'], path, head, blob_map(path, head)))
    gold = [x for x in packages if x[0] == 'goldbach']
    if len(gold) != 1:
        raise AuditError('Exactly one pinned goldbach package is required')
    _, goldroot, _, goldblobs = gold[0]
    paths = git(root, 'ls-files').splitlines()
    production = {p[:-5].replace('/', '.'): root / p for p in paths
                  if p.endswith('.lean') and (p == 'ImbalancedChen.lean' or p.startswith('ImbalancedChen/'))}
    if len(production) != PRODUCTION_TARGET_COUNT:
        raise AuditError(f'Official production scope changed: {len(production)}')
    if toolchain_source is None:
        pin = (root / 'lean-toolchain').read_text().strip()
        toolchain_source = Path(os.environ.get('ELAN_HOME', str(Path.home()/'.elan'))) / 'toolchains' / pin.replace('/', '--').replace(':', '---') / 'src/lean'
    graph, sources, staged, core = {}, {}, {}, {}
    pending = list(production)
    while pending:
        module = pending.pop()
        if module in graph or module in core:
            continue
        if not all(part and part.replace('_', '').isalnum() for part in module.split('.')):
            raise AuditError(f'Unsupported module identifier: {module}')
        rel = Path(module.replace('.', '/') + '.lean')
        if module in production:
            path = production[module]; data = path.read_bytes(); origin_blob = None
        else:
            candidates = [(p / rel, blobs[rel.as_posix()]) for _, p, _, blobs in packages if rel.as_posix() in blobs]
            if len(candidates) > 1:
                raise AuditError(f'Ambiguous package module: {module}')
            allowed_paths = {p for p, _ in candidates}
            if (RESEARCH / rel).as_posix() in goldblobs:
                allowed_paths.add(goldroot / rel)
            for _, package_root, _, _ in packages:
                unexpected = package_root / rel
                if unexpected.exists() and unexpected not in allowed_paths:
                    raise AuditError(f'Unverified package source shadows module: {unexpected}')
            if candidates:
                path, origin_blob = candidates[0]; data = checked_bytes(path, origin_blob)
            elif (RESEARCH / rel).as_posix() in goldblobs:
                path = goldroot / RESEARCH / rel; origin_blob = goldblobs[(RESEARCH / rel).as_posix()]
                data = checked_bytes(path, origin_blob)
                destination = goldroot / rel
                staged[module] = {'module': module, 'origin_path': str(path.relative_to(root)),
                    'destination_path': str(destination.relative_to(root)), 'sha256': digest(data),
                    'origin_git_blob': origin_blob, 'destination_exists': destination.exists()}
            else:
                # Core sources are toolchain leaves, never research substitutions.
                cp = toolchain_source / rel
                if module.split('.')[0] == 'Lake':
                    cp = toolchain_source / 'lake' / rel
                if module.split('.')[0] not in {'Init', 'Lean', 'Std', 'Lake'} or not cp.is_file():
                    raise AuditError(f'Unknown required module: {module}')
                core[module] = {'path': str(cp), 'sha256': digest(cp.read_bytes())}
                continue
        imports = parse_imports(data.decode('utf-8-sig'))
        graph[module] = imports
        sources[module] = {'path': str(path.relative_to(root)), 'sha256': digest(data),
            'origin_git_blob': origin_blob, 'imports': imports}
        pending.extend(imports)
    acyclic(graph)
    rows = [staged[m] for m in sorted(staged)]
    for row in sources.values():
        if digest((root / row['path']).read_bytes()) != row['sha256']:
            raise AuditError(f"Source changed during graph audit: {row['path']}")
    stage_verified(rows, root, stage)
    return {'schema': 1, 'status': 'passed', 'scope': 'SOURCE_PROVENANCE_NOT_COMPILATION_ACCEPTANCE',
        'head': git(root, 'rev-parse', 'HEAD'), 'manifest_sha256': digest((root/'lake-manifest.json').read_bytes()),
        'production_target_count': len(production), 'production_targets': sorted(production),
        'packages': [{'name': n, 'head': h} for n, _, h, _ in packages],
        'required_sources': sources, 'toolchain_source_leaves': core, 'required_graph_acyclic': True,
        'staged_sources': rows, 'staged_source_count': len(rows)}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--stage', action='store_true')
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--root', type=Path, default=Path.cwd())
    args = parser.parse_args()
    try:
        result = verify(args.root, stage=args.stage)
    except (AuditError, OSError, subprocess.CalledProcessError) as error:
        result = {'schema': 1, 'status': 'failed', 'error': str(error)}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    return 0 if result['status'] == 'passed' else 1

if __name__ == '__main__':
    raise SystemExit(main())
