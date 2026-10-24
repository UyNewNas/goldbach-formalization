#!/usr/bin/env python3
"""Read-only source coverage inventory. Never runs Lean or changes proof sources."""
from __future__ import annotations
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASELINE = '368736567624353986efd3b6d6c5ccef97e8b535'
MANIFEST = 'docs/source-only/20261024-code-only/batch4/source-manifest.json'
CENSUS_ARCHIVE = 'docs/evidence/owned-frontiers/20261024-after260-next6-v1/archive-manifest.json'


def strip_comments_and_strings(text: str) -> str:
    """Blank comments/string contents, including nested block comments; keep lines."""
    result = []
    pos = 0
    depth = 0
    while pos < len(text):
        if depth:
            if text.startswith('/-', pos):
                depth += 1
                pos += 2
            elif text.startswith('-/', pos):
                depth -= 1
                pos += 2
            else:
                if text[pos] == '\n':
                    result.append('\n')
                pos += 1
        elif text.startswith('/-', pos):
            result.append(' ')
            depth = 1
            pos += 2
        elif text.startswith('--', pos):
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        elif text[pos] == '"':
            result.append(' ')
            pos += 1
            while pos < len(text):
                char = text[pos]
                pos += 1
                if char == '\\' and pos < len(text):
                    if text[pos] == '\n':
                        result.append('\n')
                    pos += 1
                elif char == '"':
                    break
                elif char == '\n':
                    result.append('\n')
        else:
            result.append(text[pos])
            pos += 1
    return ''.join(result)


def parse_imports(text: str) -> list[str]:
    imports = []
    for line in strip_comments_and_strings(text).splitlines():
        match = re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+)', line)
        if match:
            imports.extend(match.group(1).split())
    return imports


def closure(roots: set[str], graph: dict[str, list[str]]) -> set[str]:
    seen: set[str] = set()
    todo = list(roots)
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        todo.extend(dep for dep in graph.get(module, []) if dep in graph)
    return seen


def disposition(path: str) -> str:
    if path.endswith('.lean'):
        if path == 'ImbalancedChen.lean' or path.startswith('ImbalancedChen/'):
            return 'production_library_compile_independent_target'
        if path.startswith('docs/evidence/'):
            return 'historical_external_source_evidence_do_not_compile_automatically'
        markers = ('/snapshot-sources/', '/source-snapshot/', '/history/', '/attempts/',
                   '/proof-continuation/2026-10-15/', '/round5/', '/long-slot-normalization/')
        if any(marker in '/' + path for marker in markers):
            return 'historical_verification_evidence_do_not_compile_automatically'
        if '/queue/' in path:
            return 'verification_template_do_not_compile_automatically'
        return 'verification_program_use_its_documented_runner'
    if path.startswith(('docs/evidence/', 'docs/source-only/')):
        return 'archived_evidence_preserve_bytes_not_compilation_input'
    if path.startswith('verification/'):
        return 'verification_support_or_evidence_not_lean_module'
    if path.startswith(('.github/', 'automation/')):
        return 'automation_or_ci_configuration_not_lean_module'
    if path.startswith('docs/') or path.endswith('.md'):
        return 'documentation_not_lean_module'
    return 'repository_configuration_or_other_asset_not_lean_module'


class Repository:
    def __init__(self, root: Path, revision: str | None = None):
        self.root = root
        self.revision = revision

    def git(self, *args: str) -> bytes:
        return subprocess.check_output(['git', '-C', str(self.root), *args])

    def paths(self) -> list[str]:
        args = ('ls-tree', '-rz', '--name-only', self.revision) if self.revision else ('ls-files', '-z')
        return sorted(set(self.git(*args).decode().rstrip('\0').split('\0')) - {''})

    def read(self, path: str) -> bytes:
        if self.revision:
            return self.git('show', f'{self.revision}:{path}')
        return (self.root / path).read_bytes()


def inventory(repo: Repository) -> dict:
    manifest = json.loads(repo.read(MANIFEST))
    records = {row['path'].replace('\\', '/'): row for row in manifest['records']}
    archive = json.loads(repo.read(CENSUS_ARCHIVE))
    census_sha = archive['roles']['current_census']['sha256']
    census_payload = next(row for row in archive['payloads'] if row['sha256'] == census_sha)
    census_path = str(Path(CENSUS_ARCHIVE).parent / census_payload['stored_path'])
    census_bytes = repo.read(census_path)
    if hashlib.sha256(census_bytes).hexdigest() != census_sha:
        raise ValueError('Archived ROOT266 census hash mismatch')
    census = json.loads(census_bytes)
    accepted = set(census['modules'])
    files = []
    for path in repo.paths():
        row = {'path': path, 'disposition': disposition(path), 'module': None,
               'batch711_member': path in records, 'census266_member': False}
        try:
            data = repo.read(path)
        except FileNotFoundError:
            row.update(exists=False, sha256=None, bytes=None)
            files.append(row)
            continue
        row.update(exists=True, sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
        if path.endswith('.lean'):
            row['imports'] = parse_imports(data.decode('utf-8-sig'))
            if row['disposition'] == 'production_library_compile_independent_target':
                row['module'] = path[:-5].replace('/', '.')
                row['census266_member'] = row['module'] in accepted
        files.append(row)
    graph = {row['module']: row['imports'] for row in files if row['module']}
    root = closure({'ImbalancedChen'}, graph)
    continuation = closure({'ImbalancedChen.UncompiledContinuation'}, graph)
    batch_modules = {path[:-5].replace('/', '.') for path in records}
    batch_closure = closure(batch_modules, graph)
    census_closure = closure(accepted, graph)
    missing = []
    by_path = {row['path']: row for row in files}
    for row in files:
        row['root_reachable'] = row['module'] in root
        row['continuation_reachable'] = row['module'] in continuation
        for dep in row.get('imports', []):
            if dep.startswith('ImbalancedChen') and dep not in graph:
                missing.append({'source': row['path'], 'import': dep})
        if row['path'] in records:
            original = records[row['path']]['sha256']
            row['batch_original_sha256'] = original
            row['batch_hash_status'] = ('missing' if not row['exists'] else
                                        'unchanged' if original == row['sha256'] else 'changed')
    batch_missing = sorted(path for path in records if path not in by_path or not by_path[path]['exists'])
    changed = [{'path': path, 'original_sha256': records[path]['sha256'],
                'current_sha256': by_path[path]['sha256']} for path in records
               if path in by_path and by_path[path]['exists'] and records[path]['sha256'] != by_path[path]['sha256']]
    hashes: dict[str, list[str]] = {}
    for row in files:
        if row['path'].endswith('.lean') and row['exists']:
            hashes.setdefault(row['sha256'], []).append(row['path'])
    return {
        'schema': 1, 'head': repo.git('rev-parse', repo.revision or 'HEAD').decode().strip(),
        'read_mode': 'git_revision' if repo.revision else 'tracked_worktree_files',
        'historical_source_baseline': BASELINE, 'source_manifest': MANIFEST,
        'census_source': census_path, 'census_status': census.get('status'),
        'compilation_performed': False,
        'counts': {'tracked_files': len(files), 'lean_files': sum(r['path'].endswith('.lean') for r in files),
                   'library_modules': len(graph), 'external_lean_files': sum(r['path'].endswith('.lean') and not r['module'] for r in files),
                   'root_closure': len(root), 'continuation_closure': len(continuation),
                   'root_continuation_union': len(root | continuation),
                   'outside_root_continuation': len(set(graph) - root - continuation),
                   'batch711': len(records), 'batch_closure': len(batch_closure),
                   'census266': len(accepted), 'census_closure': len(census_closure)},
        'disposition_counts': dict(Counter(r['disposition'] for r in files)),
        'targets': sorted(graph), 'root_closure': sorted(root),
        'continuation_closure': sorted(continuation),
        'outside_root_continuation': sorted(set(graph) - root - continuation),
        'batch_outside_root_continuation': sorted(batch_modules - root - continuation),
        'census_outside_root_continuation': sorted(accepted - root - continuation),
        'outside_root_batch_census': sorted(set(graph) - root - batch_closure - census_closure),
        'missing_local_imports': missing, 'missing_batch_paths': batch_missing,
        'missing_tracked_paths': [row['path'] for row in files if not row['exists']],
        'changed_batch_hashes': changed,
        'duplicate_lean_byte_groups': [group for group in hashes.values() if len(group) > 1],
        'files': files,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--revision', help='Read exact Git revision instead of tracked worktree bytes')
    parser.add_argument('--targets', action='store_true', help='Print individual production module targets, one per line')
    parser.add_argument('--output', type=Path, help='Write complete JSON inventory')
    args = parser.parse_args()
    report = inventory(Repository(args.repo, args.revision))
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + '\n')
    if args.targets:
        print('\n'.join(report['targets']))
    elif not args.output:
        print(json.dumps(report, indent=2))
    # Edited proof sources are expected during repair. Record, do not reject them.
    if report['missing_local_imports'] or report['missing_batch_paths'] or report['missing_tracked_paths']:
        print('Inventory found missing project imports or tracked/submitted paths; inspect JSON.', file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
