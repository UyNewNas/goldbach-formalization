#!/usr/bin/env python3
"""Plan dependency-ordered warm-build shards; never compile or replace final gates.

Shards are 1-based and must run strictly sequentially. All targets must still be
validated by the final full build. This tool records source identity, not proof
acceptance. Worktree inventories identify both HEAD and actual per-file bytes.
"""
from __future__ import annotations

import argparse
import hashlib
import heapq
import json
from pathlib import Path
import re
import sys

from full_source_inventory import Repository, inventory

PRODUCTION = 'production_library_compile_independent_target'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def ready_key(module: str) -> tuple[bool, str]:
    # Defer umbrella entrypoints when possible without violating dependencies.
    return (module == 'ImbalancedChen' or module.startswith('ImbalancedChen.UncompiledContinuation'), module)


def make_manifest(source: dict, count: int = 4) -> dict:
    require(type(count) is int and count > 0, 'shard count must be a positive integer')
    require(isinstance(source, dict), 'inventory must be an object')
    require(isinstance(source.get('head'), str) and re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', source['head']) is not None,
            'inventory head must be a full Git object ID')
    require(source.get('read_mode') in ('git_revision', 'tracked_worktree_files'), 'missing or invalid inventory read mode')
    targets = source.get('targets')
    require(isinstance(targets, list) and bool(targets) and all(isinstance(t, str) and t for t in targets),
            'inventory targets must be a nonempty string list')
    require(len(targets) == len(set(targets)), 'duplicate inventory target')
    require(count <= len(targets), 'shard count cannot exceed target count')
    for key in ('missing_local_imports', 'missing_batch_paths', 'missing_tracked_paths'):
        require(key in source and source[key] == [], f'inventory reports missing inputs or lacks {key}')
    files = source.get('files')
    require(isinstance(files, list) and bool(files), 'inventory files must be a nonempty list')
    paths: set[str] = set()
    module_rows: dict[str, dict] = {}
    file_hashes = []
    for row in files:
        require(isinstance(row, dict), 'malformed file record')
        path = row.get('path')
        require(isinstance(path, str) and bool(path) and path not in paths, 'missing or duplicate file path')
        paths.add(path)
        require(row.get('exists') is True, f'missing file: {path}')
        sha = row.get('sha256')
        require(isinstance(sha, str) and re.fullmatch(r'[0-9a-f]{64}', sha) is not None, f'invalid SHA-256: {path}')
        require(type(row.get('bytes')) is int and row['bytes'] >= 0, f'invalid file size: {path}')
        file_hashes.append({'path': path, 'sha256': sha, 'bytes': row['bytes']})
        module = row.get('module')
        if row.get('disposition') == PRODUCTION:
            require(isinstance(module, str) and module not in module_rows, f'missing or duplicate module: {path}')
            require(path == module.replace('.', '/') + '.lean', f'module/path mismatch: {path}')
            require(module == 'ImbalancedChen' or module.startswith('ImbalancedChen.'), f'nonproject production module: {module}')
            require(isinstance(row.get('imports'), list) and all(isinstance(i, str) and i for i in row['imports']),
                    f'invalid imports: {module}')
            module_rows[module] = row
        else:
            require(module is None, f'nonproduction record claims module: {path}')
    require(set(module_rows) == set(targets), 'target list must equal all production file modules')
    require(isinstance(source.get('counts'), dict) and source['counts'].get('library_modules') == len(targets),
            'inventory library count mismatch')
    graph = {}
    for module, row in module_rows.items():
        local = {i for i in row['imports'] if i == 'ImbalancedChen' or i.startswith('ImbalancedChen.')}
        require(local <= set(module_rows), f'missing project dependency for {module}: {sorted(local - set(module_rows))}')
        graph[module] = local
    pending = {module: len(deps) for module, deps in graph.items()}
    users: dict[str, list[str]] = {module: [] for module in graph}
    for module, deps in graph.items():
        for dep in deps:
            users[dep].append(module)
    ready = [ready_key(m) for m in graph if pending[m] == 0]
    heapq.heapify(ready)
    order = []
    while ready:
        _, module = heapq.heappop(ready)
        order.append(module)
        for user in sorted(users[module]):
            pending[user] -= 1
            if pending[user] == 0:
                heapq.heappush(ready, ready_key(user))
    require(len(order) == len(graph), f'project import cycle: {sorted(m for m, n in pending.items() if n)}')
    quotient, remainder = divmod(len(order), count)
    shards = []
    offset = 0
    for index in range(1, count + 1):
        size = quotient + (index <= remainder)
        chunk = order[offset:offset + size]
        shards.append({'index': index, 'start_offset': offset, 'end_offset_exclusive': offset + size,
                       'target_count': size, 'targets': chunk})
        offset += size
    flattened = [m for shard in shards for m in shard['targets']]
    require(flattened == order and len(set(flattened)) == len(targets) and set(flattened) == set(targets),
            'shard partition must be a disjoint exhaustive union')
    positions = {m: i for i, m in enumerate(order)}
    assignments = {m: shard['index'] for shard in shards for m in shard['targets']}
    edges = []
    for importer in sorted(graph):
        for dependency in sorted(graph[importer]):
            require(positions[dependency] < positions[importer], 'invalid dependency order')
            require(assignments[dependency] <= assignments[importer], 'dependency assigned to later shard')
            edges.append({'dependency': dependency, 'importer': importer,
                          'dependency_position': positions[dependency], 'importer_position': positions[importer],
                          'dependency_shard': assignments[dependency], 'importer_shard': assignments[importer]})
    file_hashes.sort(key=lambda row: row['path'])
    identity = {'head': source['head'], 'read_mode': source['read_mode'], 'files': file_hashes}
    return {
        'schema': 1, 'purpose': 'strictly_sequential_warm_build_only',
        'final_full_build_and_existing_gates_required': True, 'compilation_performed': False,
        'source_head': source['head'], 'source_read_mode': source['read_mode'],
        'source_identity_sha256': hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(',', ':')).encode()).hexdigest(),
        'source_files': file_hashes, 'target_count': len(order), 'shard_count': count,
        'all_targets': sorted(targets), 'topological_order': order, 'shards': shards,
        'dependency_order_evidence': {'edge_count': len(edges), 'all_dependencies_before_importers': True,
                                      'no_dependency_in_later_shard': True, 'edges': edges},
        'partition_evidence': {'disjoint': True, 'exhaustive': True, 'contiguous_topological_chunks': True,
                               'largest_smallest_size_difference': int(bool(remainder))},
    }


def select_targets(manifest: dict, index: int) -> list[str]:
    require(type(index) is int and 1 <= index <= manifest['shard_count'], 'shard index must be in 1..shard_count')
    return manifest['shards'][index - 1]['targets']


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', type=Path, help='Use existing full_source_inventory JSON')
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--revision', help='Read exact Git revision; not usable with --inventory')
    parser.add_argument('--count', type=int, default=4)
    parser.add_argument('--shard-index', type=int, help='Selected shard, 1-based')
    parser.add_argument('--targets', action='store_true', help='Print selected shard module targets, one per line')
    parser.add_argument('--output', type=Path, help='Write complete deterministic shard manifest JSON')
    args = parser.parse_args()
    if args.inventory and args.revision:
        parser.error('--inventory and --revision are mutually exclusive')
    if args.targets and args.shard_index is None:
        parser.error('--targets requires --shard-index')
    try:
        source = json.loads(args.inventory.read_text()) if args.inventory else inventory(Repository(args.repo, args.revision))
        manifest = make_manifest(source, args.count)
        selected = select_targets(manifest, args.shard_index) if args.shard_index is not None else None
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(manifest, indent=2) + '\n')
        if args.targets:
            print('\n'.join(selected))
        elif not args.output:
            print(json.dumps(manifest, indent=2))
        return 0
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(f'Shard planning failed: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    raise SystemExit(main())
