#!/usr/bin/env python3
"""Install an explicit P1.5 repair manifest using the existing serialized lane."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
import run_selected as runner

PREFIX = 'docs/p1/20261125/p15-actual-means/'


def worker(s, commit, manifest_path, run):
    s.d.verify_lane(s.h)
    raw = runner.git_file(commit, manifest_path)
    manifest = json.loads(raw)
    runner.require(manifest['schema'] == 'p15_explicit_source_repairs_v1', 'manifest schema differs')
    previous = manifest['failed_source_commit']
    runner.require(re.fullmatch('[0-9a-f]{40}', previous), 'invalid preimage commit')
    rows = manifest['repairs']
    selected = runner.selection([r['module'] for r in rows])
    runner.require([r['module'] for r in rows] == selected, 'manifest order differs')
    updates, payloads = [], {}
    for row in rows:
        path = s.h.module_path(row['module'])
        runner.require(row['path'] == path, 'repair path differs')
        before = runner.git_file(previous, path)
        after = runner.git_file(commit, path)
        runner.require(s.api.sha(before) == row['before_sha256'] and
                       s.api.sha(after) == row['after_sha256'] and before != after,
                       'repair preimage/payload differs: ' + path)
        payloads[path] = after
        updates.append({**row, 'cloud_source_mutation_required': True})
    s.api.preflight_sources(runner.PROJECT, updates, payloads, s.h)
    graph, actual = s.h.project_graph(runner.PROJECT, [runner.FIFTH, runner.FOURTH])
    runner.require(len(graph) == 304 and len(s.h.closure(graph, [runner.FOURTH])) == 252 and
                   s.h.closure(graph, [runner.FIFTH]) == set(graph) and
                   set(runner.TARGETS) <= set(graph),
                   'actual means closure differs')
    by_module = {r['module']: r for r in rows}
    for module in graph:
        payload = runner.git_file(commit, s.h.module_path(module))
        runner.require(graph[module] == [x for x in s.h.imports(payload)
                                        if x.startswith('ImbalancedChen.')],
                       'imports changed: ' + module)
        allowed = {s.api.sha(payload)}
        if module in by_module:
            allowed.add(by_module[module]['before_sha256'])
        runner.require(actual[module]['sha256'] in allowed, 'unexpected source: ' + module)
    review = json.loads(runner.pinned(commit, runner.REVIEW, runner.REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        payload = runner.git_file(commit, path)
        runner.require({'bytes': len(payload), 'sha256': s.api.sha(payload)} == expected,
                       'published configuration differs: ' + path)
    before = runner.snapshot(s, graph, review)
    s.d.save(run / 'CONTEXT_BEFORE.json', before)
    s.d.write_frozen(run / 'SOURCE_REPAIRS.json', raw)
    records = s.h.install_sources(runner.PROJECT, updates, payloads, run / 'source-backups')
    s.d.save(run / 'SOURCE_INSTALL.json', {'source_commit': commit, 'sources': records})
    _, _, _, after, _ = runner.preflight(s, commit, selected)
    s.d.save(run / 'CONTEXT_AFTER.json', after)
    expected = dict(before)
    expected['project_sources'] = {**before['project_sources'],
                                  **{r['module']: r['after_sha256'] for r in rows}}
    runner.require(after == expected, 'installation changed an unselected source/runtime')
    s.d.save(run / 'RESULT.json', {'status': 'EXACT_SOURCE_INSTALL_VERIFIED',
             'source_commit': commit, 'manifest': manifest_path,
             'modules': selected, 'mutated': [r['module'] for r in records if r['mutated']],
             'compilation_performed': False, 'whole_P1_complete': False})
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--manifest', required=True)
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    runner.require(re.fullmatch('[0-9a-f]{40}', commit), 'full source commit required')
    runner.require(re.fullmatch(PREFIX + r'round-[0-9]{2}/SOURCE_REPAIRS.json', args.manifest),
                   'manifest must be a versioned P1.5 repair')
    for name in ('run_selected.py', 'install_repairs.py'):
        runner.require((Path(__file__).parent / name).read_bytes() ==
                       runner.git_file(commit, PREFIX + name), 'driver differs from published commit')
    s = runner.helpers()
    base = runner.ROOT / 'source-installs' / commit
    if args.inside_lane:
        run = args.inside_lane.resolve()
        runner.require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name)
                       and run.is_dir(), 'invalid install directory')
        return worker(s, commit, args.manifest, run)
    run = s.d.attempt(base)
    before = s.d.original_git_state(runner.REPO)
    s.d.save(run / 'GIT_BEFORE.json', before)
    for name in ('run_selected.py', 'install_repairs.py'):
        s.d.write_frozen(run / name, (Path(__file__).parent / name).read_bytes())
    try:
        child = ['python3', '-B', str(run / 'install_repairs.py'), '--source-commit', commit,
                 '--manifest', args.manifest, '--inside-lane', str(run)]
        result = s.ops.run(run, 'source-install',
                          s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        runner.require(result['exit_code'] == 0, 'source installation failed; inspect retained evidence')
    finally:
        after = s.d.original_git_state(runner.REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        runner.require(after == before, 'original dirty Git state changed')
    print(json.dumps(s.api.read_json(run / 'RESULT.json')))
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
