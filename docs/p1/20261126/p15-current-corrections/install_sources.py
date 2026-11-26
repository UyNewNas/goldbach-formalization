#!/usr/bin/env python3
"""Add only explicitly selected correction sources; never overwrite or write cache."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType

sys.dont_write_bytecode = True
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')
PREFIX = 'docs/p1/20261126/p15-current-corrections/'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def load_driver(commit):
    code = git_file(commit, PREFIX + 'run_selected.py')
    driver = ModuleType('published_current_corrections_driver')
    driver.__file__ = PREFIX + 'run_selected.py'
    exec(compile(code, driver.__file__, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT) and
            driver.RUNNER == PREFIX + 'run_selected.py' and len(driver.TARGETS) == 21,
            'unexpected installation environment or owner scope')
    return driver, driver.helpers(), code


def prepare(driver, s, commit, selected):
    selected = driver.selection(selected)
    require(Path(__file__).read_bytes() == git_file(commit, PREFIX + 'install_sources.py'),
            'executed installer differs from committed source')
    manifest, graph, sources, observed, binding = driver.source_manifest(s, commit, selected)
    active = s.h.closure(graph, selected)
    review = json.loads(driver.pinned(commit, driver.REVIEW, driver.REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        payload = git_file(commit, path)
        require({'bytes': len(payload), 'sha256': s.api.sha(payload)} == expected,
                'published configuration differs: ' + path)
    before = driver.environment(s, review)
    planned, identical = [], {}
    for module in sorted(active):
        path = PROJECT / s.h.module_path(module)
        require(path.parent == PROJECT / 'ImbalancedChen' and path.parent.resolve() == path.parent and
                not path.is_symlink(), 'unexpected source location: ' + str(path))
        payload = git_file(commit, s.h.module_path(module))
        require(s.api.sha(payload) == sources[module], 'published source payload differs')
        if os.path.lexists(path):
            require(path.is_file() and path.read_bytes() == payload,
                    'EXISTING_SOURCE_CONFLICT_NO_OVERWRITE: ' + module)
            identical[module] = {'bytes': len(payload), 'sha256': sources[module]}
        else:
            require(module in selected, 'NONSELECTED_DEPENDENCY_SOURCE_MISSING: ' + module)
            driver.require_fresh_owner(module, driver.module_artifacts(s, module))
            planned.append((module, path, payload))
    # Cache is observed, never opened for writing. Monitor the selected closure
    # and every whitelist target, including targets outside this invocation.
    artifacts = {module: driver.module_artifacts(s, module) for module in sorted(active | set(driver.TARGETS))}
    target_sources = {}
    for module in driver.TARGETS:
        path = PROJECT / s.h.module_path(module)
        target_sources[module] = None if not os.path.lexists(path) else {
            'bytes': path.stat().st_size, 'sha256': driver.file_binding(path)}
    return {'manifest': manifest, 'graph': graph, 'sources': sources, 'active': active, 'review': review,
            'binding': binding, 'before': before, 'planned': planned, 'identical': identical,
            'artifacts': artifacts, 'target_sources': target_sources, 'selected': selected}


def install(driver, s, commit, selected, run):
    s.d.verify_lane(s.h)
    spec = prepare(driver, s, commit, selected)
    plan = {'source_commit': commit, 'selected_targets': spec['selected'],
        'full_published_source_count': len(spec['graph']), 'selected_live_source_count': len(spec['active']),
        'committed_input_bindings': spec['binding'], 'existing_identical_sources': spec['identical'],
        'additions': [{'module': module, 'path': str(path), 'bytes': len(raw), 'sha256': s.api.sha(raw)}
                      for module, path, raw in spec['planned']],
        'context_before': spec['before'], 'cache_before': spec['artifacts'],
        'target_sources_before': spec['target_sources'], 'existing_source_overwrite_allowed': False,
        'cache_write_allowed': False, 'normal_or_kernel_execution_allowed': False}
    s.d.save(run / 'INSTALL_PLAN.json', plan)
    # All active sources have passed before the first write. Only None -> exact
    # committed payload is allowed; O_EXCL also refuses a concurrent new file.
    for module, path, payload in spec['planned']:
        require(path.parent.resolve() == path.parent, 'source parent changed before additive write')
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        with os.fdopen(descriptor, 'wb') as stream:
            stream.write(payload)
    graph, actual = s.h.project_graph(PROJECT, selected)
    require(graph == {module: spec['graph'][module] for module in spec['active']} and
            {module: row['sha256'] for module, row in actual.items()} ==
            {module: spec['sources'][module] for module in spec['active']}, 'post-install selected graph differs')
    after = driver.environment(s, spec['review'])
    require(after == spec['before'], 'runtime/configuration/protected root changed during source installation')
    artifacts = {module: driver.module_artifacts(s, module) for module in spec['artifacts']}
    require(artifacts == spec['artifacts'], 'cache changed during additive source installation')
    additions = {module for module, _, _ in spec['planned']}
    for module, expected in spec['target_sources'].items():
        if module not in additions:
            path = PROJECT / s.h.module_path(module)
            actual = None if not os.path.lexists(path) else {
                'bytes': path.stat().st_size, 'sha256': driver.file_binding(path)}
            require(actual == expected, 'an existing or unselected owner source changed')
    result = {'status': 'EXPLICIT_SELECTED_SOURCE_ADDITIONS_VERIFIED_NOT_COMPILED',
        'source_commit': commit, 'selected_targets': spec['selected'],
        'full_published_source_count': len(spec['graph']), 'selected_live_source_count': len(spec['active']),
        'added_modules': [module for module, _, _ in spec['planned']],
        'existing_identical_source_count': len(spec['identical']),
        'existing_sources_overwritten': 0, 'cache_mutations': 0, 'context_before': spec['before'],
        'context_after': after, 'whole_P1_complete': False, 'whole_P1_5_complete': False,
        'new_lean_acceptance': False}
    s.d.save(run / 'INSTALL_RESULT.json', result)
    s.ops.emit('P15_CURRENT_CORRECTION_SOURCES_INSTALLED', **result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--targets', nargs='+', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--install', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    require(re.fullmatch('[0-9a-f]{40}', commit), 'require a full source commit SHA')
    driver, s, code = load_driver(commit)
    selected = driver.selection(args.targets)
    if args.check:
        require(args.inside_lane is None, 'read-only installer check does not use a lane')
        spec = prepare(driver, s, commit, selected)
        print(json.dumps({'status': 'SELECTED_SOURCE_ADDITION_PLAN_CHECKED_NO_WRITES',
            'source_commit': commit, 'selected_targets': selected,
            'published_source_count': len(spec['graph']), 'selected_live_source_count': len(spec['active']),
            'planned_additions': [module for module, _, _ in spec['planned']],
            'existing_identical_source_count': len(spec['identical']), 'new_lean_acceptance': False}))
        return 0
    base = ROOT / commit / 'source-adoption'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name) and run.is_dir(),
                'invalid source installation worker path')
        install(driver, s, commit, selected, run)
        return 0
    prepare(driver, s, commit, selected)
    run = s.d.attempt(base)
    before = s.d.original_git_state(REPO)
    s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-installer.py'
    s.d.write_frozen(executed, Path(__file__).read_bytes())
    s.d.write_frozen(run / 'published-driver.py', code)
    try:
        command = s.ops.run(run, 'serialized-source-install',
            s.h.serialize(0, run / 'INSTALL_LANE.json',
                ['python3', '-B', str(executed), '--source-commit', commit, '--targets', *selected,
                 '--install', '--inside-lane', str(run)]), relay=True)
        require(command['exit_code'] == 0, 'additive source installation held or failed')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty Git metadata changed')
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    raise SystemExit(main())
