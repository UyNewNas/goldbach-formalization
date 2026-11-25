#!/usr/bin/env python3
"""Add the 25 selected source files without changing existing sources or caches."""
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
ROOT = Path('/workspace/p1-complete-proof/20261125-p15-singleton-proper-power-v1')
PREFIX = 'docs/p1/20261125/p15-singleton-proper-power/'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def load_driver(commit):
    code = git_file(commit, PREFIX + 'run_selected.py')
    driver = ModuleType('published_p15_singleton_driver')
    driver.__file__ = PREFIX + 'run_selected.py'
    exec(compile(code, driver.__file__, 'exec'), driver.__dict__)
    require((driver.REPO, driver.PROJECT, driver.ROOT) == (REPO, PROJECT, ROOT),
            'unexpected installation environment')
    return driver, driver.helpers(), code


def context(driver, s, review):
    observed = {p: s.d.fingerprint(PROJECT / p)
                for p in review['runtime_configuration_bindings']}
    require(observed == review['runtime_configuration_bindings'] and
            not os.path.lexists(PROJECT / 'lakefile.lean'), 'existing configuration differs')
    runtime = s.d.runtime_binding(s.h)
    require(runtime == review['existing_runtime_bindings'], 'existing runtime differs')
    protected = {m: driver.file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    require(protected == s.h.FOUR_ROOTS, 'protected root differs')
    return {'configuration': observed, 'runtime': runtime, 'protected_roots': protected}


def install(driver, s, commit, run):
    s.d.verify_lane(s.h)
    manifest, graph, sources, binding = driver.source_manifest(s, commit, list(driver.TARGETS))
    suppliers, _, reuse_binding = driver.reuse_manifest(s, commit, graph, sources)
    allowed = set(driver.TARGETS) | set(suppliers)
    require(len(allowed) == 25, 'source installation scope differs')
    review = json.loads(driver.pinned(commit, driver.REVIEW, driver.REVIEW_SHA))
    for path, expected in review['source_configuration_bindings'].items():
        raw = git_file(commit, path)
        require({'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()} == expected,
                'published configuration differs')
    before = context(driver, s, review)
    planned = []
    existing = {}
    for module in sorted(graph):
        path = PROJECT / s.h.module_path(module)
        require(path.parent.resolve() == (PROJECT / 'ImbalancedChen').resolve() and
                not path.parent.is_symlink() and not path.is_symlink(), 'unexpected source location')
        raw = git_file(commit, s.h.module_path(module))
        require(hashlib.sha256(raw).hexdigest() == sources[module], 'published payload differs')
        if path.exists():
            require(path.is_file() and path.read_bytes() == raw,
                    'EXISTING_SOURCE_CONFLICT_NO_OVERWRITE: ' + module)
            existing[module] = {'bytes': len(raw), 'sha256': sources[module]}
        else:
            require(module in allowed, 'EXISTING_DEPENDENCY_SOURCE_MISSING: ' + module)
            planned.append((module, path, raw))
    # Check every source before the first additive write. Cache files are never
    # created, removed or changed by this installer.
    s.d.save(run / 'INSTALL_PLAN.json', {
        'source_commit': commit, 'closure': binding, 'p3_reuse': reuse_binding,
        'allowed_modules': sorted(allowed), 'existing_identical_sources': existing,
        'additions': [{'module': m, 'path': str(p), 'bytes': len(b), 'sha256': sources[m]}
                      for m, p, b in planned], 'context_before': before})
    for module, path, raw in planned:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
        with os.fdopen(descriptor, 'wb') as out:
            out.write(raw)
    actual_graph, actual = s.h.project_graph(PROJECT, manifest['targets'])
    require(actual_graph == graph and {m: v['sha256'] for m, v in actual.items()} == sources,
            'post-install source graph differs')
    after = context(driver, s, review)
    require(after == before, 'runtime/configuration/protected source changed')
    result = {'status': 'SELECTED_SOURCE_ADOPTION_VERIFIED_NOT_COMPILED',
              'source_commit': commit, 'project_source_count': len(graph),
              'added_modules': [m for m, _, _ in planned],
              'identical_sources_reused': len(existing),
              'existing_sources_overwritten': 0, 'cache_mutations': 0,
              'context_before': before, 'context_after': after,
              'whole_P1_complete': False, 'new_lean_acceptance': False}
    s.d.save(run / 'INSTALL_RESULT.json', result)
    s.ops.emit('P15_SINGLETON_SOURCES_INSTALLED', **result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    require(re.fullmatch('[0-9a-f]{40}', commit), 'require a full source commit SHA')
    driver, s, code = load_driver(commit)
    base = ROOT / commit / 'source-adoption'
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base and re.fullmatch('attempt-[0-9]{5}', run.name)
                and run.is_dir(), 'unexpected installer worker path')
        install(driver, s, commit, run)
        return 0
    run = s.d.attempt(base)
    before = s.d.original_git_state(REPO)
    s.d.save(run / 'GIT_BEFORE.json', before)
    executed = run / 'executed-installer.py'
    s.d.write_frozen(executed, Path(__file__).read_bytes())
    s.d.write_frozen(run / 'published-driver.py', code)
    try:
        command = s.ops.run(run, 'serialized-source-install',
            s.h.serialize(0, run / 'INSTALL_LANE.json',
                ['python3', '-B', str(executed), '--source-commit', commit,
                 '--inside-lane', str(run)]), relay=True)
        require(command['exit_code'] == 0, 'source adoption held or failed')
    finally:
        after = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_AFTER.json', after)
        require(after == before, 'original dirty repository state changed')
    return 0


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
