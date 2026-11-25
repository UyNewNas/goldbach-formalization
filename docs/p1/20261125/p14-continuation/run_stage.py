#!/usr/bin/env python3
"""Run a manifest-bound P1.4 frontier through the existing acceptance APIs.

This caller does not replace the normal, kernel, full-owned, runtime guard or
serialization implementations. --check is read-only. Existing matching receipts
are reused; ready objects with unknown provenance are held by normal_one.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import types

if not __debug__:
    raise RuntimeError('P1.4 validation requires Python assertions; optimized execution is forbidden')

sys.dont_write_bytecode = True
sys.setrecursionlimit(10000)
REPO = Path('/workspace/goldbach-formalization')
PROJECT = Path('/workspace/blue-member-build')
ROOT = Path('/workspace/p1-complete-proof/20261125-p14-continuation')
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
DRIVER_PATH = 'docs/p1/20261125/p14-continuation/run_stage.py'
REVIEW = Path('/workspace/p1-complete-proof/20261125-batch16-repairs-v1/9ea714790c06b2270f2028555d9ba774b152d536/expression-two/inputs/review.json')
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def load(data, name):
    module = types.ModuleType(name)
    module.__file__ = '<pinned Git object: ' + name + '>'
    exec(compile(data, module.__file__, 'exec'), module.__dict__)
    return module


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--manifest', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--worker', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    assert re.fullmatch(r'[0-9a-f]{40}', source)
    assert re.fullmatch(r'docs/p1/20261125/p14-continuation/stages/[a-z0-9-]+\.json', args.manifest)
    driver_bytes = Path(__file__).read_bytes()
    if driver_bytes != git(source, DRIVER_PATH):
        raise RuntimeError('executing driver differs from the claimed Git source commit')
    data = git(API_COMMIT, API_PATH)
    assert sha(data) == API_SHA
    api = load(data, 'p14_existing_api')
    raw = {p: git(api.TOOLS, p) for p in api.PINS}
    assert all(sha(raw[p]) == digest for p, digest in api.PINS.items())
    h = load(raw[api.HELPER], 'p14_existing_helper')
    ops = load(raw[api.OPS], 'p14_existing_ops')
    d = load(raw[api.PRIMITIVES], 'p14_existing_primitives')
    manifest_bytes = git(source, args.manifest)
    manifest = json.loads(manifest_bytes)
    assert manifest['schema'] == 'p14_existing_frontier_stage_v1'
    assert re.fullmatch(r'[a-z0-9-]+', manifest['stage'])
    rows = manifest['modules']
    targets = [row['module'] for row in rows]
    assert targets and len(targets) == len(set(targets))
    updates, payloads = [], {}
    for row in rows:
        assert row['path'] == h.module_path(row['module'])
        payload = git(source, row['path'])
        assert sha(payload) == row['after_sha256']
        assert sha(git(row['preimage_commit'], row['path'])) == row['before_sha256']
        payloads[row['path']] = payload
        updates.append({k: row[k] for k in ('module', 'path', 'before_sha256', 'after_sha256')})
        updates[-1]['cloud_source_mutation_required'] = row['before_sha256'] != row['after_sha256']
    api.preflight_sources(PROJECT, updates, payloads, h)
    graph, actual = h.project_graph(PROJECT, targets)
    sources = {m: sha(git(source, h.module_path(m))) for m in graph}
    for m in graph:
        assert graph[m] == [x for x in h.imports(git(source, h.module_path(m))) if x.startswith('ImbalancedChen.')], m
        assert m in targets or actual[m]['sha256'] == sources[m], m
    assert all(not (set(targets) - {m}) & h.closure(graph, [m]) for m in targets)
    assert sha(REVIEW.read_bytes()) == REVIEW_SHA
    review = json.loads(REVIEW.read_bytes())
    assert d.runtime_binding(h) == review['existing_runtime_bindings']
    assert {p: d.fingerprint(PROJECT / p) for p in ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')} == review['runtime_configuration_bindings']
    assert not (PROJECT / 'lakefile.lean').exists()
    protected = h.check_roots()
    root = ROOT / manifest['stage'] / source
    if args.check:
        assert args.worker is None
        print(json.dumps({'status': 'READ_ONLY_SOURCE_CHECK_PASS_NOT_ACCEPTANCE', 'source_commit': source,
                          'targets': targets, 'source_closure_count': len(sources), 'protected_roots': protected}), flush=True)
        return 0
    binding = {'source_commit': source, 'manifest_path': args.manifest, 'manifest_sha256': sha(manifest_bytes),
               'driver_sha256': sha(Path(__file__).read_bytes()), 'project_sources': sources,
               'targets': {m: sources[m] for m in targets}, 'runtime': d.runtime_binding(h),
               'protected_roots': protected, 'whole_P1_4_complete': False}
    if args.worker is None:
        before = d.original_git_state(REPO)
        d.save(root / 'BINDING.json', binding)
        d.write_frozen(root / 'inputs/e9.py', raw[api.E9])
        executed = root / 'executed-driver.py'
        d.write_frozen(executed, driver_bytes)
        run = d.attempt(root / 'runs')
        d.save(run / 'GIT_BEFORE.json', before)
        child = ['python3', '-B', str(executed), '--source-commit', source,
                 '--manifest', args.manifest, '--run', '--worker', str(run)]
        try:
            return subprocess.run(h.serialize(0, run / 'VALIDATION_LANE.json', child)).returncode
        finally:
            after = d.original_git_state(REPO)
            d.save(run / 'GIT_AFTER.json', after)
            assert after == before, 'original source checkout changed'
    run = args.worker.resolve()
    assert run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir()
    d.verify_lane(h)
    assert json.loads((root / 'BINDING.json').read_bytes()) == binding
    installed = h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    d.save(run / 'SOURCE_INSTALL.json', installed)
    passed, failed, accepted = {}, {}, set()
    for m in targets:
        try:
            passed[m] = api.normal_one(source, PROJECT, root, m, graph, sources, h, ops, d)
        except Exception as error:
            failed[m] = str(error)
            print('NORMAL_HELD_OR_FAILED', m, str(error), flush=True)
    audit_error = None
    try:
        api.audit(source, PROJECT, root, passed, graph, sources, h, ops, d, run, accepted)
    except Exception as error:
        audit_error = str(error)
        print('AUDIT_HELD_OR_FAILED', str(error), flush=True)
    result = {'source_commit': source, 'stage': manifest['stage'], 'targets': binding['targets'],
              'source_closure_count': len(sources), 'normal_passed': sorted(passed),
              'normal_failed_or_held': failed, 'accepted_owners': sorted(accepted), 'audit_error': audit_error,
              'whole_P1_4_complete': False, 'protected_roots': h.check_roots()}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result), flush=True)
    return 0 if set(targets) == accepted and not failed and audit_error is None else 1


if __name__ == '__main__':
    raise SystemExit(main())
