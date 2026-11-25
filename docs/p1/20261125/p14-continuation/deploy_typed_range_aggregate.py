#!/usr/bin/env python3
"""Deploy one fixed, known Range preimage before the unchanged stage driver.

This performs source deployment only. It neither invokes a compiler nor reads,
deletes, rebuilds, or grants acceptance to any Lean object or proof receipt.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

if not __debug__:
    raise RuntimeError('source deployment requires Python assertions')
sys.dont_write_bytecode = True

REPO = Path('/workspace/goldbach-formalization')
PREFIX = 'docs/p1/20261125/p14-continuation/'
SCRIPT_PATH = PREFIX + 'deploy_typed_range_aggregate.py'
PLAN_PATH = PREFIX + 'TYPED_RANGE_AGGREGATE_DEPLOYMENT.json'
MANIFEST_PATH = PREFIX + 'stages/typed-range-aggregate.json'
MANIFEST_SHA = '786faf4626265a977d9ca25920e30cc62a0007365967d7b8bc0b613b74c36a0f'
SNAPSHOT = '0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb'
DRIVER_SHA = 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1'
TARGET = {
    'module': 'ImbalancedChen.P1HistoricalFifthTypedArchiveRange',
    'path': 'ImbalancedChen/P1HistoricalFifthTypedArchiveRange.lean',
    'preimage_commit': '4d294de6b2a3128a6fb281426e4f204a8514beaa',
    'before_sha256': '79445fb1e15973a37c76bbbf35ab12d59b4be2a811685247df773b4c6fc3fabe',
    'after_sha256': '609ba2dce8e12ef50a7cb086e2eed3056dbfa6ace237757131bd9d2ed220151e',
}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True,
                        help='published commit containing these exact deployment files')
    parser.add_argument('--run', action='store_true', required=True)
    parser.add_argument('--worker', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    source = args.source_commit
    assert re.fullmatch(r'[0-9a-f]{40}', source)
    script = Path(__file__).read_bytes()
    assert script == git(source, SCRIPT_PATH), 'executing deployment source differs'
    plan_bytes = git(source, PLAN_PATH)
    plan = json.loads(plan_bytes)
    assert plan['schema'] == 'p14_fixed_known_preimage_source_deployment_v1'
    assert plan['script_sha256'] == sha(script) and plan['fixed_target'] == TARGET
    assert plan['source_snapshot_commit'] == SNAPSHOT
    assert plan['manifest_sha256'] == MANIFEST_SHA

    driver = git(source, PREFIX + 'run_stage.py')
    assert sha(driver) == DRIVER_SHA
    # Reuse the pinned loader and APIs, without calling any of their main/normal functions.
    import types
    base = types.ModuleType('unchanged_p14_driver')
    exec(compile(driver, PREFIX + 'run_stage.py', 'exec'), base.__dict__)
    assert base.REPO == REPO and base.PROJECT == Path('/workspace/blue-member-build')
    api_bytes = git(base.API_COMMIT, base.API_PATH)
    assert sha(api_bytes) == base.API_SHA
    api = base.load(api_bytes, 'p14_existing_api')
    raw = {p: git(api.TOOLS, p) for p in api.PINS}
    assert all(sha(raw[p]) == digest for p, digest in api.PINS.items())
    h = base.load(raw[api.HELPER], 'p14_existing_helper')
    d = base.load(raw[api.PRIMITIVES], 'p14_existing_primitives')

    manifest_bytes = git(SNAPSHOT, MANIFEST_PATH)
    assert sha(manifest_bytes) == MANIFEST_SHA
    manifest = json.loads(manifest_bytes)
    assert manifest == {'schema': 'p14_existing_frontier_stage_v1',
                        'stage': 'typed-range-aggregate', 'modules': [TARGET]}
    assert git(source, MANIFEST_PATH) == manifest_bytes
    assert TARGET['path'] == h.module_path(TARGET['module'])
    payload = git(SNAPSHOT, TARGET['path'])
    assert sha(payload) == TARGET['after_sha256']
    assert git(source, TARGET['path']) == payload
    assert sha(git(TARGET['preimage_commit'], TARGET['path'])) == TARGET['before_sha256']
    updates = [{k: TARGET[k] for k in ('module', 'path', 'before_sha256', 'after_sha256')}]
    payloads = {TARGET['path']: payload}

    assert sha(base.REVIEW.read_bytes()) == base.REVIEW_SHA
    review = json.loads(base.REVIEW.read_bytes())
    runtime = d.runtime_binding(h)
    assert runtime == review['existing_runtime_bindings']
    configuration = {p: d.fingerprint(base.PROJECT / p) for p in
                     ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')}
    assert configuration == review['runtime_configuration_bindings']
    assert not (base.PROJECT / 'lakefile.lean').exists()
    protected = h.check_roots()

    def preflight():
        target = base.PROJECT / TARGET['path']
        assert target.is_file(), 'fixed repair source must already exist'
        assert all(not p.is_symlink() for p in (target, *target.parents))
        assert sha(target.read_bytes()) in (TARGET['before_sha256'], TARGET['after_sha256'])
        return d.preflight_sources(base.PROJECT, updates, payloads)

    preflight()
    binding = {'source_commit': source, 'source_snapshot_commit': SNAPSHOT,
               'script_sha256': sha(script), 'plan_sha256': sha(plan_bytes),
               'manifest_path': MANIFEST_PATH, 'manifest_sha256': MANIFEST_SHA,
               'fixed_target': TARGET, 'unchanged_driver_sha256': DRIVER_SHA,
               'api_commit': base.API_COMMIT, 'api_sha256': base.API_SHA,
               'tooling_commit': api.TOOLS, 'helper_pins': api.PINS,
               'runtime': runtime, 'configuration': configuration,
               'protected_roots': protected, 'acceptance_claimed': False}
    root = base.ROOT / 'known-preimage-source-deployment' / source / 'typed-range-aggregate'
    if args.worker is None:
        before = d.original_git_state(REPO)
        d.save(root / 'BINDING.json', binding)
        executed = root / 'executed-deployer.py'
        d.write_frozen(executed, script)
        run = d.attempt(root / 'runs')
        d.save(run / 'GIT_BEFORE.json', before)
        child = ['python3', '-B', str(executed), '--source-commit', source,
                 '--run', '--worker', str(run)]
        command = h.serialize(0, run / 'VALIDATION_LANE.json', child)
        d.save(run / 'DEPLOYMENT_COMMAND.json', {'argv': command, 'cwd': str(REPO)})
        try:
            code = subprocess.run(command, cwd=REPO).returncode
        finally:
            after = d.original_git_state(REPO)
            d.save(run / 'GIT_AFTER.json', after)
            assert after == before, 'original source checkout changed'
            assert h.check_roots() == protected
        d.save(run / 'DEPLOYMENT_COMMAND_RESULT.json', {'exit_code': code})
        if code:
            return code
        assert all(row['action'] == 'ALREADY_AFTER_NOOP' for row in preflight())
        worker_bytes = (run / 'WORKER_RESULT.json').read_bytes()
        worker = json.loads(worker_bytes)
        assert worker['source_commit'] == source and worker['target_sha256'] == TARGET['after_sha256']
        result = {'status': 'SOURCE_DEPLOYMENT_ONLY_NOT_ACCEPTANCE', 'source_commit': source,
                  'source_snapshot_commit': SNAPSHOT, 'module': TARGET['module'],
                  'target_sha256': TARGET['after_sha256'], 'worker_result_sha256': sha(worker_bytes),
                  'original_git_unchanged': True, 'compiler_or_kernel_invoked': False,
                  'objects_modified': False, 'accepted_owners': [],
                  'acceptance_claimed': False, 'whole_P1_4_complete': False}
        d.save(run / 'RESULT.json', result)
        print(json.dumps(result), flush=True)
        return 0

    run = args.worker.resolve()
    assert run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir()
    d.verify_lane(h)
    assert json.loads((root / 'BINDING.json').read_bytes()) == binding
    d.save(run / 'SOURCE_PREFLIGHT.json', preflight())
    installed = d.install_sources(base.PROJECT, updates, payloads, run / 'source-backups', h)
    d.save(run / 'SOURCE_INSTALL.json', installed)
    assert all(row['action'] == 'ALREADY_AFTER_NOOP' for row in preflight())
    assert h.imports((base.PROJECT / TARGET['path']).read_bytes()) == h.imports(payload)
    assert h.check_roots() == protected
    d.save(run / 'WORKER_RESULT.json', {
        'status': 'SOURCE_INSTALLED_AWAIT_PARENT_GIT_CHECK_NOT_ACCEPTANCE',
        'source_commit': source, 'source_snapshot_commit': SNAPSHOT,
        'module': TARGET['module'], 'target_sha256': TARGET['after_sha256'],
        'compiler_or_kernel_invoked': False, 'objects_modified': False,
        'acceptance_claimed': False, 'whole_P1_4_complete': False})
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
