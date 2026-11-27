#!/usr/bin/env python3
"""Deploy the fixed Key flatMap preimage before the unchanged stage driver.

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
DEPLOY_PREFIX = 'docs/p1/20261128/p14-resume/'
SCRIPT_PATH = DEPLOY_PREFIX + 'deploy_key_flatmap_expression.py'
PLAN_PATH = DEPLOY_PREFIX + 'KEY_FLATMAP_EXPRESSION_DEPLOYMENT.json'
MANIFEST_PATH = PREFIX + 'stages/typed-key-uniqueness-flatmap-expression-retry.json'
MANIFEST_SHA = '4106bfc6ecd4a5eb1731e1c9fc5eb067e27c69b0f825d5409d4bab8e60d0a139'
STAGE = 'typed-key-uniqueness-flatmap-expression-retry'
SOURCE_BINDING = 'published_execution_commit_argument'
DRIVER_SHA = 'a4d235762954660995cf8500ca65fb94319b248c7f65f94e7ff695e2e59c71c1'
TARGET = {
    'module': 'ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCertificate',
    'path': 'ImbalancedChen/P1HistoricalFifthTypedKeyUniquenessCertificate.lean',
    'preimage_commit': 'a67809b2ce43e291d4809ee0589f8e3246f0ceeb',
    'before_sha256': '7b1a664fca62612a8f2d198a15e512420bb853a2d155eddf7950cec05660973b',
    'after_sha256': 'a8252d0efcb0aa6b46be60308f398775efde036746dcec1b8a7f85eb9402ae60',
}

FIXED_IMPORTS = ['ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore',
                 'ImbalancedChen.P1HistoricalFifthTypedArchiveShape']
ADDED_IMPORT_SHA = '8e13f914299d71a288833cb751b60e437d0cdc61e6183865cc0ba6a9de01fd7c'
SOURCE_CLOSURE_COUNT = 404


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
    assert plan['postimage_source_binding'] == SOURCE_BINDING
    assert plan['script_path'] == SCRIPT_PATH and plan['manifest_path'] == MANIFEST_PATH
    assert plan['target_project_imports'] == FIXED_IMPORTS
    assert plan['source_closure_module_count'] == SOURCE_CLOSURE_COUNT
    assert plan['added_import_source_sha256'] == ADDED_IMPORT_SHA
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

    manifest_bytes = git(source, MANIFEST_PATH)
    assert sha(manifest_bytes) == MANIFEST_SHA
    manifest = json.loads(manifest_bytes)
    assert manifest == {'schema': 'p14_existing_frontier_stage_v1',
                        'stage': STAGE, 'modules': [TARGET]}
    assert TARGET['path'] == h.module_path(TARGET['module'])
    payload = git(source, TARGET['path'])
    assert sha(payload) == TARGET['after_sha256']
    preimage = git(TARGET['preimage_commit'], TARGET['path'])
    assert sha(preimage) == TARGET['before_sha256']
    assert h.imports(preimage) == FIXED_IMPORTS[:1]
    assert h.imports(payload) == FIXED_IMPORTS
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

    # Read source bytes only. Validate the new dependency closure before changing
    # the target; then use the unchanged project_graph to check its postimage.
    published_graph, published_sources = {}, {}

    def published_visit(module):
        if module in published_graph:
            return
        data = git(source, h.module_path(module))
        deps = [m for m in h.imports(data) if m.startswith('ImbalancedChen.')]
        published_graph[module] = deps
        published_sources[module] = {'sha256': sha(data), 'bytes': len(data), 'imports': deps}
        for dependency in deps:
            published_visit(dependency)

    published_visit(TARGET['module'])
    assert h.closure(published_graph, [TARGET['module']]) == set(published_graph)
    assert len(published_graph) == SOURCE_CLOSURE_COUNT
    assert published_graph[TARGET['module']] == FIXED_IMPORTS
    assert published_sources[FIXED_IMPORTS[1]]['sha256'] == ADDED_IMPORT_SHA

    def check_source_closure(allow_known_target_preimage):
        for module, expected in published_sources.items():
            path = base.PROJECT / h.module_path(module)
            assert path.is_file() and not path.is_symlink(), ('source closure path', module)
            data = path.read_bytes()
            if module == TARGET['module'] and allow_known_target_preimage:
                assert sha(data) in (TARGET['before_sha256'], TARGET['after_sha256'])
            else:
                assert sha(data) == expected['sha256'] and len(data) == expected['bytes'], (
                    'published source closure differs', module)
        if not allow_known_target_preimage:
            graph, actual_sources = h.project_graph(base.PROJECT, [TARGET['module']])
            assert graph == published_graph and actual_sources == published_sources, (
                'installed project import graph or complete source closure differs')

    def preflight():
        target = base.PROJECT / TARGET['path']
        assert target.is_file(), 'fixed repair source must already exist'
        assert all(not p.is_symlink() for p in (target, *target.parents))
        assert sha(target.read_bytes()) in (TARGET['before_sha256'], TARGET['after_sha256'])
        check_source_closure(allow_known_target_preimage=True)
        return d.preflight_sources(base.PROJECT, updates, payloads)

    preflight()
    binding = {'source_commit': source, 'source_snapshot_commit': source,
               'script_sha256': sha(script), 'plan_sha256': sha(plan_bytes),
               'manifest_path': MANIFEST_PATH, 'manifest_sha256': MANIFEST_SHA,
               'fixed_target': TARGET, 'unchanged_driver_sha256': DRIVER_SHA,
               'api_commit': base.API_COMMIT, 'api_sha256': base.API_SHA,
               'tooling_commit': api.TOOLS, 'helper_pins': api.PINS,
               'runtime': runtime, 'configuration': configuration,
               'protected_roots': protected, 'published_project_graph': published_graph,
               'published_project_sources': published_sources,
               'source_closure_module_count': SOURCE_CLOSURE_COUNT,
               'acceptance_claimed': False}
    root = base.ROOT / 'known-preimage-source-deployment' / source / STAGE
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
        check_source_closure(allow_known_target_preimage=False)
        worker_bytes = (run / 'WORKER_RESULT.json').read_bytes()
        worker = json.loads(worker_bytes)
        assert worker['source_commit'] == source and worker['target_sha256'] == TARGET['after_sha256']
        assert worker['source_closure_module_count'] == SOURCE_CLOSURE_COUNT
        assert worker['source_closure_matches_published_commit'] is True
        result = {'status': 'SOURCE_DEPLOYMENT_ONLY_NOT_ACCEPTANCE', 'source_commit': source,
                  'source_snapshot_commit': source, 'module': TARGET['module'],
                  'target_sha256': TARGET['after_sha256'], 'worker_result_sha256': sha(worker_bytes),
                  'original_git_unchanged': True, 'compiler_or_kernel_invoked': False,
                  'objects_modified': False, 'accepted_owners': [],
                  'source_closure_module_count': SOURCE_CLOSURE_COUNT,
                  'source_closure_matches_published_commit': True,
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
    check_source_closure(allow_known_target_preimage=False)
    assert h.check_roots() == protected
    d.save(run / 'WORKER_RESULT.json', {
        'status': 'SOURCE_INSTALLED_AWAIT_PARENT_GIT_CHECK_NOT_ACCEPTANCE',
        'source_commit': source, 'source_snapshot_commit': source,
        'module': TARGET['module'], 'target_sha256': TARGET['after_sha256'],
        'compiler_or_kernel_invoked': False, 'objects_modified': False,
        'source_closure_module_count': SOURCE_CLOSURE_COUNT,
        'source_closure_matches_published_commit': True,
        'acceptance_claimed': False, 'whole_P1_4_complete': False})
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
