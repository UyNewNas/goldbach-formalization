#!/usr/bin/env python3
"""Run exactly the five reviewed ordinary P1 dependencies with published tools.

--check reads pinned Git objects, source/configuration and existing runtime hashes.
The source configuration basis is restricted to local read-only checks.
--run uses the existing lane-0 serializer, normal receipts and generic e9 audit.
No source installation, helper mutation or new verification implementation.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys
import types

sys.dont_write_bytecode = True
SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
NORMAL_TOOLS = '9246927b8faebca3c06e4a5a47e733b5f13536db'
AUDIT_TOOLS = 'afe0ca6653f4eba9c258ecb8a743d0b45edd10c6'
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-ordinary-five-v1')
GROUP = 'ordinary-five'
RETRY = 'docs/p1/20261125/batch11-repairs/retry_four.py'
GROUP_CALLER = 'docs/p1/20261125/next-frontier/batch12-candidates/run_candidates.py'
CATALOG = 'docs/p1/20261125/next-frontier/ordinary-five/CANDIDATES.json'
CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
PINS = {
    RETRY: '290228a30d7a773a52a27241d6d3fbf18efb3d5e3fd9b30c8f0db4d670e5717e',
    GROUP_CALLER: '8fc871e44e4702b01005aa179170cd172b50537f7aaa98e6bbdde4253ef2ac47',
    CATALOG: 'bcf758d858193e72dff1ff2ef77313b23abbffb17f38a601ddd51c0281ac363d',
    CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614',
    CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880',
}
TARGETS = [
    'ImbalancedChen.P1OriginalVariableFourthActiveOnly',
    'ImbalancedChen.P5ActualHBMediumRoleSupports',
    'ImbalancedChen.P4BCompactSmoothMassPrecision',
    'ImbalancedChen.P2OriginalAdaptiveSourceSplit',
    'ImbalancedChen.P2OriginalLowerCompactStartCapConstructor',
]
CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_configs(project, configuration, d):
    need({p: d.fingerprint(project / p) for p in CONFIGS} == configuration and
         not (project / 'lakefile.lean').exists() and not (project / 'lakefile.lean').is_symlink(),
         'project configuration differs from the selected pinned basis')


def check_runtime(h, d, raw):
    need(d.runtime_binding(h) == json.loads(raw[CONFIG_REVIEW])['existing_runtime_bindings'],
         'existing runtime differs from the historically accepted configuration review')


def inputs(repo, project, catalog_commit, config_basis='runtime'):
    if catalog_commit is not None:
        need(re.fullmatch(r'[0-9a-f]{40}', catalog_commit), 'catalog commit requires a full lowercase SHA')
        need(subprocess.check_output(['git', 'cat-file', '-t', catalog_commit], cwd=repo).strip() == b'commit',
             'catalog SHA is not a commit')

    def git(commit, path):
        return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)

    raw = {RETRY: git(NORMAL_TOOLS, RETRY), GROUP_CALLER: git(AUDIT_TOOLS, GROUP_CALLER)}
    for path in (CATALOG, CONFIG_OBSERVATION, CONFIG_REVIEW):
        raw[path] = git(catalog_commit, path) if catalog_commit else (repo / path).read_bytes()
    need(all(sha(raw[p]) == digest for p, digest in PINS.items()), 'published input pin differs')
    api = types.ModuleType('published_normal_primitives')
    api.__file__ = '<pinned Git object: ' + RETRY + '>'
    exec(compile(raw[RETRY], api.__file__, 'exec'), api.__dict__)
    audit_api = api.load(raw[GROUP_CALLER], 'published_generic_audit')
    need(api.COMMIT == audit_api.SOURCE == SOURCE and api.PROJECT == audit_api.PROJECT == PROJECT and
         api.REPO == audit_api.REPO == REPO, 'published source/environment differs')
    pins = dict(PINS)
    for path in (api.HELPER, api.OPS, api.PRIMITIVES, api.E9):
        raw[path] = git(SOURCE, path)
        pins[path] = api.PINS[path]
        need(sha(raw[path]) == pins[path], 'unchanged helper pin differs: ' + path)
    h, ops, d = api.load(raw[api.HELPER], 'batch5'), api.load(raw[api.OPS], 'batch6'), api.load(raw[api.PRIMITIVES], 'primitives')
    catalog = json.loads(raw[CATALOG])
    need(catalog['schema'] == 'p1-ordinary-five-source-frontier-v1' and
         catalog['anchor']['published_source_commit'] == SOURCE and
         [row['module'] for row in catalog['candidates']] == TARGETS, 'fixed five-owner catalog differs')
    graph, actual = h.project_graph(project, TARGETS)
    sources = {m: sha(git(SOURCE, h.module_path(m))) for m in graph}
    source_map_sha = sha((json.dumps(sources, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode())
    need(len(graph) == catalog['graph_verification']['union_source_modules'] == 365 and
         {m: row['sha256'] for m, row in actual.items()} == sources == catalog['expected_project_sources'] and
         source_map_sha == catalog['graph_verification']['union_source_map_sha256'],
         'complete 365-module source closure differs; no installation permitted')
    for row in catalog['candidates']:
        m = row['module']
        need(row['source']['path'] == h.module_path(m) and row['source']['sha256'] == sources[m] and
             row['direct_project_imports'] == graph[m], 'candidate source/import binding differs: ' + m)
        need(not (set(TARGETS) - {m}) & h.closure(graph, [m]), 'five owners overlap by dependency')
    parents = {parent for m in TARGETS for parent in graph[m]}
    need(set(catalog['parents']) == parents, 'accepted direct-parent scope differs')
    for parent in sorted(parents):
        row = catalog['parents'][parent]
        closure = sorted(h.closure(graph, [parent]))
        need(row['source']['sha256'] == sources[parent] and row['source_closure'] == closure and
             row['source_closure_modules'] == len(closure) and
             row['owner_receipt']['status'] == api.PASS and
             row['owner_receipt']['full_owned_including_private_generated'] is True,
             'accepted parent source/receipt scope differs: ' + parent)
    excluded = set(api.TARGETS) | {'ImbalancedChen.P4AOrderedThirdCommonSchedule',
                                 'ImbalancedChen.P4AOrderedThirdSameCoefficient'}
    need(not excluded & set(graph), 'closure includes a separately repaired or mismatched owner')
    need(set(catalog['source_configuration_bindings']) == set(CONFIGS) and
         set(catalog['runtime_configuration_bindings']) == set(CONFIGS), 'catalog configuration scope differs')
    source_configuration = {}
    for path in CONFIGS:
        raw[path] = git(SOURCE, path)
        source_configuration[path] = {'bytes': len(raw[path]), 'sha256': sha(raw[path])}
        need(source_configuration[path] == catalog['source_configuration_bindings'][path], 'source configuration pin differs')
        pins[path] = source_configuration[path]['sha256']
    observed = json.loads(raw[CONFIG_OBSERVATION])['configs']
    review = json.loads(raw[CONFIG_REVIEW])
    runtime_configuration = catalog['runtime_configuration_bindings']
    need(runtime_configuration == {p: {k: observed[p][k] for k in ('bytes', 'sha256')} for p in CONFIGS} and
         all(observed[p]['exists'] and not observed[p]['is_symlink'] for p in CONFIGS) and
         not observed['lakefile.lean']['exists'] and not observed['lakefile.lean']['is_symlink'] and
         review['source_configuration_bindings'] == source_configuration and
         review['runtime_configuration_bindings'] == runtime_configuration,
         'configuration bindings differ from the pinned observation/review')
    for key, path in (('actual_snapshot', CONFIG_OBSERVATION), ('historical_review', CONFIG_REVIEW)):
        need(catalog['runtime_configuration_evidence'][key] == {'path': path, 'sha256': pins[path]},
             'configuration evidence reference differs')
    configuration = source_configuration if config_basis == 'source' else runtime_configuration
    check_configs(project, configuration, d)
    if config_basis == 'runtime':
        check_runtime(h, d, raw)
    need(all(sha((project / h.module_path(m)).read_bytes()) == value for m, value in h.FOUR_ROOTS.items()),
         'protected original root source differs')
    return api, audit_api, h, ops, d, raw, pins, graph, sources, configuration, catalog


def binding(spec, catalog_commit):
    api, audit_api, h, ops, d, raw, pins, graph, sources, configuration, catalog = spec
    return {'source_commit': SOURCE, 'tooling_commits': {'normal': NORMAL_TOOLS, 'audit': AUDIT_TOOLS},
            'catalog_commit': catalog_commit, 'group': GROUP, 'targets': TARGETS, 'project': str(PROJECT),
            'driver_sha256': sha(Path(__file__).read_bytes()), 'inputs': pins,
            'configuration_basis': 'runtime', 'configuration': configuration,
            'source_configuration': catalog['source_configuration_bindings'],
            'runtime_configuration': catalog['runtime_configuration_bindings'],
            'runtime': d.runtime_binding(h)}


def check_parent_artifacts(project, module, graph, catalog, h, d):
    for parent in graph[module]:
        row = catalog['parents'][parent]
        need(d.snapshot(project, parent) == row['source_plus_five_outputs'],
             'accepted parent source/outputs changed; do not rebuild: ' + parent)
        receipt = row['owner_receipt']
        state = Path(receipt['runtime_state'])
        need(state in h.STATES and d.fingerprint(state)['sha256'] == receipt['runtime_state_sha256'],
             'accepted parent runtime changed; inspect existing evidence: ' + parent)


def worker(spec, catalog_commit, run):
    api, audit_api, h, ops, d, raw, pins, graph, sources, configuration, catalog = spec
    d.verify_lane(h)
    need(api.read_json(ROOT / 'BINDING.json') == binding(spec, catalog_commit), 'worker binding differs')
    d.save(run / 'PROJECT_SOURCES.json', sources)
    passed, failures, accepted, reused_parents = {}, {}, set(), set()
    for m in TARGETS:
        try:
            check_configs(PROJECT, configuration, d)
            check_runtime(h, d, raw)
            check_parent_artifacts(PROJECT, m, graph, catalog, h, d)
            reused_parents.update(graph[m])
            passed[m] = api.normal_one(m, graph, sources, h, ops, d, root=ROOT, project=PROJECT)
        except Exception as error:
            failures[m] = str(error)
            ops.emit('ORDINARY_FIVE_NORMAL_HELD_OR_FAILED', module=m, reason=str(error))
    audit_error = None
    try:
        check_configs(PROJECT, configuration, d)
        check_runtime(h, d, raw)
        audit_api.audit(ROOT, passed, graph, sources, api, h, ops, d, run, accepted)
        check_configs(PROJECT, configuration, d)
        check_runtime(h, d, raw)
    except Exception as error:
        audit_error = str(error)
        ops.emit('ORDINARY_FIVE_AUDIT_HELD_OR_FAILED', reason=audit_error)
    d.save(run / 'RESULT.json', {'source_commit': SOURCE, 'catalog_commit': catalog_commit,
           'group': GROUP, 'targets': TARGETS, 'normal_passed': sorted(passed),
           'accepted_direct_parent_artifacts_reused': sorted(reused_parents),
           'normal_failed_or_held': failures, 'accepted_owners': sorted(accepted), 'audit_error': audit_error,
           'all_five_accepted': set(TARGETS) == accepted and not failures and audit_error is None,
           'source_installation_performed': False, 'whole_P1_complete': False, 'protected_roots': h.check_roots()})
    return 0 if set(TARGETS) == accepted and not failures and audit_error is None else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--catalog-commit',
                        help='Full published catalog commit; required for --run. --check may use the pinned local catalog.')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--config-basis', choices=('runtime', 'source'), default='runtime',
                        help='source is allowed only for --check on a non-cloud project')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    repo, project = args.source_repo.resolve(), args.project.resolve()
    need(args.config_basis == 'runtime' or (args.check and project != PROJECT),
         'source configuration basis requires --check on a non-cloud project')
    if not args.check:
        need(repo == REPO and project == PROJECT, 'execution is restricted to the existing cloud project')
    need(args.check or args.catalog_commit is not None, '--run requires a published catalog commit')
    spec = inputs(repo, project, args.catalog_commit, args.config_basis)
    api, audit_api, h, ops, d, raw, pins, graph, sources, configuration, catalog = spec
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        status = ('SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                  'READ_ONLY_SOURCE_AND_RUNTIME_CONFIG_CHECK_PASS_NOT_ACCEPTANCE')
        print(json.dumps({'status': status, 'group': GROUP,
                          'source_commit': SOURCE, 'catalog_commit': args.catalog_commit,
                          'targets': TARGETS, 'source_closure_count': len(sources),
                          'configuration_basis': args.config_basis, 'configuration': configuration,
                          'source_configuration': catalog['source_configuration_bindings'],
                          'runtime_configuration': catalog['runtime_configuration_bindings'],
                          'cloud_runtime_readiness_claimed': False, 'source_installation_performed': False,
                          'whole_P1_complete': False}))
        return 0
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == ROOT / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, args.catalog_commit, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(repo)
    d.save(ROOT / 'BINDING.json', binding(spec, args.catalog_commit))
    for path, data in raw.items():
        target = ROOT / 'inputs' / ('source-configuration/' + path if path in CONFIGS else
                                   'e9.py' if path == api.E9 else Path(path).name)
        d.write_frozen(target, data)
    executed = ROOT / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(ROOT / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', [
            'python3', '-B', str(executed), '--catalog-commit', args.catalog_commit,
            '--run', '--config-basis', 'runtime', '--inside-lane', '--run-dir', str(run)]), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(repo)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
