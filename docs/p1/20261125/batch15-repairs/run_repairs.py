#!/usr/bin/env python3
"""Retry exactly the fourteen failed owners in three bounded groups.

The published Batch13 normal/audit validators and original guards are loaded
unchanged. Only this manifest's selected group may be installed or built.
--check is read-only; --config-basis source is restricted to local source checks.
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
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-batch15-repairs-v1')
MANIFEST = 'docs/p1/20261125/batch15-repairs/SOURCE_UPDATES.json'
CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
EVIDENCE_PINS = {
    CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614',
    CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880',
}
CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')
TOOL_SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
GROUPS = {
    'wire-five': ['ImbalancedChen.P1ActualVariableFifthPositiveCellLimit',
                  'ImbalancedChen.P1ActualVariableFifthGlobalSourceAssembly',
                  'ImbalancedChen.P1OriginalFifthRawBoxSelectorEquivalence',
                  'ImbalancedChen.P1OriginalFifthMiddleShellBinMoment',
                  'ImbalancedChen.P1OriginalOld15Majorant'],
    'ordinary-five': ['ImbalancedChen.P1OriginalVariableFourthActiveOnly',
                      'ImbalancedChen.P5ActualHBMediumRoleSupports',
                      'ImbalancedChen.P4BCompactSmoothMassPrecision',
                      'ImbalancedChen.P2OriginalAdaptiveSourceSplit',
                      'ImbalancedChen.P2OriginalLowerCompactStartCapConstructor'],
    'interiors-four': ['ImbalancedChen.P4AOriginalFull87H3Interiors',
                       'ImbalancedChen.P4AOriginalFull87SeedNineFiftyInteriors',
                       'ImbalancedChen.P4AOriginalFull87H5H7Interiors',
                       'ImbalancedChen.P4AOriginalFull87DescAscPairInteriors'],
}
BEFORE = {'wire-five': TOOL_SOURCE, 'ordinary-five': TOOL_SOURCE,
          'interiors-four': '4f7a975211bdbdccc76adc14734aa2de4a13b6ad'}
COUNTS = {'wire-five': 271, 'ordinary-five': 365, 'interiors-four': 219}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def check_configs(project, configuration, d):
    need({p: d.fingerprint(project / p) for p in CONFIGS} == configuration and
         not (project / 'lakefile.lean').exists() and not (project / 'lakefile.lean').is_symlink(),
         'project configuration differs from the selected pinned basis')


def inputs(repo, project, source_commit, group, config_basis):
    need(re.fullmatch(r'[0-9a-f]{40}', source_commit) is not None, 'source-commit requires a full lowercase SHA')
    need(subprocess.check_output(['git', 'cat-file', '-t', source_commit], cwd=repo).strip() == b'commit',
         'source-commit must name an existing commit object')
    cache = {}

    def git(commit, path):
        key = (commit, path)
        if key not in cache:
            cache[key] = subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)
        return cache[key]

    raw = {API_PATH: git(API_COMMIT, API_PATH), MANIFEST: git(source_commit, MANIFEST)}
    need(sha(raw[API_PATH]) == API_SHA, 'published Batch13 API pin differs')
    api = types.ModuleType('published_batch13_primitives')
    api.__file__ = '<pinned Git object: ' + API_PATH + '>'
    exec(compile(raw[API_PATH], api.__file__, 'exec'), api.__dict__)
    need(api.PROJECT == PROJECT and api.REPO == REPO and api.TOOLS == TOOL_SOURCE,
         'published helper environment differs')
    pins = {API_PATH: API_SHA, MANIFEST: sha(raw[MANIFEST]), **api.PINS, **EVIDENCE_PINS}
    for path, digest in EVIDENCE_PINS.items():
        raw[path] = git(source_commit, path)
        need(sha(raw[path]) == digest, 'accepted runtime evidence pin differs: ' + path)
    for path, digest in api.PINS.items():
        raw[path] = git(api.TOOLS, path)
        need(sha(raw[path]) == digest, 'unchanged helper pin differs: ' + path)
    h, ops, d = api.load(raw[api.HELPER], 'batch5'), api.load(raw[api.OPS], 'batch6'), api.load(raw[api.PRIMITIVES], 'primitives')
    manifest = json.loads(raw[MANIFEST])
    all_targets = [m for modules in GROUPS.values() for m in modules]
    need(manifest['schema'] == 'p1_batch15_failed_fourteen_repairs_v1' and
         [r['module'] for r in manifest['modules']] == all_targets and
         set(manifest['source_group_graphs']) == set(GROUPS), 'fixed fourteen-owner manifest scope differs')
    updates, payloads = [], {}
    for row in manifest['modules']:
        m, selected_group = row['module'], row['group']
        need(selected_group in GROUPS and m in GROUPS[selected_group] and
             row['before_commit'] == BEFORE[selected_group] and row['path'] == h.module_path(m),
             'source update path/group/preimage anchor differs: ' + m)
        payload, before = git(source_commit, row['path']), git(row['before_commit'], row['path'])
        need(sha(payload) == row['after_sha256'] and sha(before) == row['before_sha256'] and
             h.imports(payload) == h.imports(before), 'source update bytes/imports differ: ' + m)
        if selected_group == group:
            payloads[row['path']] = payload
            updates.append({'module': m, 'path': row['path'], 'before_sha256': row['before_sha256'],
                            'after_sha256': row['after_sha256'], 'cloud_source_mutation_required': True})
    need([r['module'] for r in updates] == GROUPS[group], 'selected install scope differs')
    api.preflight_sources(project, updates, payloads, h)
    graph, actual = h.project_graph(project, GROUPS[group])
    sources = {m: sha(git(source_commit, h.module_path(m))) for m in graph}
    for m in graph:
        imports = [x for x in h.imports(git(source_commit, h.module_path(m))) if x.startswith('ImbalancedChen.')]
        need(graph[m] == imports, 'project imports differ: ' + m)
        need(m in GROUPS[group] or actual[m]['sha256'] == sources[m], 'dependency source differs: ' + m)
    for m in GROUPS[group]:
        need(not (set(all_targets) - {m}) & h.closure(graph, [m]), 'candidate groups overlap by dependency')
    recorded_graph = manifest['source_group_graphs'][group]
    map_sha = sha((json.dumps(sources, ensure_ascii=False, sort_keys=True, separators=(',', ':')) + '\n').encode())
    need(recorded_graph['targets'] == GROUPS[group] and
         len(graph) == recorded_graph['union_source_modules'] == COUNTS[group] and
         map_sha == recorded_graph['union_source_map_sha256'], 'complete group source map differs')
    source_config = {}
    need(set(manifest['source_configuration_bindings']) == set(CONFIGS) and
         set(manifest['runtime_configuration_bindings']) == set(CONFIGS), 'configuration scope differs')
    for path in CONFIGS:
        raw[path] = git(source_commit, path)
        source_config[path] = {'bytes': len(raw[path]), 'sha256': sha(raw[path])}
        need(source_config[path] == manifest['source_configuration_bindings'][path], 'source configuration pin differs')
        pins[path] = source_config[path]['sha256']
    runtime_config = manifest['runtime_configuration_bindings']
    observed = json.loads(raw[CONFIG_OBSERVATION])['configs']
    review = json.loads(raw[CONFIG_REVIEW])
    evidence = manifest['runtime_configuration_evidence']
    need(evidence['path'] == CONFIG_OBSERVATION and evidence['sha256'] == EVIDENCE_PINS[CONFIG_OBSERVATION] and
         runtime_config == {p: {k: observed[p][k] for k in ('bytes', 'sha256')} for p in CONFIGS} and
         all(observed[p]['exists'] and not observed[p]['is_symlink'] for p in CONFIGS) and
         not observed['lakefile.lean']['exists'] and not observed['lakefile.lean']['is_symlink'] and
         review['source_configuration_bindings'] == source_config and
         review['runtime_configuration_bindings'] == runtime_config,
         'configuration bindings differ from the pinned observation/review')
    check_configs(project, source_config if config_basis == 'source' else runtime_config, d)
    if config_basis == 'runtime':
        need(d.runtime_binding(h) == review['existing_runtime_bindings'],
             'existing runtime differs from the historically accepted configuration review')
    need(all(sha((project / h.module_path(m)).read_bytes()) == digest for m, digest in h.FOUR_ROOTS.items()),
         'protected original roots changed')
    return api, h, ops, d, raw, pins, updates, payloads, graph, sources, source_config, runtime_config


def run_binding(spec, source_commit, group):
    api, h, ops, d, raw, pins, updates, payloads, graph, sources, source_config, runtime_config = spec
    return {'source_commit': source_commit, 'api_commit': API_COMMIT, 'group': group, 'targets': GROUPS[group],
            'project': str(PROJECT), 'inputs': pins, 'driver_sha256': sha(Path(__file__).read_bytes()),
            'configuration_basis': 'runtime',
            'source_configuration': source_config, 'runtime_configuration': runtime_config,
            'runtime': d.runtime_binding(h)}


def check_installed(spec, runtime):
    api, h, ops, d, raw, pins, updates, payloads, graph, sources, source_config, runtime_config = spec
    check_configs(PROJECT, runtime_config, d)
    need({m: sha((PROJECT / h.module_path(m)).read_bytes()) for m in sources} == sources,
         'installed project source context changed')
    need(d.runtime_binding(h) == runtime, 'existing runtime changed')
    need(all(sha((PROJECT / h.module_path(m)).read_bytes()) == digest for m, digest in h.FOUR_ROOTS.items()),
         'protected original roots changed')


def worker(spec, source_commit, group, root, run):
    api, h, ops, d, raw, pins, updates, payloads, graph, sources, source_config, runtime_config = spec
    d.verify_lane(h)
    binding = api.read_json(root / 'BINDING.json')
    need(binding == run_binding(spec, source_commit, group), 'serialized worker binding changed')
    api.preflight_sources(PROJECT, updates, payloads, h)
    check_configs(PROJECT, runtime_config, d)
    installed = h.install_sources(PROJECT, updates, payloads, run / 'source-backups')
    d.save(run / 'SOURCE_INSTALL.json', {'source_commit': source_commit, 'group': group,
                                       'sources': installed, 'protected_roots': h.check_roots()})
    check_installed(spec, binding['runtime'])
    d.save(run / 'PROJECT_SOURCES.json', {'source_commit': source_commit, 'sources': sources})
    passed, failures, accepted = {}, {}, set()
    for m in GROUPS[group]:
        try:
            check_installed(spec, binding['runtime'])
            passed[m] = api.normal_one(source_commit, PROJECT, root, m, graph, sources, h, ops, d)
        except Exception as error:
            failures[m] = str(error)
            ops.emit('BATCH15_NORMAL_HELD_OR_FAILED', group=group, module=m, reason=str(error))
    audit_error = None
    try:
        check_installed(spec, binding['runtime'])
        api.audit(source_commit, PROJECT, root, passed, graph, sources, h, ops, d, run, accepted)
    except Exception as error:
        audit_error = str(error)
        ops.emit('BATCH15_AUDIT_HELD_OR_FAILED', group=group, reason=audit_error)
    post_error = None
    try:
        check_installed(spec, binding['runtime'])
    except Exception as error:
        post_error = str(error)
        ops.emit('BATCH15_FINAL_CONTEXT_HELD', group=group, reason=post_error)
    complete = accepted == set(GROUPS[group]) and not failures and audit_error is None and post_error is None
    d.save(run / 'RESULT.json', {'source_commit': source_commit, 'group': group, 'targets': GROUPS[group],
           'normal_passed': sorted(passed), 'normal_failed_or_held': failures, 'accepted_owners': sorted(accepted),
           'audit_error': audit_error, 'final_context_error': post_error, 'all_group_owners_accepted': complete,
           'whole_P1_complete': False, 'protected_roots': h.check_roots()})
    return 0 if complete else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--group', choices=GROUPS, required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--config-basis', choices=('runtime', 'source'), default='runtime',
                        help='source is allowed only for a read-only local source/configuration check')
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
    spec = inputs(repo, project, args.source_commit, args.group, args.config_basis)
    api, h, ops, d, raw, pins, updates, payloads, graph, sources, source_config, runtime_config = spec
    root = ROOT / args.source_commit / args.group
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        status = ('SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                  'READ_ONLY_SOURCE_AND_RUNTIME_CONFIG_CHECK_PASS_NOT_ACCEPTANCE')
        print(json.dumps({'status': status, 'source_commit': args.source_commit,
              'manifest_sha256': pins[MANIFEST], 'group': args.group, 'targets': GROUPS[args.group],
              'source_closure_count': len(sources), 'configuration_basis': args.config_basis,
              'source_configuration': source_config, 'runtime_configuration': runtime_config,
              'cloud_runtime_readiness_claimed': False, 'source_installation_performed': False, 'whole_P1_complete': False}))
        return 0
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, args.source_commit, args.group, root, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(repo)
    d.save(root / 'BINDING.json', run_binding(spec, args.source_commit, args.group))
    for path, data in raw.items():
        target = root / 'inputs' / ('source-configuration/' + path if path in CONFIGS else
                                   'e9.py' if path == api.E9 else Path(path).name)
        d.write_frozen(target, data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--source-commit', args.source_commit, '--group', args.group,
             '--run', '--config-basis', 'runtime', '--inside-lane', '--run-dir', str(run)]
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(repo)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty source Git worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
