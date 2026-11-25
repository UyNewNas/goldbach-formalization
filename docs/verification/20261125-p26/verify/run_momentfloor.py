#!/usr/bin/env python3
"""One repaired owner over an exact P1 dependency tree, using unchanged P1 engines.

No Git writes/fetches. --check is read-only. --run installs ONLY the pinned target
in /workspace/blue-member-build, then reuses Batch13 normal/leanchecker/full-owned
acceptance. Source provenance is an explicit two-commit overlay, never a claim
that the P2 target commit supplies the P1 dependencies.
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
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-p26-momentfloor-p1-closure-v1')
MODULE = 'ImbalancedChen.P2OriginalSaving19MomentFloorConsumer'
TARGET_COMMIT = 'a66770a240913c3ea02b3a05277fa5c53891cffe'
DEPENDENCY_COMMIT = '298670f119d24874b719facb3ef756f1e01223a1'
BEFORE = '71cb35db43b7ccfe0340a60223e080407607869c11bf75b06542bf4c5c0a1d2d'
AFTER = '0e332cbd300f14e811a564d129c20030f1ab6bae24f9f98f4ccf7bec2d7132f0'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_PATH = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOL_SOURCE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
CONFIG_OBSERVATION = 'docs/p1/20261125/runtime-configuration/ACTUAL_CONFIGURATION.json'
CONFIG_REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
EVIDENCE_PINS = {
    CONFIG_OBSERVATION: 'df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614',
    CONFIG_REVIEW: '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880',
}
CONFIGS = ('lean-toolchain', 'lake-manifest.json', 'lakefile.toml')


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repo, commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=repo)


def check_configs(project, configuration, d):
    need({p: d.fingerprint(project / p) for p in CONFIGS} == configuration and
         not (project / 'lakefile.lean').exists() and not (project / 'lakefile.lean').is_symlink(),
         'configuration differs from the selected pinned basis')


def inputs(args):
    need(args.target_source_commit == TARGET_COMMIT and args.dependency_commit == DEPENDENCY_COMMIT,
         'this single-owner wrapper is pinned to the reviewed target and P1 dependency commits')
    for repo, commit in ((args.source_repo, DEPENDENCY_COMMIT), (args.target_source_repo, TARGET_COMMIT)):
        need(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=repo).strip() == b'commit',
             'required commit object is unavailable: ' + commit)
    raw = {API_PATH: git(args.source_repo, API_COMMIT, API_PATH)}
    need(sha(raw[API_PATH]) == API_SHA, 'published Batch13 API pin differs')
    api = types.ModuleType('published_batch13_primitives')
    api.__file__ = '<pinned Git object: ' + API_PATH + '>'
    exec(compile(raw[API_PATH], api.__file__, 'exec'), api.__dict__)
    need(api.PROJECT == PROJECT and api.REPO == REPO and api.TOOLS == TOOL_SOURCE,
         'published helper environment differs')
    for path, digest in api.PINS.items():
        raw[path] = git(args.source_repo, TOOL_SOURCE, path)
        need(sha(raw[path]) == digest, 'unchanged helper pin differs: ' + path)
    for path, digest in EVIDENCE_PINS.items():
        raw[path] = git(args.source_repo, DEPENDENCY_COMMIT, path)
        need(sha(raw[path]) == digest, 'accepted configuration evidence differs: ' + path)
    h, ops, d = (api.load(raw[api.HELPER], 'batch5'), api.load(raw[api.OPS], 'batch6'),
                 api.load(raw[api.PRIMITIVES], 'snapshot_primitives'))
    path = h.module_path(MODULE)
    before = git(args.source_repo, DEPENDENCY_COMMIT, path)
    payload = git(args.target_source_repo, TARGET_COMMIT, path)
    need(sha(before) == BEFORE and sha(payload) == AFTER and h.imports(before) == h.imports(payload),
         'target preimage/postimage/imports differ from the reviewed repair')
    raw[path] = payload
    updates = [{'module': MODULE, 'path': path, 'before_sha256': BEFORE,
                'after_sha256': AFTER, 'cloud_source_mutation_required': True}]
    payloads = {path: payload}
    api.preflight_sources(args.project, updates, payloads, h)
    graph, sources, pending = {}, {}, [MODULE]
    while pending:
        m = pending.pop()
        if m in graph:
            continue
        data = payload if m == MODULE else git(args.source_repo, DEPENDENCY_COMMIT, h.module_path(m))
        sources[m] = sha(data)
        graph[m] = [x for x in h.imports(data) if x.startswith('ImbalancedChen.')]
        pending.extend(graph[m])
    h.closure(graph, [MODULE])
    differences = []
    for m in sorted(graph):
        actual_path = args.project / h.module_path(m)
        data = actual_path.read_bytes() if actual_path.is_file() else None
        actual_sha = sha(data) if data is not None else None
        actual_imports = [x for x in h.imports(data) if x.startswith('ImbalancedChen.')] if data is not None else None
        if actual_imports != graph[m] or (m != MODULE and actual_sha != sources[m]):
            differences.append({'module': m, 'expected_p1_sha256': sources[m],
                                'actual_sha256': actual_sha,
                                'expected_imports': graph[m], 'actual_imports': actual_imports})
    need(not differences, 'P1_DEPENDENCY_CLOSURE_MISMATCH ' + json.dumps(differences, sort_keys=True))
    actual_graph, _ = h.project_graph(args.project, [MODULE])
    need(actual_graph == graph, 'actual import closure differs from the reviewed P1 dependency graph')
    source_config = {}
    for path in CONFIGS:
        raw[path] = git(args.source_repo, DEPENDENCY_COMMIT, path)
        source_config[path] = {'bytes': len(raw[path]), 'sha256': sha(raw[path])}
    observed = json.loads(raw[CONFIG_OBSERVATION])['configs']
    review = json.loads(raw[CONFIG_REVIEW])
    runtime_config = review['runtime_configuration_bindings']
    need(review['source_configuration_bindings'] == source_config and
         runtime_config == {p: {k: observed[p][k] for k in ('bytes', 'sha256')} for p in CONFIGS} and
         all(observed[p]['exists'] and not observed[p]['is_symlink'] for p in CONFIGS) and
         not observed['lakefile.lean']['exists'] and not observed['lakefile.lean']['is_symlink'],
         'configuration observation/review binding differs')
    check_configs(args.project, source_config if args.config_basis == 'source' else runtime_config, d)
    if args.config_basis == 'runtime':
        need(d.runtime_binding(h) == review['existing_runtime_bindings'], 'accepted existing runtime differs')
    need(all(sha((args.project / h.module_path(m)).read_bytes()) == digest for m, digest in h.FOUR_ROOTS.items()),
         'protected original roots changed')
    provenance = {
        'schema': 'p26_single_target_over_exact_p1_dependency_tree_v1',
        'target_source_commit': TARGET_COMMIT, 'target_source_sha256': AFTER,
        'target_preimage_sha256': BEFORE, 'dependency_commit': DEPENDENCY_COMMIT,
        'engine_source_commit_scope': 'target_owner_only_not_entire_project_tree',
        'project_source_origins': {m: TARGET_COMMIT if m == MODULE else DEPENDENCY_COMMIT for m in sources},
        'project_sources_after_single_target_install': sources,
        'source_closure_count': len(sources), 'project_import_graph': graph,
        'target_branch_dependency_acceptance_claimed': False,
        'whole_P1_complete': False, 'whole_P2_complete': False,
    }
    return types.SimpleNamespace(api=api, h=h, ops=ops, d=d, raw=raw, updates=updates,
                                 payloads=payloads, graph=graph, sources=sources, provenance=provenance,
                                 source_config=source_config, runtime_config=runtime_config)


def binding(spec):
    return {**spec.provenance, 'project': str(PROJECT), 'api_commit': API_COMMIT,
            'tooling_commit': TOOL_SOURCE, 'input_sha256': {p: sha(b) for p, b in spec.raw.items()},
            'driver_sha256': sha(Path(__file__).read_bytes()), 'configuration_basis': 'runtime',
            'source_configuration': spec.source_config, 'runtime_configuration': spec.runtime_config,
            'runtime': spec.d.runtime_binding(spec.h)}


def check_installed(spec, runtime):
    check_configs(PROJECT, spec.runtime_config, spec.d)
    need({m: sha((PROJECT / spec.h.module_path(m)).read_bytes()) for m in spec.sources} == spec.sources,
         'installed project source context changed')
    need(spec.d.runtime_binding(spec.h) == runtime, 'existing runtime changed')
    spec.h.check_roots()


def worker(spec, root, run):
    api, h, ops, d = spec.api, spec.h, spec.ops, spec.d
    d.verify_lane(h)
    frozen = api.read_json(root / 'BINDING.json')
    need(frozen == binding(spec), 'serialized worker binding changed')
    installed = h.install_sources(PROJECT, spec.updates, spec.payloads, run / 'source-backups')
    d.save(run / 'SOURCE_INSTALL.json', {**spec.provenance, 'sources': installed})
    passed, accepted, error = {}, set(), None
    before = None
    try:
        check_installed(spec, frozen['runtime'])
        before = api.context(TARGET_COMMIT, PROJECT, MODULE, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_BEFORE.json', {'provenance': spec.provenance, 'context': before})
        passed[MODULE] = api.normal_one(TARGET_COMMIT, PROJECT, root, MODULE,
                                        spec.graph, spec.sources, h, ops, d)
        api.audit(TARGET_COMMIT, PROJECT, root, passed, spec.graph, spec.sources, h, ops, d, run, accepted)
        check_installed(spec, frozen['runtime'])
        after = api.context(TARGET_COMMIT, PROJECT, MODULE, spec.graph, spec.sources, h, d)
        d.save(run / 'P1_DEPENDENCY_CONTEXT_AFTER.json', {'provenance': spec.provenance, 'context': after})
        need(after == before, 'source/object/trace/configuration/runtime context changed during acceptance')
    except Exception as caught:
        error = str(caught)
        ops.emit('P26_SINGLE_OWNER_HELD_OR_FAILED', module=MODULE, reason=error)
    complete = accepted == {MODULE} and error is None
    result = {**spec.provenance, 'status': api.PASS if complete else 'HELD_OR_FAILED',
              'normal_passed': sorted(passed), 'accepted_owners': sorted(accepted), 'error': error,
              'accepted_for_actual_P1_context_only': complete, 'all_selected_owners_accepted': complete}
    d.save(run / 'RESULT.json', result)
    print(json.dumps(result, sort_keys=True), flush=True)
    return 0 if complete else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target-source-commit', default=TARGET_COMMIT)
    parser.add_argument('--dependency-commit', default=DEPENDENCY_COMMIT)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--config-basis', choices=('runtime', 'source'), default='runtime')
    parser.add_argument('--source-repo', type=Path, default=REPO)
    parser.add_argument('--target-source-repo', type=Path, default=REPO)
    parser.add_argument('--project', type=Path, default=PROJECT)
    parser.add_argument('--inside-lane', action='store_true', help=argparse.SUPPRESS)
    parser.add_argument('--run-dir', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    sys.setrecursionlimit(10000)
    args.source_repo, args.target_source_repo, args.project = (
        p.resolve() for p in (args.source_repo, args.target_source_repo, args.project))
    need(args.config_basis == 'runtime' or (args.check and args.project != PROJECT),
         'source configuration basis is limited to read-only local checks')
    if args.run:
        need(args.source_repo == args.target_source_repo == REPO and args.project == PROJECT,
             'execution is restricted to the existing P1 cloud project/repository')
    spec = inputs(args)
    api, h, ops, d = spec.api, spec.h, spec.ops, spec.d
    root = ROOT / TARGET_COMMIT / DEPENDENCY_COMMIT
    if args.check:
        need(not args.inside_lane and args.run_dir is None, 'invalid check arguments')
        print(json.dumps({**spec.provenance,
              'status': 'SOURCE_CONFIG_ONLY_NOT_CLOUD_READY' if args.config_basis == 'source' else
                        'READ_ONLY_SOURCE_RUNTIME_CHECK_PASS_NOT_ACCEPTANCE',
              'source_installation_performed': False, 'cloud_compilation_performed': False}, sort_keys=True))
        return 0
    if args.inside_lane:
        need(args.run_dir is not None, 'serialized worker requires a run directory')
        run = args.run_dir.resolve()
        need(run.parent == root / 'runs' and re.fullmatch(r'attempt-[0-9]{5}', run.name) and run.is_dir(),
             'invalid run directory')
        return worker(spec, root, run)
    need(args.run_dir is None, 'run-dir requires the serialized worker')
    original = d.original_git_state(REPO)
    d.save(root / 'BINDING.json', binding(spec))
    for path, data in spec.raw.items():
        destination = ('source-configuration/' + path if path in CONFIGS else
                       'e9.py' if path == api.E9 else Path(path).name)
        d.write_frozen(root / 'inputs' / destination, data)
    executed = root / 'executed-driver.py'
    d.write_frozen(executed, Path(__file__).read_bytes())
    run = d.attempt(root / 'runs')
    d.save(run / 'GIT_BEFORE.json', original)
    child = ['python3', '-B', str(executed), '--target-source-commit', TARGET_COMMIT,
             '--dependency-commit', DEPENDENCY_COMMIT, '--run', '--inside-lane', '--run-dir', str(run)]
    try:
        command = ops.run(run, 'serialized-worker', h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        return command['exit_code']
    finally:
        after = d.original_git_state(REPO)
        d.save(run / 'GIT_AFTER.json', after)
        need(after == original, 'original dirty Git source worktree changed')


if __name__ == '__main__':
    raise SystemExit(main())
