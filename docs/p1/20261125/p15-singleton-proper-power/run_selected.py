#!/usr/bin/env python3
"""Check or validate new singleton owners on the unchanged existing member lane.

--check reads committed manifests, installed sources, runtime bindings and existing
objects only; it does not claim stock Lake readiness or fresh acceptance. --run
uses the existing serializer, requires guarded --no-build dependency readiness,
and sends only the selected new owners through the unchanged Batch13 normal and
full-owned audit APIs. Cache/source adoption is deliberately outside this driver.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
PROJECT = Path('/workspace/blue-member-build')
REPO = Path('/workspace/goldbach-formalization')
ROOT = Path('/workspace/p1-complete-proof/20261125-p15-singleton-proper-power-v1')
API = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
PREFIX = 'docs/p1/20261125/p15-singleton-proper-power/'
CLOSURE = PREFIX + 'SOURCE_CLOSURE.json'
P3_REUSE = PREFIX + 'P3_REUSE.json'
# This is the already reviewed source/object reuse manifest, not a newly authored
# cache acceptance record. Historical object identities cannot change silently.
P3_REUSE_SHA = '1aab54f7655ca68ae24294d49eff3c1f08455d3c31982c78d1e017888bc1316b'
P3_SOURCE_COMMIT = '70e8f69cbbacb2b851147a5fa51948a106beeca7'
P3_TERMINAL = 'ImbalancedChen.Part3ProperPowerChartSum'
TARGETS = tuple('ImbalancedChen.' + name for name in """
P1OriginalSingletonPointwiseData
P1OriginalSingletonProperPower
P1Full87TrueDPolicyDelta
P1Full87TrueDUnitBound
P1OriginalHistoricalMiddlePointwiseData
P1OriginalHistoricalProperPower
""".split())
MODULE = re.compile(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9']*)+")
SHA256 = re.compile(r'[0-9a-f]{64}')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def selection(requested):
    require(requested and len(requested) == len(set(requested)), 'specify unique targets')
    unknown = set(requested) - set(TARGETS)
    require(not unknown, 'outside the six new singleton-owner selection: ' + ', '.join(sorted(unknown)))
    return [m for m in TARGETS if m in requested]


def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def pinned(commit, path, digest):
    raw = git_file(commit, path)
    require(hashlib.sha256(raw).hexdigest() == digest, 'published pin differs: ' + path)
    return raw


def helpers():
    raw = pinned(API_COMMIT, API, API_SHA)
    api = ModuleType('published_batch13')
    api.__file__ = API
    exec(compile(raw, API, 'exec'), api.__dict__)
    require((api.REPO, api.PROJECT, api.TOOLS) == (REPO, PROJECT, TOOLS), 'unexpected helper environment')
    code = {p: pinned(TOOLS, p, sha) for p, sha in api.PINS.items()}
    return SimpleNamespace(api=api, h=api.load(code[api.HELPER], 'batch5'),
                           ops=api.load(code[api.OPS], 'batch6'),
                           d=api.load(code[api.PRIMITIVES], 'primitives'), e9=code[api.E9])


def file_binding(path):
    require(path.is_file() and not path.is_symlink(), 'expected regular file: ' + str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()


def regular_fingerprint(s, path):
    require(path.is_file() and not path.is_symlink(),
            'expected existing regular cache file; adoption is separate: ' + str(path))
    return s.d.fingerprint(path)


def source_manifest(s, commit, selected):
    raw = git_file(commit, CLOSURE)
    manifest = json.loads(raw)
    require(manifest.get('schema') == 'p15_singleton_proper_power_source_closure_v1' and
            manifest.get('missing') == [], 'source closure schema or missing sources differs')
    declared = manifest.get('targets')
    require(isinstance(declared, list) and declared and
            all(isinstance(m, str) for m in declared) and len(declared) == len(set(declared)) and
            set(declared) <= set(TARGETS), 'source closure owner scope differs')
    require(set(selected) <= set(declared), 'selected owner absent from committed SOURCE_CLOSURE')
    records = manifest.get('project_sources')
    require(isinstance(records, dict) and records and
            all(isinstance(m, str) and MODULE.fullmatch(m) for m in records),
            'invalid project source inventory')
    graph, sources = {}, {}
    for module, row in records.items():
        require(isinstance(row, dict) and row.get('path') == s.h.module_path(module) and
                isinstance(row.get('sha256'), str) and SHA256.fullmatch(row['sha256']) and
                isinstance(row.get('imports'), list) and
                all(isinstance(dep, str) and dep in records for dep in row['imports']),
                'invalid source path/hash/import binding: ' + module)
        graph[module] = row['imports']
        sources[module] = row['sha256']
    require(set(graph) == s.h.closure(graph, declared),
            'SOURCE_CLOSURE is not exactly the declared owner import closure')
    for module in graph:
        payload = git_file(commit, s.h.module_path(module))
        published_imports = [dep for dep in s.h.imports(payload)
                             if dep.startswith('ImbalancedChen.')]
        require(s.api.sha(payload) == sources[module] and published_imports == graph[module],
                'committed source/hash/import graph differs: ' + module)
    return manifest, graph, sources, {'path': CLOSURE, 'bytes': len(raw),
                                    'sha256': s.api.sha(raw)}


def reuse_manifest(s, commit, graph, sources):
    raw = pinned(commit, P3_REUSE, P3_REUSE_SHA)
    manifest = json.loads(raw)
    require(manifest.get('schema') == 'p15-p3-proper-power-reuse-v1' and
            manifest.get('selected_mathematical_source_commit') == P3_SOURCE_COMMIT,
            'P3 reuse source anchor differs')
    rows = manifest['canonical_additions']
    require(len(rows) == 19 and len({row['module'] for row in rows}) == 19 and
            not ({row['module'] for row in rows} & set(TARGETS)),
            'P3 supplier scope differs')
    suppliers = {}
    for row in rows:
        module = row['module']
        binding = row['object_reuse_binding']
        require(module in graph and row['source_commit'] == P3_SOURCE_COMMIT and
                row['path'] == s.h.module_path(module) and row['sha256'] == sources[module] and
                row['project_imports'] == graph[module] and
                binding['source_hash_matches_selected_source'] is True and
                SHA256.fullmatch(binding['expected_olean_sha256']),
                'P3 source/object identity differs: ' + module)
        payload = git_file(commit, row['path'])
        require(len(payload) == row['bytes'], 'P3 source byte count differs: ' + module)
        suppliers[module] = {'source_sha256': row['sha256'], 'source_bytes': row['bytes'],
                             'expected_olean_sha256': binding['expected_olean_sha256'],
                             'receipt_key': binding['receipt_key']}
    closure_rows = manifest['project_import_closure']
    p3_modules = {row['module'] for row in closure_rows}
    require(len(closure_rows) == len(p3_modules) == 77 and set(suppliers) <= p3_modules and
            P3_TERMINAL in graph and s.h.closure(graph, [P3_TERMINAL]) == p3_modules,
            'P3 full import closure differs')
    for row in closure_rows:
        module = row['module']
        require(row['path'] == s.h.module_path(module) and row['sha256'] == sources[module] and
                row['project_imports'] == graph[module],
                'P3 shared source/import context differs: ' + module)
    return suppliers, p3_modules, {'path': P3_REUSE, 'bytes': len(raw),
                                  'sha256': s.api.sha(raw)}


def cache_snapshot(s, fixed_dependencies, suppliers):
    objects = {}
    for module in sorted(fixed_dependencies):
        stem = '.lake/build/lib/lean/' + module.replace('.', '/')
        for suffix in ('.olean', '.trace'):
            relative = stem + suffix
            objects[relative] = regular_fingerprint(s, PROJECT / relative)
    supplier_objects = {}
    for module, expected in sorted(suppliers.items()):
        stem = '.lake/build/lib/lean/' + module.replace('.', '/')
        observed = objects[stem + '.olean']
        require(observed['sha256'] == expected['expected_olean_sha256'],
                'P3_ACCEPTED_OLEAN_HASH_MISMATCH: ' + module)
        # The reviewed receipts record .olean only. An unbound more-private part
        # must not replace the accepted object selected by Lean/leanchecker.
        for suffix in ('.olean.private', '.olean.server'):
            require(not os.path.lexists(PROJECT / (stem + suffix)),
                    'P3_UNBOUND_OLEAN_PART_REQUIRES_ADOPTION_REVIEW: ' + stem + suffix)
        supplier_objects[module] = {'expected_olean_sha256': expected['expected_olean_sha256'],
                                    'observed': observed,
                                    'receipt_key': expected['receipt_key']}
    return {'dependency_objects_and_traces': objects,
            'historically_bound_p3_objects': supplier_objects}


def snapshot(s, modules, review, fixed_dependencies, suppliers, input_bindings):
    h, d = s.h, s.d
    configs = review['runtime_configuration_bindings']
    configuration = {p: d.fingerprint(PROJECT / p) for p in configs}
    require(configuration == configs and not os.path.lexists(PROJECT / 'lakefile.lean') and
            not any((PROJECT / p).is_symlink() for p in configs), 'runtime configuration differs')
    runtime = d.runtime_binding(h)
    require(runtime == review['existing_runtime_bindings'], 'runtime binding differs')
    protected = {m: file_binding(PROJECT / h.module_path(m)) for m in h.FOUR_ROOTS}
    require(protected == h.FOUR_ROOTS, 'protected original roots differ')
    return {'project_sources': {m: file_binding(PROJECT / h.module_path(m)) for m in modules},
            'protected_roots': protected, 'configuration': configuration, 'runtime': runtime,
            'committed_input_bindings': input_bindings,
            **cache_snapshot(s, fixed_dependencies, suppliers)}


def preflight(s, commit, selected):
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source-commit must name a commit')
    review_raw = pinned(commit, REVIEW, REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        source = git_file(commit, path)
        require({'bytes': len(source), 'sha256': s.api.sha(source)} == expected,
                'published configuration differs: ' + path)
    manifest, graph, sources, closure_binding = source_manifest(s, commit, selected)
    actual_graph, actual = s.h.project_graph(PROJECT, manifest['targets'])
    require(actual_graph == graph, 'installed project graph differs from committed SOURCE_CLOSURE')
    require({m: row['sha256'] for m, row in actual.items()} == sources,
            'installed source hashes differ from committed SOURCE_CLOSURE')
    all_suppliers, p3_modules, reuse_binding = reuse_manifest(s, commit, graph, sources)
    # Validate the complete committed source/P3 identity above, but read cache
    # objects only for dependencies of the requested owner subset. Independent
    # owners must not wait for a P3 cache that they do not import.
    active_dependency_closure = s.h.closure(graph, selected)
    suppliers = {m: row for m, row in all_suppliers.items() if m in active_dependency_closure}
    fixed_dependencies = active_dependency_closure - set(selected)
    input_bindings = {'source_commit': commit, 'source_closure': closure_binding,
                      'p3_reuse': reuse_binding,
                      'runtime_review': {'path': REVIEW, 'bytes': len(review_raw),
                                         'sha256': s.api.sha(review_raw)}}
    baseline = snapshot(s, graph, review, fixed_dependencies, suppliers, input_bindings)
    require(baseline['project_sources'] == sources, 'sources changed during preflight')
    order = s.d.compile_order([], selected, graph)
    # Nonselected direct dependencies must already be ready. Selected owner
    # dependencies are compiled only in the unchanged topological owner loop.
    readiness_targets = sorted(set(suppliers) | {dep for m in selected for dep in graph[m]
                                               if dep not in selected})
    return SimpleNamespace(review=review, graph=graph, sources=sources, baseline=baseline,
                           order=order, suppliers=suppliers, fixed_dependencies=fixed_dependencies,
                           input_bindings=input_bindings, readiness_targets=readiness_targets,
                           active_dependency_closure=active_dependency_closure,
                           total_verified_p3_suppliers=len(all_suppliers),
                           active_p3_module_count=len(p3_modules & active_dependency_closure))


def current_snapshot(s, spec):
    return snapshot(s, spec.graph, spec.review, spec.fixed_dependencies,
                    spec.suppliers, spec.input_bindings)


def dependency_readiness(s, spec, run):
    require(current_snapshot(s, spec) == spec.baseline,
            'dependency context changed before stock readiness')
    command = s.ops.run(run, 'dependency-stock-readiness',
                        s.h.guard(0, ['lake', '--no-build', 'build'] +
                                  ['+' + m + ':olean' for m in spec.readiness_targets]), cwd=PROJECT)
    require(command['exit_code'] == 0 and command['actual_built_modules'] == [] and
            command['actual_failed_modules'] == [],
            'DEPENDENCIES_NOT_READY_NO_REBUILD_ALLOWED: cache adoption is a separate step')
    require(current_snapshot(s, spec) == spec.baseline,
            'dependency objects/traces changed during stock readiness')
    result = {'status': 'EXISTING_DEPENDENCIES_READY_WITHOUT_REBUILD',
              'targets': spec.readiness_targets, 'command': command,
              'source_and_object_inputs': spec.input_bindings,
              'p3_supplier_count': len(spec.suppliers),
              'fresh_dependency_acceptance': False, 'whole_P1_complete': False}
    s.d.save(run / 'DEPENDENCY_READINESS.json', result)
    return result


def run_owner(s, commit, base, run, m, graph, sources):
    folder = base / m
    s.d.write_frozen(folder / 'inputs/e9.py', s.e9)
    # A different Git commit can have the identical proof/dependency context.
    # Hold its retained computation for inspection; the pinned API still owns
    # receipt validation, and this wrapper never rebases an acceptance receipt.
    previous = [p / m for p in ROOT.iterdir()
                if p.is_dir() and p.name != commit and re.fullmatch('[0-9a-f]{40}', p.name)
                and (p / m).is_dir()]
    normal_dir = folder / 'normal' / m
    if not os.path.lexists(normal_dir / 'NORMAL_PASS.json') and any(normal_dir.glob('attempt-*/normal-started.json')):
        previous.append(folder)
    if previous:
        current = s.api.context(commit, PROJECT, m, graph, sources, s.h, s.d)
        current = {k: v for k, v in current.items() if k != 'source_commit'}
        for old in previous:
            normal = old / 'normal' / m
            bindings = []
            receipt = normal / 'NORMAL_PASS.json'
            if receipt.is_file():
                bindings.append((receipt, json.loads(receipt.read_bytes())['dependency_context']))
            for started in normal.glob('attempt-*/normal-started.json'):
                context = started.parent / 'CONTEXT_BEFORE.json'
                require(context.is_file(), 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(started))
                bindings.append((started, json.loads(context.read_bytes())))
            for path, binding in bindings:
                identity = {k: v for k, v in binding.items() if k != 'source_commit'}
                require(identity.keys() == current.keys() and binding.get('source_commit') == old.parent.name,
                        'RETAINED_HISTORY_REQUIRES_INSPECTION: incomplete or misbound context in ' + str(path))
                require(identity != current, 'RETAINED_HISTORY_REQUIRES_INSPECTION: ' + str(path))
            require(bindings or (not any((old / 'plans').glob('*.json')) and
                                 not any((old / 'audits').glob('*'))),
                    'RETAINED_HISTORY_REQUIRES_INSPECTION: missing normal context in ' + str(old))
    # Preserve a partial audit even if its normal later becomes unavailable.
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    for directory in (folder / 'audits').glob('*'):
        require((directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
    passed = s.api.normal_one(commit, PROJECT, folder, m, graph, sources, s.h, s.ops, s.d)
    accepted = set()
    s.api.audit(commit, PROJECT, folder, {m: passed}, graph, sources, s.h, s.ops,
                s.d, run / m, accepted)
    require(accepted == {m}, 'owner missing from validated audit receipt')


def worker(s, commit, selected, run):
    s.d.verify_lane(s.h)
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [],
              'failures': {}, 'whole_P1_complete': False,
              'dependency_rebuild_requested': False, 'fresh_dependency_acceptance_requested': False}
    try:
        spec = preflight(s, commit, selected)
        result['targets'] = spec.order
        s.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
        s.d.save(run / 'COMMITTED_INPUT_BINDINGS.json', spec.input_bindings)
        result['dependency_readiness'] = dependency_readiness(s, spec, run)
        for m in spec.order:
            try:
                require(current_snapshot(s, spec) == spec.baseline,
                        'source, runtime or fixed dependency context changed')
                run_owner(s, commit, ROOT / commit, run, m, spec.graph, spec.sources)
                require(current_snapshot(s, spec) == spec.baseline,
                        'source, runtime or fixed dependency context changed during owner acceptance')
                result['accepted_owners'].append(m)
                s.ops.emit('OWNER_ACCEPTED', module=m)
            except Exception as error:
                result['failures'][m] = str(error)
                s.ops.emit('OWNER_HELD_OR_FAILED', module=m, reason=str(error))
        after = current_snapshot(s, spec)
        s.d.save(run / 'CONTEXT_AFTER.json', after)
        require(after == spec.baseline, 'source, runtime or fixed dependency context changed')
    except Exception as error:
        result['context_error'] = str(error)
    s.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('context_error')))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--targets', nargs='+', required=True)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    require(re.fullmatch('[0-9a-f]{40}', commit), 'source-commit requires a full lowercase SHA')
    selected = selection(args.targets)
    s = helpers()
    if args.check:
        require(args.inside_lane is None, 'check does not use a lane')
        spec = preflight(s, commit, selected)
        print(json.dumps({'status': 'STATIC_SOURCE_RUNTIME_AND_DEPENDENCY_OBJECTS_VERIFIED',
                          'source_commit': commit, 'source_count': len(spec.graph), 'targets': spec.order,
                          'active_dependency_count': len(spec.active_dependency_closure),
                          'verified_p3_suppliers': spec.total_verified_p3_suppliers,
                          'active_p3_suppliers': len(spec.suppliers),
                          'active_p3_module_count': spec.active_p3_module_count,
                          'fixed_dependency_count': len(spec.fixed_dependencies),
                          'committed_input_bindings': spec.input_bindings,
                          'stock_readiness_performed': False, 'fresh_owner_acceptance': False}))
        return 0
    base = ROOT / commit
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name)
                and run.is_dir(), 'invalid worker directory')
        return worker(s, commit, selected, run)
    run = s.d.attempt(base / 'runs')
    result = {'source_commit': commit, 'targets': selected, 'accepted_owners': [],
              'failures': {}, 'whole_P1_complete': False}
    try:
        before = s.d.original_git_state(REPO)
        s.d.save(run / 'GIT_BEFORE.json', before)
        executed = run / 'executed-driver.py'
        s.d.write_frozen(executed, Path(__file__).read_bytes())
        child = ['python3', '-B', str(executed), '--source-commit', commit, '--targets',
                 *selected, '--run', '--inside-lane', str(run)]
        command = s.ops.run(run, 'serialized-worker', s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
        if (run / 'WORKER_RESULT.json').is_file():
            result.update(s.api.read_json(run / 'WORKER_RESULT.json'))
        result['worker_exit_code'] = command['exit_code']
        require(command['exit_code'] == 0, 'serialized worker exited ' + str(command['exit_code']))
    except Exception as error:
        result['dispatch_error'] = str(error)
    finally:
        try:
            after = s.d.original_git_state(REPO)
            s.d.save(run / 'GIT_AFTER.json', after)
            require(after == s.api.read_json(run / 'GIT_BEFORE.json'), 'original dirty Git state changed')
        except Exception as error:
            result['git_error'] = str(error)
    success = (set(result['accepted_owners']) == set(selected) and not result['failures']
               and not any(key in result for key in ('context_error', 'dispatch_error', 'git_error')))
    result['all_selected_owners_accepted'] = success
    s.d.save(run / 'RESULT.json', result)
    s.ops.emit('P15_SINGLETON_RESULT', path=str(run / 'RESULT.json'), **result)
    return int(not success)


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
