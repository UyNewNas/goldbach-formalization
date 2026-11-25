#!/usr/bin/env python3
"""Integrate only two fixed sets of existing proof sources into the current P1 context.

No source installer or cache importer is included. Existing dependency artifacts
are pinned and immutable. Only manifest targets may be compiled, each through the
unchanged Batch13 normal/kernel/full-owned APIs and existing serialized lane.
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
ROOT_BASE = Path('/workspace/p1-complete-proof/20261125-p15-current-context-integration-v1')
ROOT = ROOT_BASE
RUNNER = 'docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py'
API = 'docs/p1/20261125/batch13-repairs/run_repairs.py'
API_COMMIT = '4cea0407c1258eaddd7d4952cffa4aea67310422'
API_SHA = '95cafccabc9867c253bb3147ed80d9b3cc7afffddcd2b2b0be833d40565622ea'
TOOLS = '220c14630ffd266f824bdbf0977147ecb740c0dd'
REVIEW = 'docs/p1/20261125/runtime-configuration/review.json'
REVIEW_SHA = '34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880'
MODULE = re.compile(r"ImbalancedChen(?:\.[A-Za-z_][A-Za-z_0-9']*)+")
SHA256 = re.compile(r'[0-9a-f]{64}')
GROUPS = {'atlas10': {'manifest': 'docs/p1/20261125/p15-atlas-current-context-integration/ATLAS10_MANIFEST.json', 'sha256': '4d8c2a41316590f1cd3103c79faeb412b54923a91bb9537d232252fb5c9a5f3a', 'source_count': 68, 'targets': ['ImbalancedChen.P5OriginalHBMediumChartReserves', 'ImbalancedChen.P5SmoothChartHBDyadicPartition', 'ImbalancedChen.P5SmoothChartPhysicalHBBranch', 'ImbalancedChen.P5ActualMultiGroupHBChartScale', 'ImbalancedChen.P5ActualHBChartEventualClosure', 'ImbalancedChen.P5OriginalChartRoughCutoff', 'ImbalancedChen.P5ExactOriginalSmoothDyadicPartition', 'ImbalancedChen.P5ActualLabelledPrimeSmoothCharts', 'ImbalancedChen.Part3OriginalProperPowerChartCount', 'ImbalancedChen.Part3ActualOriginalProperPowerChartBridge']}, 'p3-20': {'manifest': 'docs/p1/20261125/p15-atlas-current-context-integration/P3_20_MANIFEST.json', 'sha256': 'f36b834f1e34a8ba98e18f8bab6c149a1de9660c6567d5447339f3c25fbb8b23', 'source_count': 77, 'targets': ['ImbalancedChen.Part3BrunWeights', 'ImbalancedChen.Part3CompletedReciprocalWeil', 'ImbalancedChen.Part3LongSlotDistribution', 'ImbalancedChen.Part3OffDiagonalModuli', 'ImbalancedChen.Part3OriginalDyadicChartPartition', 'ImbalancedChen.Part3LongSlotDivisorExpansion', 'ImbalancedChen.Part3SignedModulusPayment', 'ImbalancedChen.Part3SmoothReciprocalWeil', 'ImbalancedChen.Part3TwoLongCompletion', 'ImbalancedChen.Part3LongSlotBrunTransfer', 'ImbalancedChen.Part3TwoLongBrunComparison', 'ImbalancedChen.Part3TwoLongSmooth', 'ImbalancedChen.Part3PrimeProductChartTransfer', 'ImbalancedChen.Part3PrimeProductVonMangoldt', 'ImbalancedChen.Part3ProperPrimePowerCount', 'ImbalancedChen.Part3ProperPowerResidualPayment', 'ImbalancedChen.Part3ProperPowerDyadicBudget', 'ImbalancedChen.Part3ProperPowerOriginalChart', 'ImbalancedChen.Part3ProperPowerLogSaving', 'ImbalancedChen.Part3ProperPowerChartSum']}}


def require(ok, message):
    if not ok:
        raise ValueError(message)


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


def selection(group, requested):
    require(group in GROUPS, 'outside the two fixed integration groups')
    allowed = GROUPS[group]['targets']
    requested = allowed if requested is None else requested
    require(requested and len(requested) == len(set(requested)), 'specify unique targets')
    require(set(requested) <= set(allowed), 'outside the fixed integration target whitelist')
    return [m for m in allowed if m in requested]


def artifact_paths(module):
    require(MODULE.fullmatch(module), 'invalid module name')
    relative = module.replace('.', '/')
    lib = '.lake/build/lib/lean/' + relative
    ir = '.lake/build/ir/' + relative
    return [lib + ext for ext in ('.olean', '.olean.hash', '.olean.private', '.olean.private.hash',
                                  '.olean.server', '.olean.server.hash', '.ilean', '.ilean.hash',
                                  '.trace', '.ir', '.ir.hash', '.ir.sig')] + [
        ir + ext for ext in ('.c', '.c.hash', '.setup.json', '.bc', '.bc.hash', '.o', '.o.hash',
                            '.o.export', '.o.export.hash')]


def module_artifacts(s, module):
    result = {}
    for relative in artifact_paths(module):
        path = PROJECT / relative
        if os.path.lexists(path):
            require(path.is_file() and not path.is_symlink(), 'unexpected artifact entry: ' + relative)
            result[relative] = s.d.fingerprint(path)
        else:
            result[relative] = None
    return result


def require_fresh_owner(module, artifacts):
    present = [path for path, value in artifacts.items() if value is not None]
    require(not present, 'UNEXPECTED_EXISTING_TARGET_ARTIFACT_REQUIRES_INSPECTION: ' +
            module + ': ' + ', '.join(present))


def source_manifest(s, commit, group):
    fixed = GROUPS[group]
    raw = pinned(commit, fixed['manifest'], fixed['sha256'])
    manifest = json.loads(raw)
    require(manifest['schema'] == 'p15_current_context_integration_manifest_v1' and
            manifest['group'] == group and manifest['project'] == str(PROJECT) and
            manifest['targets'] == fixed['targets'] and
            manifest['target_count'] == len(fixed['targets']) and
            manifest['project_module_count'] == fixed['source_count'], 'fixed integration scope differs')
    anchor = manifest['source_anchor']
    anchor_raw = pinned(anchor['commit'], anchor['path'], anchor['sha256'])
    require(len(anchor_raw) == anchor['bytes'], 'source anchor byte count differs')
    document = json.loads(anchor_raw)
    authoritative = document['project_sources'] if group == 'atlas10' else {
        row['module']: row for row in document['project_import_closure']}
    rows = manifest['project_sources']
    require(len(rows) == fixed['source_count'], 'complete source inventory differs')
    graph, sources = {}, {}
    for module, row in rows.items():
        require(MODULE.fullmatch(module) and row['path'] == s.h.module_path(module) and
                SHA256.fullmatch(row['sha256']) and module in authoritative,
                'invalid source identity: ' + module)
        old = authoritative[module]
        require(all(row[k] == old[k] for k in ('path', 'bytes', 'sha256', 'git_blob')) and
                row['imports'] == old['project_imports'] and
                all(dep in rows for dep in row['imports']), 'frozen source anchor differs: ' + module)
        payload = git_file(commit, row['path'])
        blob = hashlib.sha1(b'blob ' + str(len(payload)).encode() + b'\0' + payload).hexdigest()
        require(len(payload) == row['bytes'] and s.api.sha(payload) == row['sha256'] and
                blob == row['git_blob'] and s.h.imports(payload) == row['all_imports'] and
                [dep for dep in row['all_imports'] if dep.startswith('ImbalancedChen.')] == row['imports'],
                'committed source bytes/imports differ: ' + module)
        graph[module], sources[module] = row['imports'], row['sha256']
    targets = set(manifest['targets'])
    fixed_dependencies = manifest['fixed_dependencies']
    require(set(graph) == s.h.closure(graph, manifest['targets']) and
            set(fixed_dependencies) == set(graph) - targets and
            len(fixed_dependencies) == manifest['fixed_dependency_count'] and
            not (s.h.closure(graph, fixed_dependencies) & targets),
            'dependency graph or preserved-object boundary differs')
    for module, artifacts in fixed_dependencies.items():
        require(artifacts.get('.olean') is not None and artifacts.get('.trace') is not None,
                'missing pinned existing dependency: ' + module)
        for ext, value in artifacts.items():
            require(ext in ('.olean', '.trace', '.ilean', '.olean.private', '.olean.server') and
                    (value is None or (isinstance(value['bytes'], int) and value['bytes'] >= 0 and
                                       SHA256.fullmatch(value['sha256']))), 'invalid dependency artifact pin')
    historical = []
    for row in manifest['historical_acceptance_evidence']:
        payload = pinned(row['commit'], row['path'], row['sha256'])
        require(len(payload) == row['bytes'], 'historical evidence byte count differs')
        historical.append(row)
    return manifest, graph, sources, {'manifest': {'path': fixed['manifest'], 'bytes': len(raw),
                                                  'sha256': s.api.sha(raw)},
                                      'source_anchor': anchor, 'historical_evidence': historical}


def snapshot(s, spec):
    configs = spec.review['runtime_configuration_bindings']
    configuration = {p: regular_fingerprint(s, PROJECT / p) for p in configs}
    require(configuration == configs and not os.path.lexists(PROJECT / 'lakefile.lean'),
            'runtime configuration differs')
    runtime = s.d.runtime_binding(s.h)
    require(runtime == spec.review['existing_runtime_bindings'], 'runtime binding differs')
    protected = {m: file_binding(PROJECT / s.h.module_path(m)) for m in s.h.FOUR_ROOTS}
    require(protected == s.h.FOUR_ROOTS, 'protected original roots differ')
    sources = {m: file_binding(PROJECT / s.h.module_path(m)) for m in spec.graph}
    require(sources == spec.sources, 'installed source context differs')
    dependencies = {}
    for module, expected in spec.manifest['fixed_dependencies'].items():
        observed = module_artifacts(s, module)
        stem = '.lake/build/lib/lean/' + module.replace('.', '/')
        require(all(observed[stem + ext] == value for ext, value in expected.items()),
                'PRESERVED_DEPENDENCY_PIN_DIFFERS: ' + module)
        dependencies[module] = observed
    return {'project_sources': sources, 'protected_roots': protected, 'configuration': configuration,
            'runtime': runtime, 'preserved_dependency_artifacts': dependencies,
            'committed_inputs': spec.input_bindings}


def existing_owner(s, commit, spec, module):
    folder = ROOT / commit / module
    artifacts = module_artifacts(s, module)
    normal_path = folder / 'normal' / module / 'NORMAL_PASS.json'
    if not os.path.lexists(normal_path):
        require_fresh_owner(module, artifacts)
        return {'status': 'MISSING_WITHOUT_NORMAL_RECEIPT', 'artifacts': artifacts}
    normal = s.api.read_json(normal_path)
    s.api.normal_valid(commit, PROJECT, module, normal,
                       s.api.context(commit, PROJECT, module, spec.graph, spec.sources, s.h, s.d), s.h, s.d)
    return {'status': 'BOUND_CURRENT_NORMAL_RECEIPT', 'artifacts': artifacts, 'normal': normal}


def require_completed_existing_owner(s, commit, spec, module, state):
    require(state['status'] == 'BOUND_CURRENT_NORMAL_RECEIPT',
            'NONSELECTED_TARGET_DEPENDENCY_REQUIRES_OWN_COMPLETE_ACCEPTANCE: ' + module)
    folder = ROOT / commit / module
    for plan in (folder / 'plans').glob('*.json'):
        require((folder / 'audits' / plan.stem / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(plan))
    accepted = set()
    for directory in (folder / 'audits').glob('*'):
        require(directory.is_dir() and not directory.is_symlink() and
                (directory / 'lane-0/VALIDATION_RESULTS.json').is_file(),
                'PARTIAL_AUDIT_REQUIRES_INSPECTION: ' + str(directory))
        accepted.update(s.api.audit_valid(commit, PROJECT, directory,
            s.api.read_json(directory / 'AUDIT_PLAN.json'), {module: state['normal']},
            spec.graph, spec.sources, s.h, s.d))
    require(accepted == {module}, 'NONSELECTED_TARGET_DEPENDENCY_NOT_ACCEPTED: ' + module)


def preflight(s, commit, group, selected):
    require(subprocess.check_output(['git', 'cat-file', '-t', commit], cwd=REPO).strip() == b'commit',
            'source-commit must name a commit')
    executed = Path(__file__).read_bytes()
    require(executed == git_file(commit, RUNNER), 'executed runner differs from committed source')
    review_raw = pinned(commit, REVIEW, REVIEW_SHA)
    review = json.loads(review_raw)
    for path, expected in review['source_configuration_bindings'].items():
        raw = git_file(commit, path)
        require({'bytes': len(raw), 'sha256': s.api.sha(raw)} == expected,
                'published source configuration differs: ' + path)
    manifest, graph, sources, inputs = source_manifest(s, commit, group)
    actual_graph, actual = s.h.project_graph(PROJECT, manifest['targets'])
    require(actual_graph == graph and {m: row['sha256'] for m, row in actual.items()} == sources,
            'complete installed source graph differs')
    spec = SimpleNamespace(group=group, manifest=manifest, graph=graph, sources=sources, review=review,
        order=s.d.compile_order([], selected, graph), input_bindings={**inputs, 'source_commit': commit,
        'runtime_review': {'path': REVIEW, 'bytes': len(review_raw), 'sha256': s.api.sha(review_raw)},
        'runner': {'path': RUNNER, 'bytes': len(executed), 'sha256': s.api.sha(executed)}})
    spec.baseline = snapshot(s, spec)
    spec.initial_owners = {m: existing_owner(s, commit, spec, m) for m in manifest['targets']}
    required_unselected = (s.h.closure(graph, selected) & set(manifest['targets'])) - set(selected)
    for module in sorted(required_unselected):
        require_completed_existing_owner(s, commit, spec, module, spec.initial_owners[module])
    return spec


def acceptance_binding(s, commit, module):
    folder = ROOT / commit / module
    normal = folder / 'normal' / module / 'NORMAL_PASS.json'
    audits = []
    for directory in sorted((folder / 'audits').glob('*')):
        result = directory / 'lane-0/VALIDATION_RESULTS.json'
        plan = directory / 'AUDIT_PLAN.json'
        audits.append({'plan': {'path': str(plan), **regular_fingerprint(s, plan)},
                       'result': {'path': str(result), **regular_fingerprint(s, result)}})
    require(audits, 'missing completed owner audit')
    return {'module': module, 'normal_receipt': {'path': str(normal), **regular_fingerprint(s, normal)},
            'audits': audits, 'source_plus_five_outputs': s.d.snapshot(PROJECT, module),
            'all_observed_target_artifacts': module_artifacts(s, module)}


def direct_import_readiness(s, spec, module, run):
    imports = spec.manifest['project_sources'][module]['all_imports']
    require(imports and all(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", dep) for dep in imports),
            'EMPTY_OR_UNKNOWN_DIRECT_IMPORT_SET_REQUIRES_INSPECTION: ' + module)
    command = s.ops.run(run / module, 'direct-import-stock-readiness',
        s.h.guard(0, ['lake', '--no-build', 'build'] + ['+' + dep + ':olean' for dep in imports]), cwd=PROJECT)
    require(command['exit_code'] == 0 and command['actual_built_modules'] == [] and
            command['actual_failed_modules'] == [], 'DIRECT_IMPORTS_NOT_READY_NO_REBUILD_ALLOWED: ' + module)
    return command


def worker(s, commit, group, selected, run):
    s.d.verify_lane(s.h)
    result = {'source_commit': commit, 'group': group, 'targets': selected, 'accepted_owners': [],
              'failures': {}, 'integration_acceptance_bindings': {}, 'direct_import_readiness': {},
              'whole_P1_complete': False,
              'acceptance_class': 'CURRENT_P1_ENVIRONMENT_INTEGRATION_OF_EXISTING_PROOF_SOURCES',
              'new_mathematical_proofs': 0, 'historical_acceptance_invalidated': False,
              'existing_dependency_rebuild_allowed': False, 'old_trace_rewrites_requested': False}
    spec = None
    try:
        spec = preflight(s, commit, group, selected)
        result['targets'] = spec.order
        s.d.save(run / 'CONTEXT_BEFORE.json', spec.baseline)
        s.d.save(run / 'COMMITTED_INPUT_BINDINGS.json', spec.input_bindings)
        for module in spec.order:
            require(snapshot(s, spec) == spec.baseline, 'source/runtime/preserved dependency context changed')
            other_owners = {m: module_artifacts(s, m) for m in spec.manifest['targets'] if m != module}
            try:
                result['direct_import_readiness'][module] = direct_import_readiness(s, spec, module, run)
                require(snapshot(s, spec) == spec.baseline and
                        {m: module_artifacts(s, m) for m in other_owners} == other_owners,
                        'preserved dependency or another target changed during direct-import readiness')
                # The immutable normal_one checks guarded stock --no-build on
                # every direct dependency before its one permitted owner build.
                run_owner(s, commit, ROOT / commit, run, module, spec.graph, spec.sources)
                require(snapshot(s, spec) == spec.baseline, 'preserved context changed during owner acceptance')
                require({m: module_artifacts(s, m) for m in other_owners} == other_owners,
                        'another target artifact changed during this owner acceptance')
                result['integration_acceptance_bindings'][module] = acceptance_binding(s, commit, module)
                result['accepted_owners'].append(module)
                s.ops.emit('CURRENT_CONTEXT_OWNER_ACCEPTED', group=group, module=module)
            except Exception as error:
                result['failures'][module] = str(error)
                s.ops.emit('CURRENT_CONTEXT_OWNER_HELD_OR_FAILED', group=group, module=module, reason=str(error))
                break
        if not result['failures']:
            before = {m: module_artifacts(s, m) for m in spec.manifest['targets']}
            stock = s.ops.run(run, 'final-stock-readiness', s.h.guard(0, ['lake', '--no-build', 'build'] +
                              ['+' + m + ':olean' for m in spec.order]), cwd=PROJECT)
            require(stock['exit_code'] == 0 and stock['actual_built_modules'] == [] and
                    stock['actual_failed_modules'] == [], 'FINAL_STOCK_READINESS_FAILED_NO_REBUILD_ALLOWED')
            require({m: module_artifacts(s, m) for m in spec.manifest['targets']} == before,
                    'target artifacts changed during final stock readiness')
            result['final_stock_readiness'] = stock
    except Exception as error:
        result['context_error'] = str(error)
    finally:
        if spec is not None:
            try:
                after = snapshot(s, spec)
                s.d.save(run / 'CONTEXT_AFTER.json', after)
                require(after == spec.baseline, 'source/runtime/preserved dependency context changed')
            except Exception as error:
                result['final_context_error'] = str(error)
    s.d.save(run / 'WORKER_RESULT.json', result)
    return int(bool(result['failures'] or result.get('context_error') or result.get('final_context_error')))


def main():
    global ROOT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-commit', required=True)
    parser.add_argument('--group', choices=tuple(GROUPS), required=True)
    parser.add_argument('--targets', nargs='+')
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', action='store_true')
    mode.add_argument('--run', action='store_true')
    parser.add_argument('--inside-lane', type=Path, help=argparse.SUPPRESS)
    args = parser.parse_args()
    commit = args.source_commit
    require(re.fullmatch('[0-9a-f]{40}', commit), 'source-commit requires a full lowercase SHA')
    selected = selection(args.group, args.targets)
    ROOT = ROOT_BASE / args.group
    s = helpers()
    if args.check:
        require(args.inside_lane is None, 'check does not use a lane')
        spec = preflight(s, commit, args.group, selected)
        print(json.dumps({'status': 'FIXED_SOURCES_RUNTIME_EXISTING_OBJECTS_AND_TARGET_ABSENCE_OR_PROVENANCE_VERIFIED',
                          'group': args.group, 'source_commit': commit, 'source_count': len(spec.graph),
                          'targets': spec.order, 'preserved_dependency_count': len(spec.manifest['fixed_dependencies']),
                          'committed_inputs': spec.input_bindings, 'stock_readiness_performed': False,
                          'fresh_integration_acceptance': False, 'new_mathematical_proofs': 0}))
        return 0
    base = ROOT / commit
    if args.inside_lane:
        run = args.inside_lane.resolve()
        require(run.parent == base / 'runs' and re.fullmatch('attempt-[0-9]{5}', run.name) and
                run.is_dir(), 'invalid worker directory')
        return worker(s, commit, args.group, selected, run)
    # Refuse unknown target objects or source/context drift before opening a lane.
    preflight(s, commit, args.group, selected)
    run = s.d.attempt(base / 'runs')
    result = {'source_commit': commit, 'group': args.group, 'targets': selected,
              'accepted_owners': [], 'failures': {}, 'whole_P1_complete': False}
    try:
        s.d.save(run / 'GIT_BEFORE.json', s.d.original_git_state(REPO))
        executed = run / 'executed-driver.py'
        s.d.write_frozen(executed, Path(__file__).read_bytes())
        child = ['python3', '-B', str(executed), '--source-commit', commit, '--group', args.group,
                 '--targets', *selected, '--run', '--inside-lane', str(run)]
        command = s.ops.run(run, 'serialized-worker',
                           s.h.serialize(0, run / 'VALIDATION_LANE.json', child), relay=True)
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
    success = (set(result['accepted_owners']) == set(selected) and not result['failures'] and
               not any(key in result for key in ('context_error', 'final_context_error', 'dispatch_error', 'git_error')))
    result['all_selected_integration_owners_accepted'] = success
    s.d.save(run / 'RESULT.json', result)
    s.ops.emit('P15_CURRENT_CONTEXT_INTEGRATION_RESULT', path=str(run / 'RESULT.json'), **result)
    return int(not success)


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    raise SystemExit(main())
