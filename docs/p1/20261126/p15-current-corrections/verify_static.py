#!/usr/bin/env python3
"""Pure Python/Git source checks and isolated fixtures; no driver main or Lean."""
from copy import deepcopy
from functools import lru_cache
from pathlib import Path
from types import ModuleType, SimpleNamespace
import ast
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
ANCHOR = '1103fd45507a5889d79ba1629cc36ae0e69a9672'
PRIOR_B = '3d292e4cd193ab422ca990e80a25165d5aca33a1'
PRIOR_D = '7ca00b5fcc24e188a53d3a645808d388a5b9e6d1'
D_RUNNER_SHA = '035798dde6cf355355912c60e5c23805d07b201a6ddc0ffe1115aaff3da5167b'
D_MANIFEST_SHA = 'a4af2ccc0ec40e955e5138ba1304cd226dcf39d7106ce2419929ae7047258565'
E_REPAIR = {'commit': '1103fd45507a5889d79ba1629cc36ae0e69a9672', 'path': 'docs/p1/20261126/p15-qualified-dyadic-repair/REPAIR_MANIFEST.json', 'bytes': 21111, 'sha256': '012909e00c13fa1bde452a5c6c12f28eb3a066a339b8a5a022574a9759935ce6'}
F_SOURCE_CHANGES = ['ImbalancedChen.P5OriginalPrimeChartHBWitnesses', 'ImbalancedChen.P5LicensedOriginalIntegerProfile', 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward', 'ImbalancedChen.Part3AllKLambdaChartCorrection', 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime']
PUBLICATION_CHECK_BEFORE = "public_binding['commit'] == SOURCE_ANCHOR"
PUBLICATION_CHECK_AFTER = "public_binding['commit'] == '545566753bae9464560a871bea87ea663f90aa53'"
B_RUNNER_SHA = 'ad45eb501f9a89ce1e594497a7105e4f3fac3587963e9249f40021691a82d725'
B_MANIFEST_SHA = '198861fae512aa5213a1e779bac287b5bc5551991f4e7508e4d51fe819755d73'
OLD_RUNNER = 'docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py'
OLD_RUNNER_SHA = '81b9e49db7b5c9585f6d5bef12f383898c8a8f8f4ff65786d2cb22e4b3316af0'
UNCHANGED = ['require', 'git_file', 'pinned', 'helpers', 'file_binding', 'regular_fingerprint',
    'run_owner', 'artifact_paths', 'module_artifacts', 'require_fresh_owner', 'existing_owner',
    'require_completed_existing_owner', 'acceptance_binding', 'direct_import_readiness']
CASES = []


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


@lru_cache(None)
def git_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def pin(path):
    raw = path.read_bytes()
    return {'bytes': len(raw), 'sha256': sha(raw)}


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph[module])
    return seen


def imports(raw):
    return [module for line in re.findall(r'^import\s+([^\n]+)$', raw.decode(), re.M) for module in line.split()]


def functions(raw):
    return {node.name: node for node in ast.parse(raw).body if isinstance(node, ast.FunctionDef)}


def module_from(path, name):
    module = ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def case(name, action, reject=False):
    try:
        value = action()
    except (ValueError, AssertionError, KeyError) as error:
        need(reject, name + ': ' + str(error))
        reason = re.sub(re.escape(tempfile.gettempdir()) + r'/p15-correction-fixture-[^/\s]+',
                        '<isolated-fixture>', str(error))
        CASES.append({'case': name, 'result': 'EXPECTED_HOLD', 'reason': reason})
        return None
    need(not reject, name + ': incorrectly allowed')
    CASES.append({'case': name, 'result': 'PASS'})
    return value


def support_reuse_fixtures(runner, manifest, graph, sources, public):
    """The same ten bounded D-adapter fixtures; no real retained audit is called."""
    support = 'ImbalancedChen.P1OriginalSingletonSupportData'
    witness = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
    cutoff = 'ImbalancedChen.P1OriginalSingletonCutoffData'
    first = closure(graph, [witness, cutoff])
    later_roots = manifest['selection_guidance']['subsequent_15_targets']
    later = closure(graph, later_roots)
    case('Support_only_compile_selection_rejected', lambda: runner.selection([support]), True)
    case('mixed_Support_compile_selection_rejected', lambda: runner.selection([witness, support]), True)
    case('HB_and_Cutoff_compile_selection_retained',
         lambda: need(set(runner.selection([witness, cutoff])) == {witness, cutoff}, 'first pair scope'))
    prior_loop = next(node for node in ast.walk(functions((HERE / 'run_selected.py').read_bytes())['preflight'])
                     if isinstance(node, ast.For) and 'previously_accepted_targets' in ast.unparse(node.iter))
    loop_code = compile(ast.Module(body=[prior_loop], type_ignores=[]), '<D-isolated-active-loop>', 'exec')
    def loop_case(active, expected):
        called = []
        exec(loop_code, {'active': active, 'manifest': manifest, 's': None, 'spec': None,
                         'retained_previous_target': lambda s, spec, module: called.append(module)})
        need(called == expected, 'previous-target validation exceeded actual selected closure')
    case('first68_does_not_invoke_Support_audit', lambda: loop_case(first, []))
    case('later157_invokes_precisely_Support', lambda: loop_case(later, [support]))
    def make_spec(active=later, selected=None):
        return SimpleNamespace(manifest=deepcopy(manifest), active=active,
            selected=set(later_roots if selected is None else selected), graph=graph, sources=dict(sources),
            retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
    original_spec, calls = None, []
    def retained_stub(s, shadow, module, validate_live=False):
        need(module == support and validate_live is True, 'full old audit-reader call required')
        for key in ('active', 'graph', 'sources', 'retained_inputs', 'historical_groups',
                    'historical_owners', 'supplier_evidence', 'dependency_pins'):
            need(getattr(shadow, key) is getattr(original_spec, key), 'unshared shadow state: ' + key)
        fixed = shadow.manifest['accepted_supplier_groups']['support_b']
        need(fixed['source_commit'] == fixed['source_graph']['commit'] == fixed['driver']['commit'] == PRIOR_B,
             'Support original acceptance identity rebound')
        need(closure(shadow.graph, [support]) <= shadow.active, 'shadow active expanded')
        calls.append((module, validate_live))
        return SimpleNamespace(fixture_call_only=True)
    working_public = deepcopy(public)
    original_retained, original_artifacts, original_published = (
        runner.retained_owner, runner.module_artifacts, runner.published_binding)
    fixture_artifacts = {'fixture-only.olean': {'bytes': 1, 'sha256': 'f' * 64}}
    runner.retained_owner = retained_stub
    runner.module_artifacts = lambda s, module: deepcopy(fixture_artifacts)
    runner.published_binding = lambda binding: json.dumps(working_public).encode()
    try:
        def valid_shadow():
            nonlocal original_spec
            original_spec = make_spec()
            saved = deepcopy(original_spec.manifest)
            result = runner.retained_previous_target(None, original_spec, support)
            need(result.fixture_call_only and calls == [(support, True)], 'old reader invocation differs')
            need(original_spec.manifest == saved and len(original_spec.manifest['accepted_suppliers']) == 17,
                 'real source partition mutated')
            need(original_spec.active is later and original_spec.dependency_pins[support] == fixture_artifacts,
                 'selected closure enlarged or prior-owner artifacts not retained')
        case('active_Support_uses_shared_shadow_and_B_identity_without_partition_mutation', valid_shadow)
        case('inactive_Support_direct_adapter_call_rejected',
             lambda: runner.retained_previous_target(None, make_spec(first, [witness, cutoff]), support), True)
        working_public['source_commit'] = 'wrong-isolated-fixture-source'
        case('wrong_Support_public_source_rejected',
             lambda: runner.retained_previous_target(None, make_spec(), support), True)
        working_public = deepcopy(public)
        del working_public['owners'][support]['receipt_bindings']['owned_log']
        case('missing_Support_owned_log_public_pin_rejected',
             lambda: runner.retained_previous_target(None, make_spec(), support), True)
        working_public = deepcopy(public)
        changed = make_spec()
        changed.sources[support] = 'changed-isolated-fixture-Support-source'
        case('changed_current_Support_source_rejected',
             lambda: runner.retained_previous_target(None, changed, support), True)
    finally:
        runner.retained_owner, runner.module_artifacts, runner.published_binding = (
            original_retained, original_artifacts, original_published)


def main():
    need((REPO / '.git').exists(), 'repository root differs')
    runner_path, installer_path = HERE / 'run_selected.py', HERE / 'install_sources.py'
    runner_raw, installer_raw = runner_path.read_bytes(), installer_path.read_bytes()
    old = git_file(ANCHOR, OLD_RUNNER)
    need(sha(old) == OLD_RUNNER_SHA, 'published integration template pin differs')
    current_functions, original_functions = functions(runner_raw), functions(old)
    for name in UNCHANGED:
        need(ast.dump(current_functions[name], include_attributes=False) ==
             ast.dump(original_functions[name], include_attributes=False), 'borrowed function changed: ' + name)
    prior_runner = git_file(PRIOR_B, 'docs/p1/20261126/p15-current-corrections/run_selected.py')
    prior_manifest_raw = git_file(PRIOR_B, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
    need(sha(prior_runner) == B_RUNNER_SHA and sha(prior_manifest_raw) == B_MANIFEST_SHA, 'B entrypoint pin differs')
    prior_functions = functions(prior_runner)
    changed_functions = [name for name in prior_functions if ast.dump(prior_functions[name]) !=
                         ast.dump(current_functions[name])]
    need(changed_functions == ['selection', 'source_manifest', 'preflight'] and
         set(current_functions) - set(prior_functions) == {'retained_previous_target'}, 'D function scope differs')
    unchanged_B_functions = [name for name in prior_functions if name not in changed_functions]
    for name in unchanged_B_functions:
        need(ast.get_source_segment(runner_raw.decode(), current_functions[name]) ==
             ast.get_source_segment(prior_runner.decode(), prior_functions[name]), 'B function bytes changed: ' + name)
    need(installer_raw == git_file(PRIOR_B, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'original additive installer bytes changed')
    prior_D_runner = git_file(PRIOR_D, 'docs/p1/20261126/p15-current-corrections/run_selected.py')
    prior_D_manifest_raw = git_file(PRIOR_D, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
    need(sha(prior_D_runner) == D_RUNNER_SHA and sha(prior_D_manifest_raw) == D_MANIFEST_SHA,
         'D entrypoint pin differs')
    prior_D_functions = functions(prior_D_runner)
    need(set(prior_D_functions) == set(current_functions), 'F added or removed a runner function')
    unchanged_D_functions = [name for name in prior_D_functions if name != 'source_manifest']
    for name in unchanged_D_functions:
        need(ast.get_source_segment(runner_raw.decode(), current_functions[name]) ==
             ast.get_source_segment(prior_D_runner.decode(), prior_D_functions[name]),
             'D function bytes changed: ' + name)
    D_manifest_function = ast.get_source_segment(prior_D_runner.decode(), prior_D_functions['source_manifest'])
    need(D_manifest_function.count(PUBLICATION_CHECK_BEFORE) == 1 and
         ast.get_source_segment(runner_raw.decode(), current_functions['source_manifest']) ==
         D_manifest_function.replace(PUBLICATION_CHECK_BEFORE, PUBLICATION_CHECK_AFTER, 1),
         'F source_manifest exceeds the authorized fixed-C summary comparison')
    D_assignments = {node.targets[0].id: ast.get_source_segment(prior_D_runner.decode(), node)
        for node in ast.parse(prior_D_runner).body if isinstance(node, ast.Assign) and
        len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)}
    F_assignments = {node.targets[0].id: ast.get_source_segment(runner_raw.decode(), node)
        for node in ast.parse(runner_raw).body if isinstance(node, ast.Assign) and
        len(node.targets) == 1 and isinstance(node.targets[0], ast.Name)}
    need(set(D_assignments) == set(F_assignments) and all(
        D_assignments[name] == F_assignments[name] for name in D_assignments
        if name not in ('SOURCE_ANCHOR', 'MANIFEST_SHA')), 'F changed a protected D constant')
    need(installer_raw == git_file(PRIOR_D, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'D additive installer bytes changed')
    runner = module_from(runner_path, 'isolated_correction_source_readers')
    installer = module_from(installer_path, 'isolated_addition_planner')
    # No helpers(), preflight(), worker(), main(), installer main(), or live
    # acceptance API is invoked. Replace the sole reader with local Git bytes.
    def local_file(commit, path):
        if commit == 'UNPUBLISHED_STATIC_FIXTURE' and path.startswith('docs/p1/20261126/p15-current-corrections/'):
            return (REPO / path).read_bytes()
        return git_file(ANCHOR if commit == 'UNPUBLISHED_STATIC_FIXTURE' else commit, path)
    runner.git_file = local_file
    fake = SimpleNamespace(api=SimpleNamespace(sha=sha), h=SimpleNamespace(imports=imports,
        module_path=lambda module: module.replace('.', '/') + '.lean', closure=closure))
    manifest_json = json.loads((HERE / 'SOURCE_MANIFEST.json').read_bytes())
    first = manifest_json['selection_guidance']['minimum_first_targets']
    manifest, graph, sources, observed, binding = case('full_360_published_source_and_provenance_readers',
        lambda: runner.source_manifest(fake, 'UNPUBLISHED_STATIC_FIXTURE', first))
    need(len(graph) == 360 and len(closure(graph, first)) == 68, '360/68 source count differs')
    need(set(closure(graph, first)) & set(runner.TARGETS) == set(first), 'first-two selection was expanded')
    prior_manifest = json.loads(prior_manifest_raw)
    for key in ('accepted_suppliers', 'accepted_supplier_groups', 'fixed_dependencies',
                'unaccepted_p3_dependencies', 'object_observation_binding'):
        need(manifest[key] == prior_manifest[key], 'original B partition or receipt identity changed: ' + key)
    prior_D_manifest = json.loads(prior_D_manifest_raw)
    changed_sources = {module for module in graph if manifest['project_sources'][module] !=
                       prior_D_manifest['project_sources'][module]}
    need(changed_sources == set(F_SOURCE_CHANGES) and len(changed_sources) == 5,
         'E source delta exceeds the five qualified-dyadic repairs')
    need(all(manifest['project_sources'][m]['all_imports'] == prior_D_manifest['project_sources'][m]['all_imports']
             for m in graph), 'E changed the source import graph')
    for key in manifest:
        if key not in ('source_anchor_commit', 'project_sources', 'target_source_origins'):
            need(manifest[key] == prior_D_manifest[key], 'F changed an original D manifest policy: ' + key)
    need(set(manifest) == set(prior_D_manifest), 'F changed the manifest schema')
    runner.published_binding(E_REPAIR)
    for module, origin in manifest['target_source_origins'].items():
        before = prior_D_manifest['target_source_origins'][module]
        if module in changed_sources:
            row = manifest['project_sources'][module]
            expected = {**before,
                'canonical_source': {'commit': ANCHOR, 'path': row['path'], 'bytes': row['bytes'], 'sha256': row['sha256']},
                'source_reviews': [*before['source_reviews'], E_REPAIR]}
            need(origin == expected, 'F repair provenance differs: ' + module)
        else:
            need(origin == before, 'F changed an unrelated canonical provenance: ' + module)
    ready = manifest['selection_guidance']['project_graph_unblocked_candidates']
    need(len(ready) == 18 and len(closure(graph, ready)) == 157, '18/157 project graph scope differs')
    blocked = set(manifest['unaccepted_p3_dependencies'])
    need(sorted(module for module in runner.TARGETS if closure(graph, [module]) & blocked) ==
         manifest['selection_guidance']['project_graph_blocked_candidates'], 'blocked candidate partition differs')
    for name, roots, reject in [('explicit_first2', first, False), ('reversed_explicit_first2', first[::-1], False),
            ('no_implicit_full_scope', None, True), ('empty_scope', [], True),
            ('duplicate_owner', first + [first[0]], True),
            ('accepted_Core_cannot_be_target', ['ImbalancedChen.Part3FiniteLambdaOverLogCore'], True),
            ('Geometry_requires_separate_revision', ['ImbalancedChen.P1OriginalSingletonRemainingTypeIGeometry'], True),
            ('P3_owner_cannot_be_target', ['ImbalancedChen.Part3BrunWeights'], True)]:
        case(name, lambda roots=roots: runner.selection(roots), reject)

    # Every retained-context recipe is tied to a published normal receipt hash,
    # not to a source hash used as a substitute object fingerprint.
    originals, summaries = {}, {}
    for name, group in manifest['accepted_supplier_groups'].items():
        raw = runner.published_binding(group['source_graph'])
        original = json.loads(raw)
        original_graph = {module: row['imports'] for module, row in original['project_sources'].items()}
        originals[name] = (original, original_graph)
        summaries[name] = json.loads(runner.published_binding(group['public_evidence']))
        need(len(original_graph) == group['published_source_count'], 'original graph count differs')
        need(sha(runner.published_binding(group['driver'])) == group['driver']['sha256'], 'old driver differs')
        for owner in group['owners']:
            active = closure(original_graph, [owner])
            need(active == closure(graph, [owner]) and all(
                original['project_sources'][module]['sha256'] == sources[module] for module in active),
                'accepted owner source closure differs: ' + owner)
            if name != 'mellin':
                owner_record = summaries[name]['owners'][owner]
                need(owner_record['source_commit'] == group['source_commit'] and
                     owner_record['source_sha256'] == sources[owner] and
                     runner.valid_fingerprint(owner_record['receipt_bindings']['normal']),
                     'original normal receipt hash missing: ' + owner)
    for module, policy in manifest['fixed_dependencies'].items():
        if policy['kind'] == 'retained_accepted_normal_dependency_context':
            witness = policy['witness_owner']
            group = manifest['accepted_suppliers'][witness]['group']
            original, original_graph = originals[group]
            need(module in closure(original_graph, [witness]) - {witness} and
                 original['project_sources'][module]['sha256'] == sources[module] and group != 'mellin',
                 'fixed dependency context coverage differs')
        else:
            record = observed['modules'][module]
            need(record['source']['sha256'] == sources[module] and
                 all(runner.valid_fingerprint(record['outputs'][ext]) for ext in ('.olean', '.trace')),
                 'observed cache pin missing')
    CASES.append({'case': '295_historical_context_witnesses_and_8_real_object_observations', 'result': 'PASS'})

    support = 'ImbalancedChen.P1OriginalSingletonSupportData'
    prior = manifest['previously_accepted_targets'][support]
    fixed_prior = prior['historical_group']
    need(runner.published_binding(fixed_prior['source_graph']) == prior_manifest_raw and
         runner.published_binding(fixed_prior['driver']) == prior_runner, 'Support original B graph/driver differs')
    support_public = json.loads(runner.published_binding(fixed_prior['public_evidence']))
    need(support_public['schema'] == 'p15_support_B_original_public_acceptance_v1' and
         support_public['source_commit'] == prior['source_commit'] == fixed_prior['source_commit'] == PRIOR_B and
         support_public['compiler_job'] == fixed_prior['compiler_job'] and
         support_public['original_group_worker_exit_code'] == 1 and set(support_public['owners']) == {support} and
         support_public['normal_or_kernel_commands_executed'] == 0 and
         support_public['source_runtime_and_original_receipts_unchanged'] is True,
         'Support bounded public identity or original failed group scope differs')
    public_owner = support_public['owners'][support]
    need(public_owner['source_commit'] == PRIOR_B and public_owner['source_sha256'] == sources[support] and
         public_owner['owned_count'] == public_owner['public_count'] == 5 and
         public_owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
         public_owner['receipt_rebound_to_current_commit'] is False and
         runner.valid_fingerprint(support_public['original_result']) and
         all(runner.valid_fingerprint(public_owner['receipt_bindings'].get(key)) for key in
             ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')),
         'Support original bounded receipt fields incomplete')
    prior_graph = {module: row['imports'] for module, row in prior_manifest['project_sources'].items()}
    support_closure = closure(graph, [support])
    need(len(support_closure) == 109 and support_closure == closure(prior_graph, [support]) and
         all(sources[module] == prior_manifest['project_sources'][module]['sha256'] for module in support_closure) and
         not support_closure.intersection(changed_sources), 'Support 109-source closure changed from B')
    later = manifest['selection_guidance']['subsequent_15_targets']
    need(len(later) == 15 and set(later) == set(ready) - {support, *first} and
         len(closure(graph, later)) == 157 and support_closure <= closure(graph, later), 'later actual dependency scope')
    need(manifest['selection_guidance']['remaining_project_graph_unblocked_compile_candidates'] ==
         [module for module in ready if module != support], 'remaining compilation candidate guidance differs')
    support_reuse_fixtures(runner, manifest, graph, sources, support_public)

    # Execute only the literal-import gate with a fake recorder. A failed stock
    # command, a successful command that built something, and malformed imports
    # must all hold before the immutable normal/audit path could run.
    good_module = first[0]
    recorded = []
    stock = {'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': []}
    mock_ops = SimpleNamespace(run=lambda folder, name, argv, **kw: recorded.append(argv) or deepcopy(stock))
    gate_s = SimpleNamespace(ops=mock_ops, h=SimpleNamespace(guard=lambda lane, argv: ['guard', lane, *argv]))
    literal = ['ImbalancedChen.P1OriginalSingletonPointwiseData', 'Mathlib.MeasureTheory.Integral.Bochner.Basic']
    gate_spec = SimpleNamespace(manifest={'project_sources': {good_module: {'all_imports': literal}}})
    case('direct_gate_checks_all_literal_imports_lane0',
         lambda: runner.direct_import_readiness(gate_s, gate_spec, good_module, Path('/fixture')))
    need(recorded[-1] == ['guard', 0, 'lake', '--no-build', 'build',
                         *['+' + module + ':olean' for module in literal]], 'literal gate command differs')
    for name, changes in [('native_readiness_exit3', {'exit_code': 3}),
                          ('no_build_gate_cannot_build', {'actual_built_modules': [good_module]}),
                          ('no_build_gate_cannot_fail_module', {'actual_failed_modules': [good_module]})]:
        before = deepcopy(stock)
        stock.update(changes)
        case(name, lambda: runner.direct_import_readiness(gate_s, gate_spec, good_module, Path('/fixture')), True)
        stock.clear(); stock.update(before)
    gate_spec.manifest['project_sources'][good_module]['all_imports'] = []
    case('empty_imports_never_trigger_bare_default_build',
         lambda: runner.direct_import_readiness(gate_s, gate_spec, good_module, Path('/fixture')), True)

    # Old Core acceptance remains a one-node live closure even when unrelated
    # old Mellin bytes in the full 168-node historical publication differ.
    core = 'ImbalancedChen.Part3FiniteLambdaOverLogCore'
    mellin = 'ImbalancedChen.PrimeProductsMellinExactMeanInsertion'
    core_commit = manifest['accepted_suppliers'][core]['source_commit']
    core_group = SimpleNamespace(commit=core_commit, graph={core: [], mellin: []},
        sources={core: sources[core], mellin: 'old-Mellin'}, base=Path('/fixture/old-Core'),
        public={'owners': {core: {'receipt_bindings': {'normal': {'bytes': 1, 'sha256': 'f' * 64}}}}})
    core_spec = SimpleNamespace(manifest=manifest, graph={core: [], mellin: []},
        sources={core: sources[core], mellin: sources[mellin]}, review={'runtime_configuration_bindings': {},
        'existing_runtime_bindings': {}}, historical_owners={})
    original_context = {'source_commit': core_commit, 'project_sources': {core: sources[core]},
                        'dependency_objects_and_traces': {}, 'configuration': {}, 'existing_runtime': {}}
    normal = {'module': core, 'source_commit': core_commit, 'status': 'NORMAL_PASS_AUDIT_PENDING',
              'dependency_context': original_context}
    old_group_fn, old_read_fn = runner.historical_group, runner.retained_read
    runner.historical_group = lambda *args: core_group
    runner.retained_read = lambda *args: json.dumps(normal).encode()
    case('Core_keeps_ef450_identity_despite_unrelated_Mellin_epoch', lambda: runner.retained_owner(fake, core_spec, core))
    core_spec.historical_owners.clear()
    core_spec.sources[core] = 'changed-Core'
    case('changed_selected_Core_source_holds', lambda: runner.retained_owner(fake, core_spec, core), True)
    core_spec.sources[core] = sources[core]
    normal['dependency_context']['source_commit'] = manifest['accepted_suppliers'][mellin]['source_commit']
    case('Core_receipt_cannot_be_rebound_to_Mellin_commit', lambda: runner.retained_owner(fake, core_spec, core), True)
    runner.historical_group, runner.retained_read = old_group_fn, old_read_fn

    # The published Mellin terminal observation also fixes the outer audit-lane
    # log. Exercise its real retained_read path on fixture bytes, without any
    # live acceptance API or execution of a driver/installer entrypoint.
    with tempfile.TemporaryDirectory(prefix='p15-correction-fixture-') as directory:
        fixed = deepcopy(manifest['accepted_supplier_groups']['mellin'])
        fixed['evidence_root'] = directory
        run = Path(directory) / fixed['source_commit'] / fixed['run']
        (run / mellin).mkdir(parents=True)
        public = deepcopy(summaries['mellin'])
        published_reader = runner.published_binding
        (run / 'executed-driver.py').write_bytes(published_reader(fixed['driver']))
        (run / 'RESULT.json').write_text(json.dumps({key: value for key, value in public['result'].items()
            if key not in ('batch6', 'path')}))
        for stem in ('CONTEXT', 'GIT'):
            for suffix in ('BEFORE', 'AFTER'):
                (run / (stem + '_' + suffix + '.json')).write_bytes(b'{}\n')
        audit_log = run / mellin / 'audit-lane-0.log'
        audit_raw = b'isolated successful audit-lane fixture\n'
        audit_log.write_bytes(audit_raw)
        audit_row = next(row for row in public['normal_and_audit'] if row.get('name') == 'audit-lane-0')
        audit_row['log_sha256'] = sha(audit_raw)
        runner.published_binding = lambda value: (json.dumps(public).encode()
            if value == fixed['public_evidence'] else published_reader(value))
        def mellin_fixture():
            fixture = SimpleNamespace(manifest={'accepted_supplier_groups': {'mellin': fixed}},
                historical_groups={}, retained_inputs={})
            runner.historical_group(fake, fixture, 'mellin')
            need(fixture.retained_inputs[str(audit_log)] == pin(audit_log),
                 'Mellin audit log was not included in retained input preservation')
            return fixture
        case('Mellin_published_audit_log_bound_and_preserved', mellin_fixture)
        audit_log.write_bytes(b'different audit log\n')
        case('Mellin_wrong_published_audit_log_SHA_holds', mellin_fixture, True)
        audit_log.write_bytes(audit_raw)
        audit_row['exit_code'] = 1
        case('Mellin_unsuccessful_published_audit_lane_holds', mellin_fixture, True)
        runner.published_binding = published_reader

    # The addition planner runs against a temporary fixture tree, with every
    # external/runtime function replaced. No production installer is invoked.
    with tempfile.TemporaryDirectory(prefix='p15-correction-fixture-') as directory:
        project = Path(directory)
        (project / 'ImbalancedChen').mkdir()
        target, dependency = 'ImbalancedChen.FixtureTarget', 'ImbalancedChen.FixtureDependency'
        payloads = {target: b'import ImbalancedChen.FixtureDependency\n', dependency: b'import Mathlib\n'}
        fixture_graph = {target: [dependency], dependency: []}
        fixture_sources = {m: sha(raw) for m, raw in payloads.items()}
        source_path = lambda m: project / (m.replace('.', '/') + '.lean')
        source_path(dependency).write_bytes(payloads[dependency])
        fixture_review = {'source_configuration_bindings': {}}
        cache = {target: {'fixture.olean': None}, dependency: {'fixture.olean': {'bytes': 1, 'sha256': '0' * 64}}}
        fixture_driver = SimpleNamespace(TARGETS=[target], REVIEW='fixture-review', REVIEW_SHA='fixture',
            selection=lambda selected: selected,
            source_manifest=lambda *args: ({}, fixture_graph, fixture_sources, {}, {}),
            pinned=lambda *args: json.dumps(fixture_review).encode(), environment=lambda *args: {},
            module_artifacts=lambda s, m: deepcopy(cache[m]), require_fresh_owner=runner.require_fresh_owner,
            file_binding=lambda path: sha(path.read_bytes()))
        fixture_s = SimpleNamespace(h=SimpleNamespace(closure=closure,
            module_path=lambda module: module.replace('.', '/') + '.lean'), api=SimpleNamespace(sha=sha))
        installer.PROJECT = project
        installer.git_file = lambda commit, path: (installer_raw if path.endswith('install_sources.py')
            else payloads[path[:-5].replace('/', '.')])
        result = case('additive_plan_accepts_only_absent_selected_source',
            lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]))
        need([row[0] for row in result['planned']] == [target] and not source_path(target).exists(),
             'planning wrote a file or broadened target list')
        source_path(target).write_bytes(b'conflicting source\n')
        case('existing_different_source_has_no_overwrite_path',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)
        source_path(target).unlink()
        cache[target]['fixture.olean'] = {'bytes': 1, 'sha256': '0' * 64}
        case('absent_source_with_existing_artifact_holds',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)
        cache[target]['fixture.olean'] = None
        source_path(dependency).unlink()
        case('missing_unselected_dependency_is_not_auto_installed',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)
        source_path(dependency).write_bytes(payloads[dependency])
        source_path(target).symlink_to(source_path(dependency))
        case('symlink_source_is_not_followed_or_replaced',
             lambda: installer.prepare(fixture_driver, fixture_s, 'fixture', [target]), True)

    # Exactly one project write primitive exists, under the prevalidated plan,
    # and it requires O_EXCL. The runner has no project/cache write primitive.
    opens = [node for node in ast.walk(ast.parse(installer_raw)) if isinstance(node, ast.Call) and
             isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and
             node.func.value.id == 'os' and node.func.attr == 'open']
    need(len(opens) == 1 and 'O_EXCL' in ast.unparse(opens[0].args[1]) and
         'O_TRUNC' not in ast.unparse(opens[0]), 'additive write primitive broadened')
    need(not any(isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and
        node.func.attr in {'unlink', 'remove', 'rename', 'rmtree', 'install_sources'}
        for node in ast.walk(ast.parse(runner_raw + b'\n' + installer_raw))), 'destructive/cache writer present')
    runtime_paths = [runner.API, 'docs/p1/20261124/batch5-parallel/run_batch5_parallel.py',
        'docs/p1/20261125/p15-singleton-proper-power/P3_REUSE.json',
        'docs/p1/20261125/p15-atlas-current-context-integration/run_selected.py',
        'docs/p1/20261125/p15-original-atlas-proper-power/run_selected.py']
    for path in runtime_paths:
        need((REPO / path).read_bytes() == git_file(ANCHOR, path), 'protected old source changed: ' + path)
    historical_paths = ['SOURCE_REANCHOR.json', 'ROOT_STATIC_REVIEW.json',
                        'FIRST_THREE_COMPILE_OBSERVATION.json', 'FIXED_DEPENDENCY_OBSERVATIONS.json']
    for name in historical_paths:
        need((HERE / name).read_bytes() == git_file(PRIOR_B, 'docs/p1/20261126/p15-current-corrections/' + name),
             'historical B evidence rewritten: ' + name)
    historical_D_paths = ['SOURCE_REANCHOR_D.json']
    for name in historical_D_paths:
        need((HERE / name).read_bytes() == git_file(PRIOR_D, 'docs/p1/20261126/p15-current-corrections/' + name),
             'historical D reanchor rewritten: ' + name)
    receipt = {'schema': 'p15_current_corrections_local_static_verification_v1',
        'status': 'PASS_LOCAL_SOURCE_BINDINGS_AST_PRESERVATION_AND_ISOLATED_PYTHON_FIXTURES_ONLY',
        'source_anchor_commit': ANCHOR,
        'inputs': {name: pin(HERE / name) for name in ['SOURCE_MANIFEST.json', 'FIXED_DEPENDENCY_OBSERVATIONS.json',
                                                     'run_selected.py', 'install_sources.py', 'verify_static.py', 'README.md']},
        'unchanged_original_functions': UNCHANGED, 'immutable_template_sha256': OLD_RUNNER_SHA,
        'unchanged_B_functions': unchanged_B_functions, 'unchanged_B_function_bytes': True,
        'B_installer_bytes_unchanged': True, 'B_source_commit': PRIOR_B,
        'full_source_manifest_function_executed_including_303_fixed_dependency_policies': True,
        'E_changed_source_rows': sorted(changed_sources), 'other_355_source_rows_unchanged': True,
        'D_source_commit': PRIOR_D, 'D_runner_sha256': D_RUNNER_SHA, 'D_manifest_sha256': D_MANIFEST_SHA,
        'unchanged_D_functions': unchanged_D_functions, 'unchanged_D_function_bytes': True,
        'D_source_manifest_only_fixed_C_publication_comparison_changed': True,
        'D_installer_bytes_unchanged': True, 'E_repair_manifest': E_REPAIR,
        'historical_D_files_unchanged': historical_D_paths,
        'counts': {'targets': 21, 'published_project_sources': 360, 'accepted_supplier_whitelist': 17,
            'fixed_dependencies': 303, 'retained_normal_context_witnesses': 295,
            'recorded_object_dependencies': 8, 'unaccepted_P3_suppliers': 19,
            'first2_selected_source_closure': 68, 'first2_preserved_dependencies': 66,
            'project_unblocked18_source_closure': 157, 'remaining_unblocked_compile_candidates': 17,
            'subsequent_15_source_closure': 157, 'previously_accepted_target_count': 1,
            'Support_B_source_closure': 109},
        'Support_B_public_evidence': fixed_prior['public_evidence'],
        'Support_live_reuse_condition': 'Only when in the actual selected closure; the first2 closure68 excludes it.',
        'fixtures': CASES, 'fixture_count': len(CASES),
        'driver_or_installer_entrypoints_executed': False, 'live_acceptance_API_invoked': False,
        'Lean_or_kernel_invoked': False, 'cloud_jobs_submitted': False, 'new_lean_acceptance': False,
        'protected_old_paths_unchanged': runtime_paths, 'historical_B_files_unchanged': historical_paths,
        'whole_P1_5_complete': False}
    (HERE / 'STATIC_VERIFICATION.json').write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'status': receipt['status'], 'fixture_count': len(CASES),
        'receipt': pin(HERE / 'STATIC_VERIFICATION.json')}, ensure_ascii=False))


if __name__ == '__main__':
    os.environ['GIT_OPTIONAL_LOCKS'] = '0'
    os.environ['GIT_NO_LAZY_FETCH'] = '1'
    main()
