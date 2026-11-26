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
ANCHOR = 'f6fdd7fffe17803c60914bf28b39b55715d34464'
PRIOR_F = '080d4178711ae042235104f7f4768649f51da2ab'
F_RUNNER_SHA = '9fffe0f6608eec153c5d58d8269f5ddb1b8f0552d8b862ae73b03451d4eda45c'
F_MANIFEST_SHA = '12c8898624290d088a7f51065db87fefa0e7f6ee72954a7fb582a28e17f4f609'
H_REPAIR = {'commit': ANCHOR, 'path': 'docs/p1/20261126/p15-cutoff-first-compile-repair/REPAIR_CANDIDATE.json', 'bytes': 16096, 'sha256': 'eb0431fd9667f3433a5f62b513ea6ecbaa2c561403145e9e0250153683eb4c38'}
HB = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
CUTOFF = 'ImbalancedChen.P1OriginalSingletonCutoffData'
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
    """Original Support adapter fixtures, with the I selection/dispatch boundary."""
    support = 'ImbalancedChen.P1OriginalSingletonSupportData'
    witness = 'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'
    cutoff = 'ImbalancedChen.P1OriginalSingletonCutoffData'
    first = closure(graph, [witness, cutoff])
    later_roots = manifest['selection_guidance']['subsequent_15_targets']
    later = closure(graph, later_roots)
    case('Support_only_compile_selection_rejected', lambda: runner.selection([support]), True)
    case('mixed_Support_compile_selection_rejected', lambda: runner.selection([witness, support]), True)
    case('HB_and_Cutoff_compile_selection_rejected',
         lambda: runner.selection([witness, cutoff]), True)
    prior_loop = next(node for node in ast.walk(functions((HERE / 'run_selected.py').read_bytes())['preflight'])
                     if isinstance(node, ast.For) and 'previously_accepted_targets' in ast.unparse(node.iter))
    loop_code = compile(ast.Module(body=[prior_loop], type_ignores=[]), '<D-isolated-active-loop>', 'exec')
    def loop_case(active, expected):
        called = []
        exec(loop_code, {'active': active, 'manifest': manifest, 's': None, 'spec': None,
                         'HB_F_MODULE': witness,
                         'retained_hb_f_target': lambda s, spec, module: called.append(module),
                         'retained_previous_target': lambda s, spec, module: called.append(module)})
        need(called == expected, 'previous-target validation exceeded actual selected closure')
    case('Cutoff68_invokes_only_HB_F_not_Support', lambda: loop_case(first, [witness]))
    case('later157_invokes_precisely_Support_B_and_HB_F', lambda: loop_case(later, [support, witness]))
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


def hb_f_reuse_fixtures(runner, manifest, graph, sources, public):
    """Bounded new adapter cases; all live readers and the audit call are synthetic."""
    prior = runner.HB_F_PREVIOUSLY_ACCEPTED_TARGET
    case('HB_F_real_public_scope_and_7_owned_7_public',
         lambda: runner.require_hb_f_public_scope(prior, public))
    for key, value in [('source_commit', '1' * 40), ('original_group_worker_exit_code', 0),
                       ('original_group_failed_modules', []), ('original_group_dispatch_error', 'unknown'),
                       ('selected_owner_live_closure_count', 68)]:
        mutated = deepcopy(public); mutated[key] = value
        case('HB_F_public_rejects_' + key,
             lambda p=mutated: runner.require_hb_f_public_scope(prior, p), True)
    mutated = deepcopy(public); mutated['owners'][HB]['receipt_rebound_to_current_commit'] = True
    case('HB_F_public_rejects_receipt_rebinding',
         lambda: runner.require_hb_f_public_scope(prior, mutated), True)
    paths = runner.artifact_paths(HB)
    cache = {path: None for path in paths}
    cache[paths[0]] = {'bytes': 1, 'sha256': 'a' * 64}
    source5 = {'synthetic_only': 'source-and-five-output-snapshot'}
    receipts, aid = public['owners'][HB]['receipt_bindings'], public['owners'][HB]['audit_id']
    binding = {'module': HB, 'normal_receipt': receipts['normal'],
        'audits': [{'plan': receipts['audit_plan'], 'result': receipts['audit_result']}],
        'all_observed_target_artifacts': cache, 'source_plus_five_outputs': source5}
    worker = {'source_commit': PRIOR_F, 'targets': [HB, CUTOFF], 'accepted_owners': [HB],
        'failures': {CUTOFF: 'synthetic-known-Cutoff-normal-failure'}, 'acceptance_bindings': {HB: binding}}
    original = {**deepcopy(worker), 'worker_exit_code': 1, 'all_selected_owners_accepted': False,
                'dispatch_error': 'serialized worker exited 1'}
    case('HB_F_known_partial_RESULT_and_WORKER_scope',
         lambda: runner.require_hb_f_run_scope(public, original, worker))
    for label, target, key, value in [
        ('extra_worker_acceptance', 'worker', 'accepted_owners', [HB, CUTOFF]),
        ('worker_dispatch', 'worker', 'dispatch_error', 'serialized worker exited 1'),
        ('group_success_claim', 'original', 'all_selected_owners_accepted', True),
        ('extra_result_failure', 'original', 'failures', {CUTOFF: 'x', HB: 'x'}),
        ('context_error', 'original', 'context_error', 'x')]:
        a, b = deepcopy(original), deepcopy(worker)
        (a if target == 'original' else b)[key] = value
        case('HB_F_rejects_' + label, lambda a=a, b=b: runner.require_hb_f_run_scope(public, a, b), True)
    run = Path(prior['historical_group']['evidence_root']) / PRIOR_F / 'runs/attempt-00000'
    retained = {run / 'RESULT.json': json.dumps(original).encode(),
                run / 'WORKER_RESULT.json': json.dumps(worker).encode()}
    model_public = deepcopy(public)
    raw_pin = lambda raw: {'bytes': len(raw), 'sha256': sha(raw)}
    model_public['original_result'] = raw_pin(retained[run / 'RESULT.json'])
    model_public['original_worker_result'] = raw_pin(retained[run / 'WORKER_RESULT.json'])
    for stem in ('CONTEXT', 'GIT'):
        raw = ('synthetic-' + stem).encode()
        for side in ('BEFORE', 'AFTER'):
            retained[run / (stem + '_' + side + '.json')] = raw
        model_public['original_context_pairs'][stem] = {'before': raw_pin(raw), 'after': raw_pin(raw)}
    actual_cache, actual_source5, calls, mutate_after = deepcopy(cache), deepcopy(source5), [], [False]
    active = closure(graph, [CUTOFF])
    s = SimpleNamespace(h=SimpleNamespace(closure=closure),
        d=SimpleNamespace(snapshot=lambda project, module: deepcopy(actual_source5)))

    def model_read(s, spec, path, expected):
        raw = retained[path]
        need(raw_pin(raw) == expected, 'synthetic retained pin differs')
        spec.retained_inputs[str(path)] = expected
        return raw

    def model_owner(s, shadow, module, validate_live):
        need(module == HB and validate_live is True and shadow.active is active,
             'HB did not call the original full reader within its actual scope')
        need(shadow.manifest['accepted_suppliers'][HB]['source_commit'] == PRIOR_F and
             shadow.manifest['accepted_supplier_groups']['hb_f']['source_commit'] == PRIOR_F,
             'HB receipt identity rebound')
        calls.append((module, validate_live))
        shadow.supplier_evidence[HB] = {'source_commit': PRIOR_F, 'selected_supplier_live_closure_count': 67,
            'owned_count': 7, 'public_count': 7,
            'audit_plan': {'path': str(run.parent.parent / HB / 'audits' / aid / 'AUDIT_PLAN.json')}}
        if mutate_after[0]:
            actual_cache[paths[1]] = {'bytes': 1, 'sha256': 'b' * 64}
        return SimpleNamespace(synthetic_reader_only=True)

    def spec():
        return SimpleNamespace(manifest=deepcopy(manifest), graph=graph, sources=sources, active=active,
            selected={CUTOFF}, retained_inputs={}, historical_groups={}, historical_owners={},
            supplier_evidence={}, dependency_pins={})

    saved = (runner.published_binding, runner.retained_read, runner.retained_owner, runner.module_artifacts)
    runner.published_binding = lambda binding: json.dumps(model_public).encode()
    runner.retained_read, runner.retained_owner = model_read, model_owner
    runner.module_artifacts = lambda s, module: deepcopy(actual_cache)
    try:
        def valid():
            candidate = spec()
            runner.retained_hb_f_target(s, candidate, HB)
            need(candidate.dependency_pins == {HB: cache} and calls == [(HB, True)] and
                 HB not in candidate.manifest['accepted_suppliers'] and
                 'ImbalancedChen.P1OriginalSingletonSupportData' not in candidate.active,
                 'HB adapter changed the actual scope, partition or original artifact pins')
        case('HB_F_full21_and_source5_match_original_before_after_reader', valid)
        actual_cache[paths[1]] = {'bytes': 1, 'sha256': 'b' * 64}; calls.clear()
        case('HB_F_artifact_change_before_reader_holds', lambda: runner.retained_hb_f_target(s, spec(), HB), True)
        need(not calls, 'HB artifact failure did not stop before the audit reader')
        actual_cache.clear(); actual_cache.update(deepcopy(cache)); actual_source5['synthetic_only'] = 'changed'
        case('HB_F_source5_change_before_reader_holds', lambda: runner.retained_hb_f_target(s, spec(), HB), True)
        need(not calls, 'HB source failure did not stop before the audit reader')
        actual_source5.clear(); actual_source5.update(deepcopy(source5)); mutate_after[0] = True
        case('HB_F_artifact_change_after_reader_holds', lambda: runner.retained_hb_f_target(s, spec(), HB), True)
        actual_cache.clear(); actual_cache.update(deepcopy(cache)); mutate_after[0] = False
        candidate = spec(); candidate.selected.add(HB)
        case('HB_F_selected_target_cannot_enter_reuse_adapter',
             lambda: runner.retained_hb_f_target(s, candidate, HB), True)
    finally:
        runner.published_binding, runner.retained_read, runner.retained_owner, runner.module_artifacts = saved


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
    prior_F_runner = git_file(PRIOR_F, 'docs/p1/20261126/p15-current-corrections/run_selected.py')
    prior_F_manifest_raw = git_file(PRIOR_F, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
    need(sha(prior_F_runner) == F_RUNNER_SHA and sha(prior_F_manifest_raw) == F_MANIFEST_SHA,
         'F entrypoint pin differs')
    prior_F_functions = functions(prior_F_runner)
    added = {'hb_f_source_binding', 'require_hb_f_public_scope', 'require_hb_f_run_scope',
             'retained_hb_f_target'}
    need(set(current_functions) - set(prior_F_functions) == added and
         set(prior_F_functions) <= set(current_functions), 'I function scope differs')
    unchanged_F_functions = [name for name in prior_F_functions if name not in ('source_manifest', 'preflight')]
    for name in unchanged_F_functions:
        need(ast.get_source_segment(runner_raw.decode(), current_functions[name]) ==
             ast.get_source_segment(prior_F_runner.decode(), prior_F_functions[name]),
             'F function bytes changed: ' + name)
    old_source = ast.get_source_segment(prior_F_runner.decode(), prior_F_functions['source_manifest'])
    expected_source = old_source.replace(
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData'},",
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE},", 1).replace(
        '    for module, prior in previous.items():\n',
        "    for module, prior in previous.items():\n"
        "        if module == HB_F_MODULE:\n"
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'HB@F previous target classification differs')\n"
        "            hb_f_source_binding(s, graph, sources, prior)\n"
        "            continue\n", 1)
    need(ast.get_source_segment(runner_raw.decode(), current_functions['source_manifest']) == expected_source,
         'I source_manifest exceeds the HB source-binding branch')
    old_preflight = ast.get_source_segment(prior_F_runner.decode(), prior_F_functions['preflight'])
    expected_preflight = old_preflight.replace('        retained_previous_target(s, spec, module)\n',
        '        if module == HB_F_MODULE:\n'
        '            retained_hb_f_target(s, spec, module)\n'
        '        else:\n'
        '            retained_previous_target(s, spec, module)\n', 1)
    need(ast.get_source_segment(runner_raw.decode(), current_functions['preflight']) == expected_preflight,
         'I preflight exceeds the separate HB dispatch')
    old_nodes = [node for node in ast.parse(prior_F_runner).body if not isinstance(node, ast.FunctionDef)]
    new_nodes = [node for node in ast.parse(runner_raw).body if not isinstance(node, ast.FunctionDef)]
    extra_names = {'HB_F_MODULE', 'HB_F_CUTOFF', 'HB_F_SOURCE_ANCHOR', 'HB_F_PREVIOUSLY_ACCEPTED_TARGET'}
    filtered = []
    for node in new_nodes:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in extra_names or (name == 'PREVIOUSLY_ACCEPTED_TARGETS' and
                                      isinstance(node.value, ast.Dict) and None in node.value.keys):
                continue
        filtered.append(node)
    need(len(old_nodes) == len(filtered), 'I changed protected top-level structure')
    for before, after in zip(old_nodes, filtered):
        if before is old_nodes[0]:
            expected_doc = ast.get_source_segment(prior_F_runner.decode(), before).replace(
                'E-anchored', 'H-anchored', 1).replace(
                'Previously accepted Support@B\nis always excluded from compilation and is revalidated only when a dependency.',
                'Previously accepted Support@B and HB@F\nare excluded from compilation and revalidated only inside the actual dependency closure.', 1)
            need(ast.get_source_segment(runner_raw.decode(), after) == expected_doc,
                 'I driver docstring exceeds the explicit anchor/HB description')
            continue
        if isinstance(before, ast.Assign) and isinstance(before.targets[0], ast.Name) and before.targets[0].id in (
                'SOURCE_ANCHOR', 'MANIFEST_SHA'):
            continue
        need(ast.get_source_segment(prior_F_runner.decode(), before) ==
             ast.get_source_segment(runner_raw.decode(), after), 'I changed a protected constant/import/main guard')
    need(installer_raw == git_file(PRIOR_F, 'docs/p1/20261126/p15-current-corrections/install_sources.py') ==
         git_file(PRIOR_B, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'original additive installer bytes changed')
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
    need((set(closure(graph, first)) & set(runner.TARGETS)) - set(runner.PREVIOUSLY_ACCEPTED_TARGETS) == set(first),
         'Cutoff selection was expanded')
    prior_manifest = json.loads(prior_manifest_raw)
    for key in ('accepted_suppliers', 'accepted_supplier_groups', 'fixed_dependencies',
                'unaccepted_p3_dependencies', 'object_observation_binding'):
        need(manifest[key] == prior_manifest[key], 'original B partition or receipt identity changed: ' + key)
    prior_F_manifest = json.loads(prior_F_manifest_raw)
    changed_sources = {module for module in graph if manifest['project_sources'][module] !=
                       prior_F_manifest['project_sources'][module]}
    need(changed_sources == {CUTOFF}, 'H source delta exceeds the Cutoff repair')
    need(all(manifest['project_sources'][m]['all_imports'] == prior_F_manifest['project_sources'][m]['all_imports']
             for m in graph), 'H changed the source import graph')
    for key in manifest:
        if key not in ('source_anchor_commit', 'project_sources', 'target_source_origins',
                       'previously_accepted_targets', 'selection_guidance'):
            need(manifest[key] == prior_F_manifest[key], 'I changed an original F manifest policy: ' + key)
    need(set(manifest) == set(prior_F_manifest), 'I changed the manifest schema')
    runner.published_binding(H_REPAIR)
    for module, origin in manifest['target_source_origins'].items():
        before = prior_F_manifest['target_source_origins'][module]
        if module in changed_sources:
            row = manifest['project_sources'][module]
            expected = {**before,
                'canonical_source': {'commit': ANCHOR, 'path': row['path'], 'bytes': row['bytes'], 'sha256': row['sha256']},
                'source_reviews': [*before['source_reviews'], H_REPAIR]}
            need(origin == expected, 'I repair provenance differs: ' + module)
        else:
            need(origin == before, 'I changed unrelated canonical provenance: ' + module)
    for row in manifest['project_sources'].values():
        need((REPO / row['path']).read_bytes() == git_file(ANCHOR, row['path']),
             'current canonical source differs from published H: ' + row['path'])
    need(manifest['previously_accepted_targets'] == {
        **prior_F_manifest['previously_accepted_targets'], HB: runner.HB_F_PREVIOUSLY_ACCEPTED_TARGET},
        'I changed the original Support mapping or added an unapproved historical target')
    old_guidance, guidance = prior_F_manifest['selection_guidance'], manifest['selection_guidance']
    expected_guidance = {**old_guidance,
        'minimum_first_targets': [CUTOFF],
        'previously_accepted_not_compile_targets': ['ImbalancedChen.P1OriginalSingletonSupportData', HB],
        'remaining_project_graph_unblocked_compile_candidates': [module for module in
            old_guidance['project_graph_unblocked_candidates'] if module not in runner.PREVIOUSLY_ACCEPTED_TARGETS],
        'previous_target_live_reuse_condition':
            'Only historical targets in the actual selected closure: Cutoff root68 revalidates HB@F67, without Support. '
            'Subsequent15 closure157 reuses Support@B109 and HB@F67, and requires Cutoff accepted under this same I commit.'}
    need(guidance == expected_guidance, 'I selection guidance exceeds Cutoff/HB reuse change')
    ready = manifest['selection_guidance']['project_graph_unblocked_candidates']
    need(len(ready) == 18 and len(closure(graph, ready)) == 157, '18/157 project graph scope differs')
    blocked = set(manifest['unaccepted_p3_dependencies'])
    need(sorted(module for module in runner.TARGETS if closure(graph, [module]) & blocked) ==
         manifest['selection_guidance']['project_graph_blocked_candidates'], 'blocked candidate partition differs')
    for name, roots, reject in [('explicit_Cutoff_only', first, False), ('same_Cutoff_explicit_order', first[::-1], False),
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
    need(len(later) == 15 and set(later) == set(ready) - {support, HB, *first} and
         len(closure(graph, later)) == 157 and support_closure <= closure(graph, later), 'later actual dependency scope')
    need(manifest['selection_guidance']['remaining_project_graph_unblocked_compile_candidates'] ==
         [module for module in ready if module not in (support, HB)], 'remaining compilation candidate guidance differs')
    support_reuse_fixtures(runner, manifest, graph, sources, support_public)
    hb_public = json.loads(runner.published_binding(runner.HB_F_PREVIOUSLY_ACCEPTED_TARGET['historical_group']['public_evidence']))
    hb_group = runner.HB_F_PREVIOUSLY_ACCEPTED_TARGET['historical_group']
    need(runner.published_binding(hb_group['source_graph']) == prior_F_manifest_raw and
         runner.published_binding(hb_group['driver']) == prior_F_runner, 'HB original F graph/driver differs')
    hb_graph = {module: row['imports'] for module, row in prior_F_manifest['project_sources'].items()}
    hb_closure = closure(graph, [HB])
    need(len(hb_closure) == 67 and hb_closure == closure(hb_graph, [HB]) and
         all(sources[module] == prior_F_manifest['project_sources'][module]['sha256'] for module in hb_closure),
         'HB 67-source closure changed from F')
    hb_f_reuse_fixtures(runner, manifest, graph, sources, hb_public)

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
        'Support_B_mapping_and_adapter_bytes_unchanged_from_F': True,
        'B_installer_bytes_unchanged': True, 'B_source_commit': PRIOR_B,
        'full_source_manifest_function_executed_including_303_fixed_dependency_policies': True,
        'H_changed_source_rows': sorted(changed_sources), 'other_359_source_rows_unchanged': True,
        'F_source_commit': PRIOR_F, 'F_runner_sha256': F_RUNNER_SHA, 'F_manifest_sha256': F_MANIFEST_SHA,
        'unchanged_F_functions': unchanged_F_functions, 'unchanged_F_function_bytes': True,
        'F_source_manifest_and_preflight_only_added_HB_dispatch': True,
        'F_installer_bytes_unchanged': True, 'H_repair_record': H_REPAIR,
        'historical_D_files_unchanged': historical_D_paths,
        'counts': {'targets': 21, 'published_project_sources': 360, 'accepted_supplier_whitelist': 17,
            'fixed_dependencies': 303, 'retained_normal_context_witnesses': 295,
            'recorded_object_dependencies': 8, 'unaccepted_P3_suppliers': 19,
            'Cutoff_selected_source_closure': 68, 'Cutoff_preserved_dependencies': 67,
            'project_unblocked18_source_closure': 157, 'remaining_unblocked_compile_candidates': 16,
            'subsequent_15_source_closure': 157, 'previously_accepted_target_count': 2,
            'Support_B_source_closure': 109, 'HB_F_source_closure': 67},
        'Support_B_public_evidence': fixed_prior['public_evidence'],
        'Support_live_reuse_condition': 'Only when in the actual selected closure; the Cutoff closure68 excludes it.',
        'HB_F_public_evidence': hb_group['public_evidence'],
        'HB_F_reuse_condition': 'Original F partial-run identity, full21 artifacts and source5 before/after the unchanged retained full audit.',
        'HB_adapter_fixtures_use_only_synthetic_readers': True,
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
