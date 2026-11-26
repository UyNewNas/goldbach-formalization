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
ANCHOR = 'c47ea640bf40c22423aec7066c13e5b05956d349'
PRIOR_F = '080d4178711ae042235104f7f4768649f51da2ab'
F_RUNNER_SHA = '9fffe0f6608eec153c5d58d8269f5ddb1b8f0552d8b862ae73b03451d4eda45c'
F_MANIFEST_SHA = '12c8898624290d088a7f51065db87fefa0e7f6ee72954a7fb582a28e17f4f609'
H_REPAIR = {'commit': 'f6fdd7fffe17803c60914bf28b39b55715d34464', 'path': 'docs/p1/20261126/p15-cutoff-first-compile-repair/REPAIR_CANDIDATE.json', 'bytes': 16096, 'sha256': 'eb0431fd9667f3433a5f62b513ea6ecbaa2c561403145e9e0250153683eb4c38'}
PRIOR_I = 'f21a8601d99ea33ec572223f5267415ca4ead8db'
I_RUNNER_SHA = '1a7e64b6c0afebdef03fe7361751a57c1ec859f0f1f1c74c1a2cfa75155cc986'
I_MANIFEST_SHA = 'c87b444c02cd3e9d3ea35c1d24a3c0f0525c4a038cc9d587082034a1ce9bb150'
J_REPAIR = {'commit': '7c59a3d125d99010a501c14f1ecc60710483f918', 'path': 'docs/p1/20261126/p15-cutoff-bind-pure-repair/REPAIR_CANDIDATE.json', 'bytes': 6592, 'sha256': '4119a1b346879b9fadc93a390eb95ab3c7e951cf367a6503625af36bcaa74383'}
PRIOR_K = '237b5c5c6b9fa721ea2d069fb5fafc0940a27e4e'
K_RUNNER_SHA = '575fcc9737d0b239cb0d994ad286ad8cae5dbf4406ca898157d7c2e87782c293'
K_MANIFEST_SHA = 'f683cfc328b7323d4e1840e10dc1eca0b24c4b55b644756ef2e5d910152a27e5'
L_REPAIR = {'commit': '972c2220d87669869a65c03fa64dc04562e37f0d', 'path': 'docs/p1/20261126/p15-licensed-profile-first-compile-repair/REPAIR_CANDIDATES.json', 'bytes': 5675, 'sha256': 'cea241b550d0e4c534209af59ba273a3a9b369e93ce4c05156a54fb66807e13a'}
L_SOURCE_CHANGES = ['ImbalancedChen.P5LicensedOriginalIntegerProfile', 'ImbalancedChen.P1OriginalSingletonSmoothLicence', 'ImbalancedChen.P5AdmissibleAllRankIntegerGeometricFamily']
LICENSED = 'ImbalancedChen.P5LicensedOriginalIntegerProfile'
PRIOR_M = '54c6e72732ce3a6d209960c396956f9cb2fe3f59'
M_RUNNER_SHA = 'a956f87fa00e360156c6e10dba3de857e038486b7e6a97aefebfe80e9a05ccfa'
M_MANIFEST_SHA = '0ce2649ad047edaba54c63c62f369d3df1046c5b2bd4cf4a916cac9584348a8d'
N_REPAIR = {'commit': 'c47ea640bf40c22423aec7066c13e5b05956d349', 'path': 'docs/p1/20261126/p15-pergroup-first-compile-repair/REPAIR_CANDIDATE.json', 'bytes': 7133, 'sha256': '16dfd87cd005c8fa78c6fac0d50c102be3631e67e0efd7ffc7eba03f4744fab7'}
N_PROBE = {'commit': 'c47ea640bf40c22423aec7066c13e5b05956d349', 'path': 'docs/p1/20261126/p15-pergroup-first-compile-repair/ACTUAL_PROBE_RESULT.json', 'bytes': 2130, 'sha256': '5085f0795e082a5b8118d7fa0bd0f6d60916f5859aa2ca43821ef8dca0fe9809'}
PERGROUP = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
O_REUSE_CONDITION = 'Only historical targets in the actual selected closure: PerGroup root69 revalidates Licensed@M68 and HB@F67, without Support or Cutoff. Remaining14 closure157 separately reuses Support@B109, HB@F67, Cutoff@K68 and Licensed@M68 under their original accepted source commits; none is a compilation target. The original M fifteen-target group remains partial failure.'
M_REUSE_CONDITION = 'Only historical targets in the actual selected closure: Licensed root68 revalidates HB@F67, without Support or Cutoff. Subsequent15 closure157 separately reuses Support@B109, HB@F67 and Cutoff@K68 under their original accepted source commits; none is a compilation target.'
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
    first = closure(graph, [PERGROUP])
    later_roots = manifest['selection_guidance']['subsequent_14_targets']
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
                         'HB_F_MODULE': witness, 'CUTOFF_K_MODULE': cutoff, 'LICENSED_M_MODULE': LICENSED,
                         'retained_licensed_m_target': lambda s, spec, module: called.append(module),
                         'retained_cutoff_k_target': lambda s, spec, module: called.append(module),
                         'retained_hb_f_target': lambda s, spec, module: called.append(module),
                         'retained_previous_target': lambda s, spec, module: called.append(module)})
        need(called == expected, 'previous-target validation exceeded actual selected closure')
    case('PerGroup69_invokes_Licensed_M_and_HB_F_not_Support_or_Cutoff', lambda: loop_case(first, [LICENSED, witness]))
    case('later157_invokes_precisely_four_original_priors', lambda: loop_case(later, [cutoff, support, LICENSED, witness]))
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
             lambda: runner.retained_previous_target(None, make_spec(first, [PERGROUP]), support), True)
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


def cutoff_k_reuse_fixtures(runner, manifest, graph, sources, public):
    draft = Path(runner.__file__).read_text()
    K = PRIOR_K
    def raw_fingerprint(raw):
        return {'bytes': len(raw), 'sha256': sha(raw)}
    # Extract declarations only. This does not import/execute the unbound driver,
    # helpers, preflight, main, installer, guard, or any original acceptance API.
    allowed_functions = {'require', 'valid_fingerprint', 'selection', 'artifact_paths',
        'cutoff_k_source_binding', 'require_cutoff_k_public_scope',
        'require_cutoff_k_run_scope', 'retained_cutoff_k_target'}
    allowed_constants = {'PROJECT', 'ROOT', 'MODULE', 'SHA256', 'TARGETS', 'PREVIOUSLY_ACCEPTED_TARGETS',
        'HB_F_MODULE', 'HB_F_CUTOFF', 'HB_F_SOURCE_ANCHOR', 'HB_F_PREVIOUSLY_ACCEPTED_TARGET',
        'CUTOFF_K_MODULE', 'CUTOFF_K_SOURCE_ANCHOR', 'CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET',
        'LICENSED_M_MODULE', 'LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET'}
    nodes = []
    for node in ast.parse(draft).body:
        if isinstance(node, ast.FunctionDef) and node.name in allowed_functions:
            nodes.append(node)
        elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in allowed_constants:
                nodes.append(node)
    ns = {'Path': Path, 're': re, 'json': json, 'SimpleNamespace': SimpleNamespace}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), '<isolated-new-Cutoff-adapter>', 'exec'), ns)
    s = SimpleNamespace(h=SimpleNamespace(closure=closure))
    prior = ns['CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET']
    bound_prior = prior
    prior = deepcopy(bound_prior)
    prior['historical_group']['public_evidence']['commit'] = '__UNBOUND_L_FIXTURE__'
    ns['CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET'] = prior
    case('unbound_L_publication_cannot_pass_source_binding',
         lambda: ns['cutoff_k_source_binding'](s, graph, sources, prior), True)
    prior = bound_prior
    ns['CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET'] = prior
    case('accepted_Cutoff_cannot_be_selected_for_compilation', lambda: ns['selection']([CUTOFF]), True)
    case('real_K_public_summary_has_16_owned_8_public_and_single_success',
         lambda: ns['require_cutoff_k_public_scope'](prior, public))
    for label, mutate in [
        ('wrong_public_count', lambda p: p['owners'][CUTOFF].update(public_count=16)),
        ('failed_group_status', lambda p: p.update(original_group_worker_exit_code=1))]:
        altered = deepcopy(public)
        mutate(altered)
        case(label, lambda p=altered: ns['require_cutoff_k_public_scope'](prior, p), True)
    altered_prior = deepcopy(prior)
    altered_prior['historical_group']['run'] = 'runs/attempt-00001'
    case('later_attempt_00001_cannot_replace_K_success',
         lambda: ns['cutoff_k_source_binding'](s, graph, sources, altered_prior), True)

    manifest = deepcopy(manifest)
    root = ns['ROOT'] / K
    run = root / 'runs/attempt-00000'
    base = root / CUTOFF
    audit_id = prior['audit_id']
    audit = base / 'audits' / audit_id
    receipts = public['owners'][CUTOFF]['receipt_bindings']
    paths = ns['artifact_paths'](CUTOFF)
    expected_artifacts = {path: None for path in paths}
    expected_artifacts[paths[0]] = {'bytes': 1, 'sha256': 'a' * 64}
    expected_source5 = {'synthetic_only': 'original-source-and-five-output-binding'}
    binding = {'module': CUTOFF,
        'normal_receipt': {'path': str(base / 'normal' / CUTOFF / 'NORMAL_PASS.json'), **receipts['normal']},
        'audits': [{'plan': {'path': str(audit / 'AUDIT_PLAN.json'), **receipts['audit_plan']},
                    'result': {'path': str(audit / 'lane-0/VALIDATION_RESULTS.json'), **receipts['audit_result']}}],
        'all_observed_target_artifacts': expected_artifacts, 'source_plus_five_outputs': expected_source5}
    guard = lambda lane, argv: ['SYNTHETIC-LANE-' + str(lane), *argv]
    stock_raw = b'synthetic successful final stock log\n'
    stock_pin = raw_fingerprint(stock_raw)
    stock = {'argv': guard(0, ['lake', '--no-build', 'build', '+' + CUTOFF + ':olean']),
        'cwd': str(ns['PROJECT']), 'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': [],
        'log': str(run / 'final-stock-readiness.log'),
        'log_bytes': stock_pin['bytes'], 'log_sha256': stock_pin['sha256']}
    worker = {'source_commit': K, 'targets': [CUTOFF], 'accepted_owners': [CUTOFF], 'failures': {},
        'acceptance_bindings': {CUTOFF: binding}, 'published_source_count': 360,
        'selected_live_source_count': 68, 'accepted_supplier_recompile_requested': False,
        'dependency_rebuild_requested': False, 'old_receipts_rebound': False, 'old_P3_REUSE_changed': False,
        'reused_complete_selected_owners': [], 'original_supplier_acceptance_bindings': {'synthetic_only': 'HB@F'},
        'direct_import_readiness': {CUTOFF: {'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': []}},
        'final_stock_readiness': stock}
    original = {**deepcopy(worker), 'worker_exit_code': 0, 'all_selected_owners_accepted': True}
    case('single_success_RESULT_WORKER_and_exact_receipt_paths',
         lambda: ns['require_cutoff_k_run_scope'](public, original, worker))
    altered = deepcopy(original)
    altered.update(targets=manifest['selection_guidance']['subsequent_15_targets'],
                   accepted_owners=[], failures={'ImbalancedChen.P5LicensedOriginalIntegerProfile': 'synthetic failure'})
    case('later_15_failure_cannot_supply_single_success',
         lambda: ns['require_cutoff_k_run_scope'](public, altered, worker), True)
    altered_worker, altered_original = deepcopy(worker), deepcopy(original)
    altered_worker['final_stock_readiness']['actual_built_modules'] = ['synthetic forbidden build']
    altered_original['final_stock_readiness'] = deepcopy(altered_worker['final_stock_readiness'])
    case('original_stock_build_disqualifies_reuse',
         lambda: ns['require_cutoff_k_run_scope'](public, altered_original, altered_worker), True)

    retained = {run / 'RESULT.json': json.dumps(original).encode(),
                run / 'WORKER_RESULT.json': json.dumps(worker).encode(),
                run / 'final-stock-readiness.log': stock_raw}
    model_public = deepcopy(public)
    model_public['original_result'] = raw_fingerprint(retained[run / 'RESULT.json'])
    model_public['original_worker_result'] = raw_fingerprint(retained[run / 'WORKER_RESULT.json'])
    model_public['original_final_stock_readiness']['log_fingerprint'] = stock_pin
    for stem in ('CONTEXT', 'GIT'):
        raw = ('synthetic unchanged ' + stem).encode()
        for side in ('BEFORE', 'AFTER'):
            retained[run / (stem + '_' + side + '.json')] = raw
        model_public['original_context_pairs'][stem] = {'before': raw_fingerprint(raw), 'after': raw_fingerprint(raw)}
    actual_artifacts, actual_source5 = deepcopy(expected_artifacts), deepcopy(expected_source5)
    active = closure(graph, manifest['selection_guidance']['subsequent_14_targets'])
    calls, mutate_after, wrong_counts = [], [False], [False]
    s = SimpleNamespace(h=SimpleNamespace(closure=closure, guard=guard),
                        d=SimpleNamespace(snapshot=lambda project, module: deepcopy(actual_source5)))

    def model_read(s, spec, path, expected):
        raw = retained[path]
        need(raw_fingerprint(raw) == expected, 'synthetic retained pin differs')
        spec.retained_inputs[str(path)] = expected
        return raw

    def model_owner(s, shadow, module, validate_live):
        need(module == CUTOFF and validate_live is True and shadow.active is active,
             'new adapter did not call unchanged reader within actual active scope')
        need(shadow.manifest['accepted_suppliers'][module]['source_commit'] == K and
             shadow.manifest['accepted_supplier_groups']['cutoff_k']['source_commit'] == K,
             'old K acceptance was rebound')
        calls.append((module, validate_live))
        shadow.supplier_evidence[module] = {'source_commit': K, 'selected_supplier_live_closure_count': 68,
            'owned_count': 16, 'public_count': 7 if wrong_counts[0] else 8,
            'audit_plan': {'path': str(audit / 'AUDIT_PLAN.json')}}
        if mutate_after[0]:
            actual_artifacts[paths[1]] = {'bytes': 1, 'sha256': 'b' * 64}
        return SimpleNamespace(synthetic_reader_only=True)

    def spec():
        return SimpleNamespace(manifest=deepcopy(manifest), graph=graph, sources=sources, active=active,
            selected=set(manifest['selection_guidance']['subsequent_14_targets']),
            retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})

    ns.update(published_binding=lambda binding: json.dumps(model_public).encode(), retained_read=model_read,
              retained_owner=model_owner, module_artifacts=lambda s, module: deepcopy(actual_artifacts))

    def valid_adapter():
        candidate = spec()
        shared = {key: getattr(candidate, key) for key in
                  ('active', 'retained_inputs', 'historical_groups', 'historical_owners', 'supplier_evidence', 'dependency_pins')}
        result = ns['retained_cutoff_k_target'](s, candidate, CUTOFF)
        need(result.synthetic_reader_only and calls == [(CUTOFF, True)], 'reader invocation differs')
        need(all(getattr(candidate, key) is value for key, value in shared.items()), 'state maps replaced')
        need(candidate.dependency_pins == {CUTOFF: expected_artifacts} and
             CUTOFF not in candidate.manifest['accepted_suppliers'] and
             str(run / 'final-stock-readiness.log') in candidate.retained_inputs,
             'original partition/artifacts/final stock preservation differs')

    case('K_reader_full21_source5_counts_and_stock_log_are_preserved', valid_adapter)
    calls.clear()
    outside = spec()
    outside.active = closure(graph, ['ImbalancedChen.P5LicensedOriginalIntegerProfile'])
    case('Licensed_only_does_not_revalidate_out_of_scope_Cutoff',
         lambda: ns['retained_cutoff_k_target'](s, outside, CUTOFF), True)
    selected = spec()
    selected.selected.add(CUTOFF)
    case('selected_Cutoff_cannot_enter_the_reuse_adapter',
         lambda: ns['retained_cutoff_k_target'](s, selected, CUTOFF), True)
    actual_artifacts[paths[1]] = {'bytes': 1, 'sha256': 'b' * 64}
    case('artifact_change_before_reader_holds', lambda: ns['retained_cutoff_k_target'](s, spec(), CUTOFF), True)
    need(not calls, 'early artifact failure did not stop before reader')
    actual_artifacts.clear(); actual_artifacts.update(deepcopy(expected_artifacts))
    actual_source5['synthetic_only'] = 'changed source or output'
    case('source_plus_five_change_before_reader_holds', lambda: ns['retained_cutoff_k_target'](s, spec(), CUTOFF), True)
    need(not calls, 'early source5 failure did not stop before reader')
    actual_source5.clear(); actual_source5.update(deepcopy(expected_source5))
    mutate_after[0] = True
    case('artifact_change_after_reader_holds', lambda: ns['retained_cutoff_k_target'](s, spec(), CUTOFF), True)
    mutate_after[0] = False
    actual_artifacts.clear(); actual_artifacts.update(deepcopy(expected_artifacts)); calls.clear()
    wrong_counts[0] = True
    case('full_reader_count_must_equal_original_16_and_8',
         lambda: ns['retained_cutoff_k_target'](s, spec(), CUTOFF), True)
    wrong_counts[0] = False
    model_public['original_final_stock_readiness']['log_fingerprint'] = {'bytes': stock_pin['bytes'], 'sha256': 'c' * 64}
    case('wrong_final_stock_log_pin_holds', lambda: ns['retained_cutoff_k_target'](s, spec(), CUTOFF), True)


def licensed_m_reuse_fixtures(runner, manifest, graph, sources, public):
    """The 17 reviewed Licensed cases, now bound to actual N publication."""
    draft = Path(runner.__file__).read_text()
    MODULE, FAILED, M = LICENSED, PERGROUP, PRIOR_M
    case_base = len(CASES)
    def raw_fingerprint(raw):
        return {'bytes': len(raw), 'sha256': sha(raw)}
    allowed_functions = {'require', 'valid_fingerprint', 'selection', 'artifact_paths',
        'licensed_m_source_binding', 'require_licensed_m_public_scope',
        'require_licensed_m_run_scope', 'retained_licensed_m_target'}
    allowed_constants = {'PROJECT', 'ROOT', 'MODULE', 'SHA256', 'TARGETS', 'PREVIOUSLY_ACCEPTED_TARGETS',
        'HB_F_MODULE', 'HB_F_CUTOFF', 'HB_F_SOURCE_ANCHOR', 'HB_F_PREVIOUSLY_ACCEPTED_TARGET',
        'CUTOFF_K_MODULE', 'CUTOFF_K_SOURCE_ANCHOR', 'CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET',
        'LICENSED_M_MODULE', 'LICENSED_M_FAILED_MODULE', 'LICENSED_M_SOURCE_ANCHOR',
        'LICENSED_M_PUBLIC_PATH', 'LICENSED_M_RESULT', 'LICENSED_M_WORKER',
        'LICENSED_M_ORIGINAL_TARGETS', 'LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET'}
    nodes = []
    for node in ast.parse(draft).body:
        if isinstance(node, ast.FunctionDef) and node.name in allowed_functions:
            nodes.append(node)
        elif isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in allowed_constants:
                nodes.append(node)
    ns = {'Path': Path, 're': re, 'json': json, 'SimpleNamespace': SimpleNamespace}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), '<isolated-new-Licensed-adapter>', 'exec'), ns)
    s = SimpleNamespace(h=SimpleNamespace(closure=closure))
    prior = ns['LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET']
    bound_prior = prior
    prior = deepcopy(bound_prior)
    prior['historical_group']['public_evidence']['commit'] = '__UNBOUND_N_FIXTURE__'
    ns['LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET'] = prior
    case('unbound_N_publication_holds', lambda: ns['licensed_m_source_binding'](s, graph, sources, prior), True)
    prior = bound_prior
    ns['LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET'] = prior
    case('accepted_Licensed_cannot_be_selected', lambda: ns['selection']([MODULE]), True)
    case('measured_33_33_summary_preserves_original_partial_group',
         lambda: ns['require_licensed_m_public_scope'](prior, public))
    for label, mutate in [
        ('wrong_public_count_holds', lambda obj: obj['owners'][MODULE].update(public_count=32)),
        ('partial_group_cannot_be_relabelled_success',
         lambda obj: obj.update(original_group_worker_exit_code=0, original_group_all_selected_owners_accepted=True))]:
        altered = deepcopy(public)
        mutate(altered)
        case(label, lambda obj=altered: ns['require_licensed_m_public_scope'](prior, obj), True)
    altered_prior = deepcopy(prior)
    altered_prior['historical_group']['run'] = 'runs/attempt-00001'
    case('another_attempt_cannot_replace_original_M',
         lambda: ns['licensed_m_source_binding'](s, graph, sources, altered_prior), True)

    manifest = deepcopy(manifest)
    root = ns['ROOT'] / M
    run = root / 'runs/attempt-00000'
    base = root / MODULE
    audit = base / 'audits' / prior['audit_id']
    receipts = public['owners'][MODULE]['receipt_bindings']
    paths = ns['artifact_paths'](MODULE)
    expected_artifacts = {path: None for path in paths}
    expected_artifacts[paths[0]] = {'bytes': 1, 'sha256': 'a' * 64}
    expected_source5 = {'synthetic_only': 'original-source-and-five-output-binding'}
    binding = {'module': MODULE,
        'normal_receipt': {'path': str(base / 'normal' / MODULE / 'NORMAL_PASS.json'), **receipts['normal']},
        'audits': [{'plan': {'path': str(audit / 'AUDIT_PLAN.json'), **receipts['audit_plan']},
                    'result': {'path': str(audit / 'lane-0/VALIDATION_RESULTS.json'), **receipts['audit_result']}}],
        'all_observed_target_artifacts': expected_artifacts, 'source_plus_five_outputs': expected_source5}
    ordered = [MODULE, *public['original_group_not_accepted_modules']]
    worker = {'source_commit': M, 'targets': ordered, 'accepted_owners': [MODULE],
        'failures': {FAILED: 'synthetic public source failure'}, 'acceptance_bindings': {MODULE: binding},
        'published_source_count': 360, 'selected_live_source_count': 157,
        'accepted_supplier_recompile_requested': False, 'dependency_rebuild_requested': False,
        'old_receipts_rebound': False, 'old_P3_REUSE_changed': False, 'reused_complete_selected_owners': [],
        'original_supplier_acceptance_bindings': {'synthetic_only': 'historical suppliers'},
        'direct_import_readiness': {MODULE: {
            'exit_code': 0, 'actual_built_modules': [], 'actual_failed_modules': []}}}
    original = {**deepcopy(worker), 'worker_exit_code': 1, 'all_selected_owners_accepted': False,
                'dispatch_error': 'serialized worker exited 1'}
    case('partial_RESULT_WORKER_and_exact_receipt_paths',
         lambda: ns['require_licensed_m_run_scope'](public, original, worker))
    altered = deepcopy(original)
    altered.update(worker_exit_code=0, all_selected_owners_accepted=True)
    case('original_partial_worker_cannot_be_rebound_to_success',
         lambda: ns['require_licensed_m_run_scope'](public, altered, worker), True)
    altered = deepcopy(original)
    altered['final_stock_readiness'] = {'exit_code': 0}
    case('missing_original_final_stock_cannot_be_invented',
         lambda: ns['require_licensed_m_run_scope'](public, altered, worker), True)

    retained = {run / 'RESULT.json': json.dumps(original).encode(),
                run / 'WORKER_RESULT.json': json.dumps(worker).encode()}
    model_public = deepcopy(public)
    model_public['original_result'] = raw_fingerprint(retained[run / 'RESULT.json'])
    model_public['original_worker_result'] = raw_fingerprint(retained[run / 'WORKER_RESULT.json'])
    # Isolated reader model uses synthetic JSON payloads. Production constants
    # remain the two actual M hashes; no fixture value escapes this namespace.
    ns['LICENSED_M_RESULT'] = model_public['original_result']
    ns['LICENSED_M_WORKER'] = model_public['original_worker_result']
    for stem in ('CONTEXT', 'GIT'):
        raw = ('synthetic unchanged ' + stem).encode()
        for side in ('BEFORE', 'AFTER'):
            retained[run / (stem + '_' + side + '.json')] = raw
        model_public['original_context_pairs'][stem] = {'before': raw_fingerprint(raw), 'after': raw_fingerprint(raw)}
    actual_artifacts, actual_source5 = deepcopy(expected_artifacts), deepcopy(expected_source5)
    selected14 = [module for module in ns['LICENSED_M_ORIGINAL_TARGETS'] if module != MODULE]
    active = closure(graph, selected14)
    calls, mutate_after, wrong_counts = [], [None], [False]
    s = SimpleNamespace(h=SimpleNamespace(closure=closure),
                        d=SimpleNamespace(snapshot=lambda project, module: deepcopy(actual_source5)))

    def model_read(s, spec, path, expected):
        raw = retained[path]
        need(raw_fingerprint(raw) == expected, 'synthetic retained pin differs')
        spec.retained_inputs[str(path)] = expected
        return raw

    def model_owner(s, shadow, module, validate_live):
        need(module == MODULE and validate_live is True and shadow.active is active,
             'new adapter did not use original reader inside actual active scope')
        need(shadow.manifest['accepted_suppliers'][module]['source_commit'] == M and
             shadow.manifest['accepted_supplier_groups']['licensed_m']['source_commit'] == M,
             'original M identity was rebound')
        calls.append((module, validate_live))
        shadow.supplier_evidence[module] = {'source_commit': M, 'selected_supplier_live_closure_count': 68,
            'original_group_worker_exit_code': 1, 'owned_count': 33, 'public_count': 32 if wrong_counts[0] else 33,
            'audit_plan': {'path': str(audit / 'AUDIT_PLAN.json')}}
        if mutate_after[0] == 'artifact':
            actual_artifacts[paths[1]] = {'bytes': 1, 'sha256': 'b' * 64}
        if mutate_after[0] == 'source5':
            actual_source5['synthetic_only'] = 'changed after reader'
        return SimpleNamespace(synthetic_reader_only=True)

    def spec():
        return SimpleNamespace(manifest=deepcopy(manifest), graph=graph, sources=sources, active=active,
            selected=set(selected14), retained_inputs={}, historical_groups={}, historical_owners={},
            supplier_evidence={}, dependency_pins={})

    ns.update(published_binding=lambda binding: json.dumps(model_public).encode(), retained_read=model_read,
              retained_owner=model_owner, module_artifacts=lambda s, module: deepcopy(actual_artifacts))

    def valid_adapter():
        candidate = spec()
        shared = {key: getattr(candidate, key) for key in
                  ('active', 'retained_inputs', 'historical_groups', 'historical_owners', 'supplier_evidence', 'dependency_pins')}
        result = ns['retained_licensed_m_target'](s, candidate, MODULE)
        need(result.synthetic_reader_only and calls == [(MODULE, True)], 'reader invocation differs')
        need(all(getattr(candidate, key) is value for key, value in shared.items()), 'state maps replaced')
        need(candidate.dependency_pins == {MODULE: expected_artifacts} and
             MODULE not in candidate.manifest['accepted_suppliers'], 'original partition/artifacts changed')

    case('M_reader_33_33_full21_source5_and_partial_identity_preserved', valid_adapter)
    calls.clear()
    outside = spec()
    outside.active = set()
    case('outside_actual_scope_holds', lambda: ns['retained_licensed_m_target'](s, outside, MODULE), True)
    selected = spec()
    selected.selected.add(MODULE)
    case('selected_Licensed_cannot_enter_reuse_adapter',
         lambda: ns['retained_licensed_m_target'](s, selected, MODULE), True)
    actual_artifacts[paths[1]] = {'bytes': 1, 'sha256': 'b' * 64}
    case('artifact_change_before_reader_holds', lambda: ns['retained_licensed_m_target'](s, spec(), MODULE), True)
    need(not calls, 'artifact precondition did not stop before reader')
    actual_artifacts.clear(); actual_artifacts.update(deepcopy(expected_artifacts))
    actual_source5['synthetic_only'] = 'changed before reader'
    case('source_plus_five_change_before_reader_holds', lambda: ns['retained_licensed_m_target'](s, spec(), MODULE), True)
    need(not calls, 'source5 precondition did not stop before reader')
    actual_source5.clear(); actual_source5.update(deepcopy(expected_source5))
    mutate_after[0] = 'artifact'
    case('artifact_change_after_reader_holds', lambda: ns['retained_licensed_m_target'](s, spec(), MODULE), True)
    actual_artifacts.clear(); actual_artifacts.update(deepcopy(expected_artifacts)); calls.clear()
    mutate_after[0] = 'source5'
    case('source_plus_five_change_after_reader_holds', lambda: ns['retained_licensed_m_target'](s, spec(), MODULE), True)
    actual_source5.clear(); actual_source5.update(deepcopy(expected_source5)); calls.clear()
    mutate_after[0] = None
    wrong_counts[0] = True
    case('full_reader_count_disagreement_holds', lambda: ns['retained_licensed_m_target'](s, spec(), MODULE), True)
    need(len(CASES) == case_base + 17, 'exactly 17 new Licensed cases required')


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
    prior_K_runner = git_file(PRIOR_K, 'docs/p1/20261126/p15-current-corrections/run_selected.py')
    prior_K_manifest_raw = git_file(PRIOR_K, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
    need(sha(prior_K_runner) == K_RUNNER_SHA and sha(prior_K_manifest_raw) == K_MANIFEST_SHA,
         'K entrypoint pin differs')
    prior_M_runner = git_file(PRIOR_M, 'docs/p1/20261126/p15-current-corrections/run_selected.py')
    prior_M_manifest_raw = git_file(PRIOR_M, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
    need(sha(prior_M_runner) == M_RUNNER_SHA and sha(prior_M_manifest_raw) == M_MANIFEST_SHA,
         'M entrypoint pin differs')
    prior_M_functions = functions(prior_M_runner)
    prior_M_manifest = json.loads(prior_M_manifest_raw)
    prior_K_functions = functions(prior_K_runner)
    prior_K_manifest = json.loads(prior_K_manifest_raw)
    prior_F_functions = functions(prior_F_runner)
    added = {'hb_f_source_binding', 'require_hb_f_public_scope', 'require_hb_f_run_scope',
             'retained_hb_f_target'}
    need(set(prior_K_functions) - set(prior_F_functions) == added and
         set(prior_F_functions) <= set(prior_K_functions), 'I function scope differs')
    unchanged_F_functions = [name for name in prior_F_functions if name not in ('source_manifest', 'preflight')]
    for name in unchanged_F_functions:
        need(ast.get_source_segment(prior_K_runner.decode(), prior_K_functions[name]) ==
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
    need(ast.get_source_segment(prior_K_runner.decode(), prior_K_functions['source_manifest']) == expected_source,
         'I source_manifest exceeds the HB source-binding branch')
    old_preflight = ast.get_source_segment(prior_F_runner.decode(), prior_F_functions['preflight'])
    expected_preflight = old_preflight.replace('        retained_previous_target(s, spec, module)\n',
        '        if module == HB_F_MODULE:\n'
        '            retained_hb_f_target(s, spec, module)\n'
        '        else:\n'
        '            retained_previous_target(s, spec, module)\n', 1)
    need(ast.get_source_segment(prior_K_runner.decode(), prior_K_functions['preflight']) == expected_preflight,
         'I preflight exceeds the separate HB dispatch')
    old_nodes = [node for node in ast.parse(prior_F_runner).body if not isinstance(node, ast.FunctionDef)]
    new_nodes = [node for node in ast.parse(prior_K_runner).body if not isinstance(node, ast.FunctionDef)]
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
                'E-anchored', 'J-anchored', 1).replace(
                'Previously accepted Support@B\nis always excluded from compilation and is revalidated only when a dependency.',
                'Previously accepted Support@B and HB@F\nare excluded from compilation and revalidated only inside the actual dependency closure.', 1)
            need(ast.get_source_segment(prior_K_runner.decode(), after) == expected_doc,
                 'I driver docstring exceeds the explicit anchor/HB description')
            continue
        if isinstance(before, ast.Assign) and isinstance(before.targets[0], ast.Name) and before.targets[0].id in (
                'SOURCE_ANCHOR', 'MANIFEST_SHA'):
            continue
        need(ast.get_source_segment(prior_F_runner.decode(), before) ==
             ast.get_source_segment(prior_K_runner.decode(), after), 'I changed a protected constant/import/main guard')
    need(installer_raw == git_file(PRIOR_F, 'docs/p1/20261126/p15-current-corrections/install_sources.py') ==
         git_file(PRIOR_B, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'original additive installer bytes changed')
    prior_I_runner = git_file(PRIOR_I, 'docs/p1/20261126/p15-current-corrections/run_selected.py')
    prior_I_manifest_raw = git_file(PRIOR_I, 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json')
    need(sha(prior_I_runner) == I_RUNNER_SHA and sha(prior_I_manifest_raw) == I_MANIFEST_SHA,
         'I entrypoint pin differs')
    prior_I_functions = functions(prior_I_runner)
    need(set(prior_I_functions) == set(prior_K_functions), 'K added or removed a runner function')
    for name in prior_I_functions:
        need(ast.get_source_segment(prior_K_runner.decode(), prior_K_functions[name]) ==
             ast.get_source_segment(prior_I_runner.decode(), prior_I_functions[name]),
             'I runner function bytes changed: ' + name)
    I_assignments = [node for node in ast.parse(prior_I_runner).body if isinstance(node, ast.Assign)]
    K_assignments = [node for node in ast.parse(prior_K_runner).body if isinstance(node, ast.Assign)]
    need(len(I_assignments) == len(K_assignments), 'K changed the I constant inventory')
    for before, after in zip(I_assignments, K_assignments):
        if len(before.targets) == 1 and isinstance(before.targets[0], ast.Name) and before.targets[0].id in (
                'SOURCE_ANCHOR', 'MANIFEST_SHA'):
            continue
        need(ast.get_source_segment(prior_I_runner.decode(), before) ==
             ast.get_source_segment(prior_K_runner.decode(), after), 'K changed a protected I constant or reuse mapping')
    need(installer_raw == git_file(PRIOR_I, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'I additive installer bytes changed')
    cutoff_added = {'cutoff_k_source_binding', 'require_cutoff_k_public_scope',
                    'require_cutoff_k_run_scope', 'retained_cutoff_k_target'}
    need(set(prior_M_functions) - set(prior_K_functions) == cutoff_added and
         len(prior_K_functions) == 32 and len(prior_M_functions) == 36, 'M function scope differs')
    unchanged_K_functions = [name for name in prior_K_functions if name not in ('source_manifest', 'preflight')]
    for name in unchanged_K_functions:
        need(ast.get_source_segment(prior_M_runner.decode(), prior_M_functions[name]) ==
             ast.get_source_segment(prior_K_runner.decode(), prior_K_functions[name]),
             'K function bytes changed: ' + name)
    source_K = ast.get_source_segment(prior_K_runner.decode(), prior_K_functions['source_manifest'])
    source_M = source_K.replace(
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE},",
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE},", 1).replace(
        '    for module, prior in previous.items():\n',
        '    for module, prior in previous.items():\n'
        '        if module == CUTOFF_K_MODULE:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Cutoff@K previous target classification differs')\n"
        '            cutoff_k_source_binding(s, graph, sources, prior)\n'
        '            continue\n', 1)
    need(ast.get_source_segment(prior_M_runner.decode(), prior_M_functions['source_manifest']) == source_M,
         'M source_manifest exceeds the fixed Cutoff branch')
    preflight_K = ast.get_source_segment(prior_K_runner.decode(), prior_K_functions['preflight'])
    preflight_M = preflight_K.replace(
        '        if module == HB_F_MODULE:\n'
        '            retained_hb_f_target(s, spec, module)\n'
        '        else:\n',
        '        if module == HB_F_MODULE:\n'
        '            retained_hb_f_target(s, spec, module)\n'
        '        elif module == CUTOFF_K_MODULE:\n'
        '            retained_cutoff_k_target(s, spec, module)\n'
        '        else:\n', 1)
    need(ast.get_source_segment(prior_M_runner.decode(), prior_M_functions['preflight']) == preflight_M,
         'M preflight exceeds conditional Cutoff dispatch')
    K_nodes = [node for node in ast.parse(prior_K_runner).body if not isinstance(node, ast.FunctionDef)]
    M_nodes = [node for node in ast.parse(prior_M_runner).body if not isinstance(node, ast.FunctionDef)]
    filtered_M = []
    for node in M_nodes:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in {'CUTOFF_K_MODULE', 'CUTOFF_K_SOURCE_ANCHOR', 'CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET'}:
                continue
            if name == 'PREVIOUSLY_ACCEPTED_TARGETS' and isinstance(node.value, ast.Dict) and any(
                    isinstance(key, ast.Name) and key.id == 'CUTOFF_K_MODULE' for key in node.value.keys):
                continue
        filtered_M.append(node)
    need(len(K_nodes) == len(filtered_M), 'M changed protected K top-level structure')
    for before_node, after_node in zip(K_nodes, filtered_M):
        if before_node is K_nodes[0]:
            expected_doc = ast.get_source_segment(prior_K_runner.decode(), before_node).replace(
                'J-anchored', 'L-anchored', 1).replace(
                'Previously accepted Support@B and HB@F\n',
                'Previously accepted Support@B, HB@F and Cutoff@K\n', 1)
            need(ast.get_source_segment(prior_M_runner.decode(), after_node) == expected_doc, 'M docstring exceeds its scope')
            continue
        if isinstance(before_node, ast.Assign) and isinstance(before_node.targets[0], ast.Name) and before_node.targets[0].id in (
                'SOURCE_ANCHOR', 'MANIFEST_SHA'):
            continue
        need(ast.get_source_segment(prior_K_runner.decode(), before_node) ==
             ast.get_source_segment(prior_M_runner.decode(), after_node), 'M changed protected K constants/imports/guard')
    need(installer_raw == git_file(PRIOR_K, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'K additive installer bytes changed')
    licensed_added = {'licensed_m_source_binding', 'require_licensed_m_public_scope',
                      'require_licensed_m_run_scope', 'retained_licensed_m_target'}
    need(set(current_functions) - set(prior_M_functions) == licensed_added and
         len(prior_M_functions) == 36 and len(current_functions) == 40,
         'O function scope differs from the reviewed fourth-prior extension')
    unchanged_M_functions = [name for name in prior_M_functions if name not in ('source_manifest', 'preflight')]
    for name in unchanged_M_functions:
        need(ast.get_source_segment(runner_raw.decode(), current_functions[name]) ==
             ast.get_source_segment(prior_M_runner.decode(), prior_M_functions[name]),
             'M function bytes changed: ' + name)
    source_M = ast.get_source_segment(prior_M_runner.decode(), prior_M_functions['source_manifest'])
    source_O = source_M.replace(
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE}",
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE, LICENSED_M_MODULE}", 1).replace(
        '    for module, prior in previous.items():\n        if module == CUTOFF_K_MODULE:',
        '    for module, prior in previous.items():\n'
        '        if module == LICENSED_M_MODULE:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'Licensed@M previous target classification differs')\n"
        '            licensed_m_source_binding(s, graph, sources, prior)\n'
        '            continue\n'
        '        if module == CUTOFF_K_MODULE:', 1)
    need(ast.get_source_segment(runner_raw.decode(), current_functions['source_manifest']) == source_O,
         'O source_manifest exceeds the fixed Licensed branch')
    preflight_M = ast.get_source_segment(prior_M_runner.decode(), prior_M_functions['preflight'])
    preflight_O = preflight_M.replace(
        '        elif module == CUTOFF_K_MODULE:\n            retained_cutoff_k_target(s, spec, module)',
        '        elif module == LICENSED_M_MODULE:\n            retained_licensed_m_target(s, spec, module)\n'
        '        elif module == CUTOFF_K_MODULE:\n            retained_cutoff_k_target(s, spec, module)', 1)
    need(ast.get_source_segment(runner_raw.decode(), current_functions['preflight']) == preflight_O,
         'O preflight exceeds conditional Licensed dispatch')
    M_nodes = [node for node in ast.parse(prior_M_runner).body if not isinstance(node, ast.FunctionDef)]
    O_nodes = [node for node in ast.parse(runner_raw).body if not isinstance(node, ast.FunctionDef)]
    licensed_constants = {'LICENSED_M_MODULE', 'LICENSED_M_FAILED_MODULE', 'LICENSED_M_SOURCE_ANCHOR',
        'LICENSED_M_PUBLIC_PATH', 'LICENSED_M_RESULT', 'LICENSED_M_WORKER', 'LICENSED_M_ORIGINAL_TARGETS',
        'LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET'}
    filtered_O = []
    for node in O_nodes:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            name = node.targets[0].id
            if name in licensed_constants:
                continue
            if name == 'PREVIOUSLY_ACCEPTED_TARGETS' and isinstance(node.value, ast.Dict) and any(
                    isinstance(key, ast.Name) and key.id == 'LICENSED_M_MODULE' for key in node.value.keys):
                continue
        filtered_O.append(node)
    need(len(M_nodes) == len(filtered_O), 'O changed protected M top-level structure')
    for before_node, after_node in zip(M_nodes, filtered_O):
        if before_node is M_nodes[0]:
            expected_doc = ast.get_source_segment(prior_M_runner.decode(), before_node).replace(
                'L-anchored', 'N-anchored', 1).replace(
                'Previously accepted Support@B, HB@F and Cutoff@K\n',
                'Previously accepted Support@B, HB@F, Cutoff@K and Licensed@M\n', 1)
            need(ast.get_source_segment(runner_raw.decode(), after_node) == expected_doc,
                 'O docstring exceeds N anchor and the fourth-prior scope')
            continue
        if isinstance(before_node, ast.Assign) and isinstance(before_node.targets[0], ast.Name) and before_node.targets[0].id in (
                'SOURCE_ANCHOR', 'MANIFEST_SHA'):
            continue
        need(ast.get_source_segment(prior_M_runner.decode(), before_node) ==
             ast.get_source_segment(runner_raw.decode(), after_node), 'O changed protected M constants/imports/guard')
    need(installer_raw == git_file(PRIOR_M, 'docs/p1/20261126/p15-current-corrections/install_sources.py'),
         'M additive installer bytes changed')
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
    need(len(graph) == 360 and len(closure(graph, first)) == 69, '360/69 source count differs')
    need((set(closure(graph, first)) & set(runner.TARGETS)) - set(runner.PREVIOUSLY_ACCEPTED_TARGETS) == set(first),
         'PerGroup first selection was expanded')
    prior_manifest = json.loads(prior_manifest_raw)
    for key in ('accepted_suppliers', 'accepted_supplier_groups', 'fixed_dependencies',
                'unaccepted_p3_dependencies', 'object_observation_binding'):
        need(manifest[key] == prior_manifest[key], 'original B partition or receipt identity changed: ' + key)
    prior_F_manifest = json.loads(prior_F_manifest_raw)
    prior_I_manifest = json.loads(prior_I_manifest_raw)
    historical_H_changed_sources = {module for module in graph if prior_I_manifest['project_sources'][module] !=
                                    prior_F_manifest['project_sources'][module]}
    need(historical_H_changed_sources == {CUTOFF} and
         prior_I_manifest['source_anchor_commit'] == H_REPAIR['commit'], 'historical I/H source binding differs')
    historical_J_changed_sources = {module for module in graph if prior_K_manifest['project_sources'][module] !=
                                    prior_I_manifest['project_sources'][module]}
    need(historical_J_changed_sources == {CUTOFF} and
         prior_K_manifest['source_anchor_commit'] == J_REPAIR['commit'], 'historical K/J source delta differs')
    need(all(prior_K_manifest['project_sources'][m]['all_imports'] == prior_I_manifest['project_sources'][m]['all_imports']
             for m in graph), 'historical J changed imports')
    for key in prior_K_manifest:
        if key not in ('source_anchor_commit', 'project_sources', 'target_source_origins'):
            need(prior_K_manifest[key] == prior_I_manifest[key], 'historical K changed I policy: ' + key)
    runner.published_binding(H_REPAIR)
    candidate_raw = runner.published_binding(J_REPAIR)
    need(prior_I_manifest['target_source_origins'][CUTOFF]['source_reviews'][-1] == H_REPAIR,
         'historical H repair review is not retained under H')
    for module, origin in prior_K_manifest['target_source_origins'].items():
        before_origin = prior_I_manifest['target_source_origins'][module]
        if module == CUTOFF:
            row = prior_K_manifest['project_sources'][module]
            expected = {**before_origin, 'canonical_source': {'commit': J_REPAIR['commit'],
                'path': row['path'], 'bytes': row['bytes'], 'sha256': row['sha256']},
                'source_reviews': [*before_origin['source_reviews'], J_REPAIR]}
            need(origin == expected, 'historical K exact J provenance differs')
        else:
            need(origin == before_origin, 'historical K changed unrelated provenance: ' + module)
    candidate = json.loads(candidate_raw)
    before = git_file(PRIOR_I, prior_K_manifest['project_sources'][CUTOFF]['path'])
    after = git_file(J_REPAIR['commit'], prior_K_manifest['project_sources'][CUTOFF]['path'])
    need(candidate['failed_source_commit'] == PRIOR_I and candidate['module'] == CUTOFF and
         candidate['before']['bytes'] == len(before) and candidate['before']['sha256'] == sha(before) and
         candidate['after']['bytes'] == len(after) and candidate['after']['sha256'] == sha(after) and
         len(candidate['exact_byte_splices']) == 1, 'historical J single-splice identity differs')
    splice = candidate['exact_byte_splices'][0]
    lo, hi = splice['pre_start_byte'], splice['pre_end_byte']
    need(type(lo) is int and type(hi) is int and 0 <= lo < hi <= len(before) and
         before[lo:hi] == splice['old_utf8'].encode() and
         before[:lo] + splice['new_utf8'].encode() + before[hi:] == after,
         'historical J is not its original exact expression splice')
    historical_L_changed_sources = {module for module in graph if prior_M_manifest['project_sources'][module] !=
                       prior_K_manifest['project_sources'][module]}
    need(historical_L_changed_sources == set(L_SOURCE_CHANGES), 'L source delta exceeds three scoped-infinity sources')
    need(all(prior_M_manifest['project_sources'][m]['all_imports'] == prior_K_manifest['project_sources'][m]['all_imports'] and
             prior_M_manifest['project_sources'][m]['imports'] == prior_K_manifest['project_sources'][m]['imports']
             for m in graph), 'L changed the import graph')
    for key in prior_M_manifest:
        if key not in ('source_anchor_commit', 'project_sources', 'target_source_origins',
                       'previously_accepted_targets', 'selection_guidance'):
            need(prior_M_manifest[key] == prior_K_manifest[key], 'M changed unrelated K policy: ' + key)
    need(set(prior_M_manifest) == set(prior_K_manifest), 'M changed prior_M_manifest schema')
    repairs = json.loads(runner.published_binding(L_REPAIR))
    need(repairs['failed_source_commit'] == PRIOR_K and len(repairs['files']) == 3 and
         {row['path'][:-5].replace('/', '.') for row in repairs['files']} == set(L_SOURCE_CHANGES),
         'L exact repair source set differs')
    for record in repairs['files']:
        before = git_file(PRIOR_K, record['path'])
        after = git_file(L_REPAIR['commit'], record['path'])
        need(record['before'] == {'bytes': len(before), 'sha256': sha(before)} and
             record['after'] == {'bytes': len(after), 'sha256': sha(after)} and
             len(record['exact_byte_splices']) == 1, 'L repair fingerprints differ')
        splice = record['exact_byte_splices'][0]
        lo, hi = splice['pre_start_byte'], splice['pre_end_byte']
        need(type(lo) is int and type(hi) is int and 0 <= lo < hi <= len(before) and
             before[lo:hi] == splice['old_utf8'].encode() and
             before[:lo] + splice['new_utf8'].encode() + before[hi:] == after and
             imports(before) == imports(after), 'L scope-only splice differs')
    for module, origin in prior_M_manifest['target_source_origins'].items():
        before_origin = prior_K_manifest['target_source_origins'][module]
        if module in historical_L_changed_sources:
            row = prior_M_manifest['project_sources'][module]
            expected = {**before_origin, 'canonical_source': {'commit': L_REPAIR['commit'],
                'path': row['path'], 'bytes': row['bytes'], 'sha256': row['sha256']},
                'source_reviews': [*before_origin['source_reviews'], L_REPAIR]}
            need(origin == expected, 'M did not preserve/append exact source review: ' + module)
        else:
            need(origin == before_origin, 'M changed unrelated source provenance: ' + module)
    need(prior_M_manifest['previously_accepted_targets'] == {
        **prior_K_manifest['previously_accepted_targets'], CUTOFF: runner.CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET},
        'M changed Support/HB mappings or added an unapproved previous target')
    old_guidance, guidance = prior_K_manifest['selection_guidance'], prior_M_manifest['selection_guidance']
    expected_guidance = {**old_guidance, 'minimum_first_targets': [LICENSED],
        'previously_accepted_not_compile_targets': ['ImbalancedChen.P1OriginalSingletonSupportData', HB, CUTOFF],
        'remaining_project_graph_unblocked_compile_candidates': [module for module in
            old_guidance['project_graph_unblocked_candidates'] if module not in prior_M_manifest['previously_accepted_targets']],
        'previous_target_live_reuse_condition': M_REUSE_CONDITION}
    need(guidance == expected_guidance, 'M guidance exceeds accepted Cutoff/new Licensed first selection')
    changed_sources = {module for module in graph if manifest['project_sources'][module] !=
                       prior_M_manifest['project_sources'][module]}
    need(changed_sources == {PERGROUP}, 'N changed more than the single PerGroup source')
    need(all(manifest['project_sources'][module]['imports'] == prior_M_manifest['project_sources'][module]['imports'] and
             manifest['project_sources'][module]['all_imports'] == prior_M_manifest['project_sources'][module]['all_imports']
             for module in graph), 'N changed source imports')
    need(set(manifest) == set(prior_M_manifest), 'O changed manifest schema')
    for key in manifest:
        if key not in ('source_anchor_commit', 'project_sources', 'target_source_origins',
                       'previously_accepted_targets', 'selection_guidance'):
            need(manifest[key] == prior_M_manifest[key], 'O changed unrelated M policy: ' + key)
    n_repair = json.loads(runner.published_binding(N_REPAIR))
    need(n_repair['failed_source_commit'] == PRIOR_M and
         n_repair['failed_compiler_job'] == 'job_11072d40ef774d1abb6afb1c38b215b1' and
         len(n_repair['files']) == 1 and n_repair['files'][0]['module'] == PERGROUP,
         'N repair source/run identity differs')
    n_record = n_repair['files'][0]
    before, after = git_file(PRIOR_M, n_record['path']), git_file(ANCHOR, n_record['path'])
    git_blob = lambda raw: hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    need(n_record['before'] == {'bytes': len(before), 'sha256': sha(before), 'git_blob': git_blob(before)} and
         n_record['after'] == {'bytes': len(after), 'sha256': sha(after), 'git_blob': git_blob(after)} and
         len(n_record['exact_byte_splices']) == 1, 'N repair fingerprints/splice count differ')
    n_splice = n_record['exact_byte_splices'][0]
    lo, hi = n_splice['pre_start_byte'], n_splice['pre_end_byte']
    need(type(lo) is int and type(hi) is int and 0 <= lo < hi <= len(before) and
         before[lo:hi] == n_splice['old_utf8'].encode() and
         before[:lo] + n_splice['new_utf8'].encode() + before[hi:] == after and
         imports(before) == imports(after), 'N is not the published exact two-byte proof-expression change')
    probe = json.loads(runner.published_binding(N_PROBE))
    need(probe['status'] == 'WHOLE_PERGROUP_PROBE_SUCCEEDED_NO_OWNER_OUTPUT' and
         probe['new_owner_acceptance'] is False and probe['probe']['exit_code'] == 0 and
         probe['probe']['probe_source']['bytes'] == len(after) and
         probe['probe']['probe_source']['sha256'] == sha(after) and
         probe['probe']['output_object_requested'] is False and
         probe['probe']['normal_or_kernel_acceptance_claimed'] is False,
         'N actual whole-module probe binding or scope differs')
    for module, origin in manifest['target_source_origins'].items():
        previous_origin = prior_M_manifest['target_source_origins'][module]
        if module == PERGROUP:
            row = manifest['project_sources'][module]
            expected = {**previous_origin, 'canonical_source': {'commit': ANCHOR,
                'path': row['path'], 'bytes': row['bytes'], 'sha256': row['sha256']},
                'source_reviews': [*previous_origin['source_reviews'], N_REPAIR]}
            need(origin == expected, 'O did not preserve/append exact PerGroup source review')
        else:
            need(origin == previous_origin, 'O changed unrelated source provenance: ' + module)
    for module, row in manifest['project_sources'].items():
        raw = git_file(ANCHOR, row['path'])
        need((REPO / row['path']).read_bytes() == raw,
             'current canonical source differs from published N: ' + row['path'])
        if module != PERGROUP:
            need(raw == git_file(PRIOR_M, row['path']), 'one of the other 359 sources differs from M: ' + module)
    need(manifest['previously_accepted_targets'] == {
        **prior_M_manifest['previously_accepted_targets'], LICENSED: runner.LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET},
        'O changed an older previous-target identity or added an unapproved target')
    old_guidance, guidance = prior_M_manifest['selection_guidance'], manifest['selection_guidance']
    remaining_14 = [module for module in old_guidance['subsequent_15_targets'] if module != LICENSED]
    expected_guidance = {**old_guidance, 'minimum_first_targets': [PERGROUP], 'minimum_first_source_count': 69,
        'previously_accepted_not_compile_targets': [*old_guidance['previously_accepted_not_compile_targets'], LICENSED],
        'remaining_project_graph_unblocked_compile_candidates': remaining_14,
        'subsequent_14_targets': remaining_14, 'subsequent_14_source_count': 157,
        'previous_target_live_reuse_condition': O_REUSE_CONDITION}
    need(guidance == expected_guidance, 'O guidance exceeds accepted Licensed/PerGroup first selection')
    ready = manifest['selection_guidance']['project_graph_unblocked_candidates']
    need(len(ready) == 18 and len(closure(graph, ready)) == 157, '18/157 project graph scope differs')
    blocked = set(manifest['unaccepted_p3_dependencies'])
    need(sorted(module for module in runner.TARGETS if closure(graph, [module]) & blocked) ==
         manifest['selection_guidance']['project_graph_blocked_candidates'], 'blocked candidate partition differs')
    for name, roots, reject in [('explicit_PerGroup_only', first, False), ('same_PerGroup_explicit_order', first[::-1], False),
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
    later = manifest['selection_guidance']['subsequent_14_targets']
    need(len(later) == 14 and set(later) == set(ready) - {support, HB, CUTOFF, LICENSED} and
         len(closure(graph, later)) == 157 and support_closure <= closure(graph, later), 'later actual dependency scope')
    need(manifest['selection_guidance']['remaining_project_graph_unblocked_compile_candidates'] ==
         [module for module in ready if module not in (support, HB, CUTOFF, LICENSED)], 'remaining compilation candidate guidance differs')
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

    need(len(CASES) == 54, 'original 54 fixture gates were removed or broadened')
    cutoff_group = runner.CUTOFF_K_PREVIOUSLY_ACCEPTED_TARGET['historical_group']
    cutoff_public = json.loads(runner.published_binding(cutoff_group['public_evidence']))
    need(runner.published_binding(cutoff_group['source_graph']) == prior_K_manifest_raw and
         runner.published_binding(cutoff_group['driver']) == prior_K_runner, 'Cutoff original K graph/driver differs')
    cutoff_graph = {module: row['imports'] for module, row in prior_K_manifest['project_sources'].items()}
    cutoff_closure = closure(graph, [CUTOFF])
    need(len(cutoff_closure) == 68 and cutoff_closure == closure(cutoff_graph, [CUTOFF]) and
         all(sources[module] == prior_K_manifest['project_sources'][module]['sha256'] for module in cutoff_closure) and
         not cutoff_closure.intersection(changed_sources) and CUTOFF not in closure(graph, first),
         'Cutoff K live closure changed or was incorrectly added to PerGroup first selection')
    cutoff_k_reuse_fixtures(runner, manifest, graph, sources, cutoff_public)
    need(len(CASES) == 71, 'original M 71 fixture gates were removed or broadened')
    licensed_group = runner.LICENSED_M_PREVIOUSLY_ACCEPTED_TARGET['historical_group']
    licensed_public = json.loads(runner.published_binding(licensed_group['public_evidence']))
    need(runner.published_binding(licensed_group['source_graph']) == prior_M_manifest_raw and
         runner.published_binding(licensed_group['driver']) == prior_M_runner and
         licensed_group['source_commit'] == PRIOR_M and licensed_group['public_evidence']['commit'] == ANCHOR,
         'Licensed original M graph/driver or N public publication differs')
    licensed_graph = {module: row['imports'] for module, row in prior_M_manifest['project_sources'].items()}
    licensed_closure = closure(graph, [LICENSED])
    need(len(licensed_closure) == 68 and licensed_closure == closure(licensed_graph, [LICENSED]) and
         all(sources[module] == prior_M_manifest['project_sources'][module]['sha256'] for module in licensed_closure) and
         not licensed_closure.intersection(changed_sources) and LICENSED in closure(graph, first),
         'Licensed M live closure changed or was omitted from PerGroup first selection')
    licensed_m_reuse_fixtures(runner, manifest, graph, sources, licensed_public)
    need(len(CASES) == 88, 'O must retain 71 original and exactly 17 Licensed gates')

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
    historical_I_paths = ['SOURCE_REANCHOR_I.json', 'SOURCE_REANCHOR_F.json']
    for name in historical_I_paths:
        need((HERE / name).read_bytes() == git_file(PRIOR_I, 'docs/p1/20261126/p15-current-corrections/' + name),
             'historical I/F reanchor rewritten: ' + name)
    historical_K_paths = ['SOURCE_REANCHOR_K.json']
    for name in historical_K_paths:
        need((HERE / name).read_bytes() == git_file(PRIOR_K, 'docs/p1/20261126/p15-current-corrections/' + name),
             'historical K reanchor rewritten: ' + name)
    historical_M_paths = ['SOURCE_REANCHOR_M.json']
    for name in historical_M_paths:
        need((HERE / name).read_bytes() == git_file(PRIOR_M, 'docs/p1/20261126/p15-current-corrections/' + name),
             'historical M reanchor rewritten: ' + name)
    need((REPO / H_REPAIR['path']).read_bytes() == runner.published_binding(H_REPAIR),
         'historical H proof repair record was overwritten')
    receipt = {'schema': 'p15_current_corrections_local_static_verification_v1',
        'status': 'PASS_LOCAL_SOURCE_BINDINGS_AST_PRESERVATION_AND_ISOLATED_PYTHON_FIXTURES_ONLY',
        'source_anchor_commit': ANCHOR,
        'inputs': {name: pin(HERE / name) for name in ['SOURCE_MANIFEST.json', 'FIXED_DEPENDENCY_OBSERVATIONS.json',
                                                     'run_selected.py', 'install_sources.py', 'verify_static.py', 'README.md']},
        'unchanged_original_functions': UNCHANGED, 'immutable_template_sha256': OLD_RUNNER_SHA,
        'Support_B_mapping_and_adapter_bytes_unchanged_from_F': True,
        'B_installer_bytes_unchanged': True, 'B_source_commit': PRIOR_B,
        'full_source_manifest_function_executed_including_303_fixed_dependency_policies': True,
        'H_changed_source_rows': sorted(historical_H_changed_sources),
        'historical_J_changed_source_rows': sorted(historical_J_changed_sources),
        'historical_K_other_359_source_rows_unchanged': True,
        'historical_L_changed_source_rows': sorted(historical_L_changed_sources),
        'historical_L_other_357_source_rows_unchanged': True,
        'N_changed_source_rows': sorted(changed_sources), 'other_359_M_source_rows_unchanged': True,
        'M_source_commit': PRIOR_M, 'M_runner_sha256': M_RUNNER_SHA, 'M_manifest_sha256': M_MANIFEST_SHA,
        'unchanged_M_function_bytes': unchanged_M_functions, 'N_repair_record': N_REPAIR,
        'N_single_exact_splice_verified': True, 'N_whole_module_probe': N_PROBE,
        'M_source_manifest_and_preflight_only_added_Licensed_dispatch': True,
        'K_source_commit': PRIOR_K, 'K_runner_sha256': K_RUNNER_SHA, 'K_manifest_sha256': K_MANIFEST_SHA,
        'unchanged_K_function_bytes': unchanged_K_functions,
        'K_source_manifest_and_preflight_only_added_Cutoff_dispatch': True,
        'K_installer_bytes_unchanged': True, 'L_repair_record': L_REPAIR,
        'L_three_exact_scope_splices_verified': True, 'historical_K_files_unchanged': historical_K_paths,
        'I_source_commit': PRIOR_I, 'I_runner_sha256': I_RUNNER_SHA, 'I_manifest_sha256': I_MANIFEST_SHA,
        'historical_K_unchanged_I_function_bytes': sorted(prior_I_functions),
        'I_installer_bytes_unchanged': True, 'J_repair_record': J_REPAIR,
        'J_single_exact_splice_verified': True, 'historical_I_files_unchanged': historical_I_paths,
        'F_source_commit': PRIOR_F, 'F_runner_sha256': F_RUNNER_SHA, 'F_manifest_sha256': F_MANIFEST_SHA,
        'unchanged_F_functions': unchanged_F_functions, 'unchanged_F_function_bytes': True,
        'historical_K_F_source_manifest_and_preflight_only_added_HB_dispatch': True,
        'F_installer_bytes_unchanged': True, 'H_repair_record': H_REPAIR,
        'historical_D_files_unchanged': historical_D_paths,
        'counts': {'targets': 21, 'published_project_sources': 360, 'accepted_supplier_whitelist': 17,
            'fixed_dependencies': 303, 'retained_normal_context_witnesses': 295,
            'recorded_object_dependencies': 8, 'unaccepted_P3_suppliers': 19,
            'PerGroup_first_source_closure': 69, 'PerGroup_first_preserved_dependencies': 68,
            'project_unblocked18_source_closure': 157, 'remaining_unblocked_compile_candidates': 14,
            'subsequent_14_source_closure': 157, 'previously_accepted_target_count': 4,
            'Licensed_M_source_closure': 68, 'Cutoff_K_source_closure': 68,
            'Support_B_source_closure': 109, 'HB_F_source_closure': 67},
        'Support_B_public_evidence': fixed_prior['public_evidence'],
        'Support_live_reuse_condition': 'Only when in the actual selected closure; PerGroup first closure69 excludes Support and Cutoff.',
        'HB_F_public_evidence': hb_group['public_evidence'],
        'HB_F_reuse_condition': 'Original F partial-run identity, full21 artifacts and source5 before/after the unchanged retained full audit.',
        'HB_adapter_fixtures_use_only_synthetic_readers': True,
        'Cutoff_K_public_evidence': cutoff_group['public_evidence'],
        'Cutoff_K_original_success_run': 'runs/attempt-00000',
        'Cutoff_K_actual_conditional_scope_no_expansion': True,
        'Cutoff_K_adapter_fixtures_use_only_synthetic_readers': True,
        'historical_first_54_fixture_count': 54, 'historical_Cutoff_K_fixture_count': 17,
        'old_M_fixture_count_preserved': 71, 'new_Licensed_M_fixture_count': 17,
        'Licensed_M_public_evidence': licensed_group['public_evidence'],
        'Licensed_M_original_partial_run_preserved': True,
        'Licensed_M_adapter_fixtures_use_only_synthetic_readers': True,
        'selection_fixture_subject_change': 'Two original positive selection cases now use PerGroup; accepted Licensed is rejected by the new fixed gate.',
        'original_conditional_dispatch_fixture_adaptation': 'Same actual-scope gate: PerGroup69 invokes HB@F and Licensed@M; later157 invokes all four priors; only the new branch stub/global is added.',
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
