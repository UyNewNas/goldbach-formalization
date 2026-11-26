#!/usr/bin/env python3
"""Frozen source checks and isolated acceptance fixtures. No Git/cloud/Lean work."""
import ast
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = Path(os.environ.get('P15_BASE', '/workspace/scratch/76f3bdb16a38/goldbach-p15'))
EVIDENCE = HERE.parent
OLD = BASE / 'docs/p1/20261126/p15-current-corrections'
O = 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d'
P = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
PG = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
ALLK = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
REPAIR_PATH = 'docs/p1/20261126/p15-allk-first-compile-repair/REPAIR_CANDIDATE.json'
CASES = []


def load(path, name):
    module = ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def need(ok, message):
    if not ok:
        raise AssertionError(message)


def case(name, action, reject=False):
    try:
        value = action()
    except ValueError as error:
        need(reject, name + ': ' + str(error))
        CASES.append({'case': name, 'result': 'EXPECTED_HOLD', 'reason': str(error)})
        return
    need(not reject, name + ': incorrectly allowed')
    CASES.append({'case': name, 'result': 'PASS'})
    return value


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def closure(graph, roots):
    seen, pending = set(), list(roots)
    while pending:
        name = pending.pop()
        if name not in seen:
            seen.add(name)
            pending.extend(graph[name])
    return seen


def imports(raw):
    return [name for line in re.findall(r'^import\s+([^\n]+)$', raw.decode(), re.M) for name in line.split()]


def functions(raw):
    text = raw.decode()
    return {n.name: ast.get_source_segment(text, n) for n in ast.parse(text).body if isinstance(n, ast.FunctionDef)}


def main():
    runner = load(HERE / 'run_selected.py', 'candidate_entrypoint')
    old_runner = load(OLD / 'run_selected.py', 'original_O_entrypoint')
    manifest_raw = (HERE / 'SOURCE_MANIFEST.json').read_bytes()
    manifest, old_manifest = [json.loads(path.read_bytes()) for path in
                              (HERE / 'SOURCE_MANIFEST.json', OLD / 'SOURCE_MANIFEST.json')]
    public = json.loads((EVIDENCE / 'PERGROUP_O_PUBLIC_ACCEPTANCE.json').read_bytes())
    original = {k: v for k, v in json.loads((EVIDENCE / 'OLD_O_RESULT_CAPTURE.json').read_bytes()).items()
                if k not in ('batch6', 'path')}
    # A synthetic WORKER-shaped record, derived from real captured RESULT content.
    # Neither reserialization below is asserted to reproduce an original raw digest.
    worker = {k: deepcopy(v) for k, v in original.items()
              if k not in ('worker_exit_code', 'dispatch_error', 'all_selected_owners_accepted')}
    graph = {name: row['imports'] for name, row in manifest['project_sources'].items()}
    sources = {name: row['sha256'] for name, row in manifest['project_sources'].items()}
    old_sources = {name: row['sha256'] for name, row in old_manifest['project_sources'].items()}
    prior = runner.PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET
    s = SimpleNamespace(h=SimpleNamespace(closure=closure))
    old_funcs, new_funcs = [functions(path.read_bytes()) for path in (OLD / 'run_selected.py', HERE / 'run_selected.py')]

    def preserved_functions():
        need([n for n in old_funcs if old_funcs[n] != new_funcs.get(n)] == ['source_manifest', 'preflight'],
             'old functions changed beyond classification and dispatch')
        need(set(new_funcs) - set(old_funcs) == {
            'pergroup_o_source_binding', 'require_pergroup_o_scope', 'retained_pergroup_o_target'}, 'unexpected new functions')
        need({n: runner.PREVIOUSLY_ACCEPTED_TARGETS[n] for n in old_runner.PREVIOUSLY_ACCEPTED_TARGETS} ==
             old_runner.PREVIOUSLY_ACCEPTED_TARGETS, 'original four priors changed')
        need(runner.TARGETS == old_runner.TARGETS and runner.SUPPLIER_IDENTITIES == old_runner.SUPPLIER_IDENTITIES,
             'original targets or supplier groups changed')
        block = ("        if module == PERGROUP_O_MODULE:\n"
                 "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
                 "                    'PerGroup@O previous target classification differs')\n"
                 "            pergroup_o_source_binding(s, graph, sources, prior)\n            continue\n")
        source = new_funcs['source_manifest'].replace(', LICENSED_M_MODULE, PERGROUP_O_MODULE}', ', LICENSED_M_MODULE}')
        need(source.count(block) == 1 and source.replace(block, '', 1) == old_funcs['source_manifest'],
             'source_manifest changed beyond fixed prior classification')
        block = ("        if module == PERGROUP_O_MODULE:\n            retained_pergroup_o_target(s, spec, module)\n"
                 "        elif module == HB_F_MODULE:")
        need(new_funcs['preflight'].count(block) == 1 and
             new_funcs['preflight'].replace(block, '        if module == HB_F_MODULE:', 1) == old_funcs['preflight'],
             'preflight changed beyond fixed prior dispatch')
    case('all_original_functions_preserved_except_exact_two_additions_and_four_priors_unchanged', preserved_functions)

    def manifest_scope():
        need([m for m in sources if old_manifest['project_sources'][m] != manifest['project_sources'][m]] == [ALLK],
             'source changes exceed AllK')
        for name in ('accepted_suppliers', 'accepted_supplier_groups', 'fixed_dependencies',
                     'unaccepted_p3_dependencies', 'object_observation_binding', 'targets'):
            need(old_manifest[name] == manifest[name], 'original partition/policy changed: ' + name)
        for name, row in old_manifest['project_sources'].items():
            need(all(row[k] == manifest['project_sources'][name][k] for k in ('imports', 'all_imports')),
                 'imports changed: ' + name)
        need([m for m in runner.TARGETS if old_manifest['target_source_origins'][m] != manifest['target_source_origins'][m]] == [ALLK],
             'source provenance changes exceed AllK')
        origin, old_origin = manifest['target_source_origins'][ALLK], old_manifest['target_source_origins'][ALLK]
        need(origin['source_reviews'][:-1] == old_origin['source_reviews'] and
             origin['source_reviews'][-1]['path'] == REPAIR_PATH and origin['source_reviews'][-1]['commit'] == P and
             origin['canonical_source']['commit'] == P, 'AllK historical provenance lost or new provenance misbound')
        need(runner.SOURCE_ANCHOR == manifest['source_anchor_commit'] == P and
             fp(manifest_raw)['sha256'] == runner.MANIFEST_SHA, 'P anchor or manifest pin differs')
        need(prior == manifest['previously_accepted_targets'][PG] and prior['source_commit'] == O,
             'PerGroup prior differs')
        fixed = prior['historical_group']
        for name, path in [('driver', OLD / 'run_selected.py'), ('source_graph', OLD / 'SOURCE_MANIFEST.json')]:
            need(fixed[name]['commit'] == O and fp(path.read_bytes()) == {k: fixed[name][k] for k in ('bytes', 'sha256')},
                 'original O pin differs: ' + name)
        pub = fixed['public_evidence']
        need(pub['commit'] == P and fp((EVIDENCE / 'PERGROUP_O_PUBLIC_ACCEPTANCE.json').read_bytes()) ==
             {k: pub[k] for k in ('bytes', 'sha256')} and
             pub['sha256'] == '3d69364fab09231361e4f551c2318147966c092ba2e56f3c8292675d6fb196c6',
             'actual public evidence is not pinned at P')
    case('actual_P_O_bindings_and_only_AllK_source_row_provenance_changed', manifest_scope)
    first = closure(graph, [ALLK])
    later_roots = manifest['selection_guidance']['subsequent_13_targets']
    later = closure(graph, later_roots)
    case('AllK73_dependencies72_remaining13_157_dependencies144', lambda: need(
        (len(first), len(first - {ALLK}), len(later), len(later - set(later_roots))) == (73, 72, 157, 144) and
        set(later_roots) == set(public['original_targets']) - {PG} and
        not later.intersection(manifest['unaccepted_p3_dependencies']), 'selected closure differs'))
    # RED established only a new historical-prior classification difference. O's
    # unchanged worker already knew how to reuse a same-commit completed owner.
    case('PerGroup_prior_selection_rejected', lambda: runner.selection([PG]), True)
    case('mixed_AllK_PerGroup_prior_selection_rejected', lambda: runner.selection([ALLK, PG]), True)
    case('failed_AllK_remains_selectable', lambda: need(runner.selection([ALLK]) == [ALLK], 'AllK selection failed'))
    for name in old_runner.PREVIOUSLY_ACCEPTED_TARGETS:
        case('old_prior_selection_rejected:' + name, lambda name=name: runner.selection([name]), True)

    def dispatch():
        node = ast.parse(new_funcs['preflight']).body[0]
        loop = next(n for n in ast.walk(node) if isinstance(n, ast.For) and 'previously_accepted_targets' in ast.unparse(n.iter))
        code = compile(ast.Module(body=[loop], type_ignores=[]), '<actual-candidate-dispatch>', 'exec')
        names = {'retained_pergroup_o_target': PG, 'retained_licensed_m_target': runner.LICENSED_M_MODULE,
                 'retained_hb_f_target': runner.HB_F_MODULE, 'retained_cutoff_k_target': runner.CUTOFF_K_MODULE,
                 'retained_previous_target': 'ImbalancedChen.P1OriginalSingletonSupportData'}
        for active, expected in [(first, {PG, runner.LICENSED_M_MODULE, runner.HB_F_MODULE}),
                                  (later, set(runner.PREVIOUSLY_ACCEPTED_TARGETS))]:
            called = []
            ns = dict(runner.__dict__, active=active, manifest=manifest, s=None, spec=None)
            for name, owner in names.items():
                ns[name] = lambda s, spec, module, owner=owner: called.append((owner, module))
            exec(code, ns)
            need(called == [(name, name) for name in sorted(expected)], 'prior dispatch exceeded scope or used wrong adapter')
    case('actual_candidate_preflight_dispatches_three_or_five_original_priors_only', dispatch)

    # Invoke real source_manifest against exact local frozen bytes. The local
    # reader maps explicit commit/path requests; it does not query remote Git.
    inventory = load(HERE / 'run_selected.py', 'isolated_inventory')
    entry_commit, payloads = 'a' * 40, {}
    for name, row in manifest['project_sources'].items():
        raw = (EVIDENCE / 'Part3AllKLambdaChartCorrection.lean' if name == ALLK else BASE / row['path']).read_bytes()
        for commit in (entry_commit, P): payloads[commit, row['path']] = raw
    for origin in manifest['target_source_origins'].values():
        for binding in [origin['canonical_source'], *origin['source_reviews']]:
            key = binding['commit'], binding['path']
            if key not in payloads:
                raw = (EVIDENCE / 'REPAIR_CANDIDATE.json' if binding['path'] == REPAIR_PATH else BASE / binding['path']).read_bytes()
                need(fp(raw) == {k: binding[k] for k in ('bytes', 'sha256')}, 'frozen provenance payload differs')
                payloads[key] = raw
    payloads[entry_commit, runner.MANIFEST] = manifest_raw
    payloads[entry_commit, runner.OBSERVATIONS] = (OLD / 'FIXED_DEPENDENCY_OBSERVATIONS.json').read_bytes()
    inventory.git_file = lambda commit, path: payloads[commit, path]
    inventory_s = SimpleNamespace(h=SimpleNamespace(closure=closure, imports=imports,
        module_path=lambda m: m.replace('.', '/') + '.lean'), api=SimpleNamespace(sha=lambda raw: fp(raw)['sha256']))
    checked = case('actual_source_manifest_all_360_sources_and_303_fixed_policies',
                   lambda: inventory.source_manifest(inventory_s, entry_commit, [ALLK]))
    need(checked[1] == graph and checked[2] == sources and checked[4]['selected_live_source_count'] == 73,
         'actual source_manifest output differs')
    for label, key, wrong in [
        ('unrelated_source_change', (entry_commit, manifest['project_sources'][PG]['path']), b'-- changed source\n'),
        ('old_AllK_replaces_P_repair', (entry_commit, manifest['project_sources'][ALLK]['path']),
         (BASE / manifest['project_sources'][ALLK]['path']).read_bytes()),
        ('missing_P_repair_provenance', (P, REPAIR_PATH), b'{}')]:
        saved, payloads[key] = payloads[key], wrong
        case(label + '_rejected_by_real_source_manifest', lambda: inventory.source_manifest(inventory_s, entry_commit, [ALLK]), True)
        payloads[key] = saved

    scope = lambda pub=public, orig=original, work=worker: runner.require_pergroup_o_scope(prior, pub, orig, work)
    case('actual_public_and_captured_RESULT_partial_scope', scope)
    for key, value in [('source_commit', P), ('original_group_worker_exit_code', 0),
                       ('original_group_all_selected_owners_accepted', True), ('whole_P1_5_complete', True),
                       ('normal_or_kernel_commands_executed', 1), ('selected_owner_live_closure_count', 70),
                       ('original_group_not_started_modules', public['original_targets'][1:]),
                       ('original_targets', list(reversed(public['original_targets'])))]:
        altered = deepcopy(public); altered[key] = value
        case('public_scope_change_rejected:' + key, lambda altered=altered: scope(pub=altered), True)
    for label, mutate in [
        ('public_count', lambda p: p['owners'][PG].update(public_count=68)),
        ('missing_owned_log_pin', lambda p: p['owners'][PG]['receipt_bindings'].pop('owned_log')),
        ('receipt_rebinding', lambda p: p['owners'][PG].update(receipt_rebound_to_current_commit=True)),
        ('changed_context', lambda p: p['original_context_pairs']['CONTEXT']['after'].update(sha256='0' * 64))]:
        altered = deepcopy(public); mutate(altered)
        case(label + '_rejected', lambda altered=altered: scope(pub=altered), True)
    for label, mutate in [
        ('relabel_partial_group_success', lambda r: r.update(worker_exit_code=0, all_selected_owners_accepted=True)),
        ('invent_final_stock', lambda r: r.update(final_stock_readiness={'exit_code': 0})),
        ('accept_failed_AllK', lambda r: r['accepted_owners'].append(ALLK)),
        ('reorder_original_targets', lambda r: r['targets'].reverse()),
        ('hide_started_AllK', lambda r: r['direct_import_readiness'].pop(ALLK))]:
        altered = deepcopy(original); mutate(altered)
        case(label + '_rejected', lambda altered=altered: scope(orig=altered), True)
    altered = deepcopy(worker)
    altered['acceptance_bindings'][PG]['source_plus_five_outputs']['isolated_change'] = True
    case('WORKER_disagrees_with_original_binding_rejected', lambda: scope(work=altered), True)
    altered_o, altered_w = deepcopy(original), deepcopy(worker)
    for record in (altered_o, altered_w):
        binding = record['acceptance_bindings'][PG]['normal_receipt']; binding['path'] = binding['path'].replace(O, P)
    case('receipt_paths_cannot_be_rebound_to_P', lambda: scope(orig=altered_o, work=altered_w), True)
    for label, mutate in [('another_attempt', lambda p: p['historical_group'].update(run='runs/attempt-00001')),
                          ('new_acceptance_commit', lambda p: p.update(source_commit=P)),
                          ('wrong_publication', lambda p: p['historical_group']['public_evidence'].update(commit=O))]:
        altered = deepcopy(prior); mutate(altered)
        case(label + '_source_binding_rejected', lambda altered=altered: runner.pergroup_o_source_binding(s, graph, sources, altered), True)

    # Use actual original full21/source+5 content, but synthetic serialized
    # retained records/context and a synthetic generic-reader result. Only this
    # isolated namespace substitutes receipt fingerprints for those byte strings.
    r = load(HERE / 'run_selected.py', 'isolated_adapter')
    model_public = deepcopy(public)
    run = Path(prior['historical_group']['evidence_root']) / O / prior['historical_group']['run']
    retained = {run / 'RESULT.json': json.dumps(original).encode(), run / 'WORKER_RESULT.json': json.dumps(worker).encode()}
    r.PERGROUP_O_RESULT = model_public['original_result'] = fp(retained[run / 'RESULT.json'])
    r.PERGROUP_O_WORKER = model_public['original_worker_result'] = fp(retained[run / 'WORKER_RESULT.json'])
    for stem in ('CONTEXT', 'GIT'):
        raw = ('isolated retained ' + stem).encode()
        for side in ('BEFORE', 'AFTER'): retained[run / (stem + '_' + side + '.json')] = raw
        model_public['original_context_pairs'][stem] = {'before': fp(raw), 'after': fp(raw)}
    expected = original['acceptance_bindings'][PG]
    artifacts, source5 = deepcopy(expected['all_observed_target_artifacts']), deepcopy(expected['source_plus_five_outputs'])
    calls, reads, after = [], [], [lambda spec: None]
    def read(s, spec, path, expected):
        raw = retained[path]
        r.require(fp(raw) == expected, 'isolated retained pin differs')
        spec.retained_inputs[str(path)] = expected; reads.append(path)
        return raw
    def spec():
        return SimpleNamespace(manifest=deepcopy(manifest), graph=graph, sources=dict(sources), active=first, selected={ALLK},
            retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
    current = [None]
    def owner(s, shadow, module, validate_live):
        need(module == PG and validate_live is True, 'original full reader not requested')
        for key in ('active', 'graph', 'sources', 'retained_inputs', 'historical_groups', 'historical_owners',
                    'supplier_evidence', 'dependency_pins'):
            need(getattr(shadow, key) is getattr(current[0], key), 'unshared state: ' + key)
        need(shadow.manifest['accepted_suppliers'][PG]['source_commit'] == O and
             shadow.manifest['accepted_supplier_groups']['pergroup_o'] == prior['historical_group'] and
             closure(graph, [PG]) <= shadow.active, 'historical identity or active closure changed')
        calls.append((module, validate_live))
        shadow.supplier_evidence[PG] = {'source_commit': O, 'selected_supplier_live_closure_count': 69,
            'original_group_worker_exit_code': 1, 'owned_count': 68, 'public_count': 58,
            'audit_plan': expected['audits'][0]['plan']}
        after[0](shadow)
        return SimpleNamespace(isolated_generic_reader_result=True)
    r.published_binding = lambda binding: json.dumps(model_public).encode()
    r.retained_read, r.retained_owner = read, owner
    r.module_artifacts = lambda s, module: deepcopy(artifacts)
    model_s = SimpleNamespace(h=SimpleNamespace(closure=closure), d=SimpleNamespace(snapshot=lambda project, module: deepcopy(source5)))
    def adapter(obj=None):
        current[0] = spec() if obj is None else obj
        return r.retained_pergroup_o_target(model_s, current[0], PG)
    def valid_adapter():
        candidate = spec(); saved = deepcopy(candidate.manifest)
        result = adapter(candidate)
        need(result.isolated_generic_reader_result and calls == [(PG, True)] and len(reads) == 6 and
             candidate.manifest == saved and candidate.active is first and
             candidate.dependency_pins == {PG: expected['all_observed_target_artifacts']} and
             len(candidate.dependency_pins[PG]) == 21, 'adapter did not preserve identity/state/artifacts')
    case('PerGroup_O_shared_shadow_generic_reader_full21_source5_and_partial_identity', valid_adapter)
    for label, mutate in [('inactive', lambda obj: setattr(obj, 'active', set())),
                          ('selected', lambda obj: obj.selected.add(PG)),
                          ('changed_source', lambda obj: obj.sources.update({PG: '0' * 64})),
                          ('supplier_collision', lambda obj: obj.manifest['accepted_suppliers'].update({PG: {}}))]:
        calls.clear(); obj = spec(); mutate(obj)
        case(label + '_prior_stops_before_generic_reader', lambda obj=obj: adapter(obj), True)
        need(not calls, 'scope/source precondition allowed reader')
    for name in ('WORKER_RESULT.json', 'CONTEXT_AFTER.json'):
        calls.clear(); path = run / name; saved = retained[path]; retained[path] += b'\n'
        case('changed_' + name + '_pin_stops_before_generic_reader', adapter, True)
        need(not calls, 'retained pin failure allowed reader'); retained[path] = saved
    key = next(k for k, value in artifacts.items() if value is not None)
    calls.clear(); saved = artifacts[key]; artifacts[key] = None
    case('full21_change_before_reader_holds', adapter, True)
    need(not calls, 'artifact precondition allowed reader'); artifacts[key] = saved
    calls.clear(); source5['isolated_change'] = True
    case('source5_change_before_reader_holds', adapter, True)
    need(not calls, 'source5 precondition allowed reader'); del source5['isolated_change']
    for label, mutate, reset in [
        ('full21_change_during_reader', lambda obj: artifacts.update({key: None}), lambda: artifacts.update({key: saved})),
        ('source5_change_during_reader', lambda obj: source5.update(isolated_change=True), lambda: source5.pop('isolated_change'))]:
        after[0] = mutate
        case(label + '_holds', adapter, True)
        need(not current[0].dependency_pins, 'postcondition failure installed dependency pin'); reset()
    for field, wrong in [('public_count', 68), ('source_commit', P), ('original_group_worker_exit_code', 0),
                         ('selected_supplier_live_closure_count', 157), ('audit_plan', {'path': '/isolated/wrong-audit/AUDIT_PLAN.json'})]:
        after[0] = lambda obj, field=field, wrong=wrong: obj.supplier_evidence[PG].update({field: wrong})
        case('generic_reader_disagreement_holds:' + field, adapter, True)
        need(not current[0].dependency_pins, 'reader disagreement installed dependency pin')

    # Reexecute original fixtures without editing their logic or copying 100KB.
    # Their old four-prior dispatch fixture stays historical; candidate five-prior
    # dispatch is tested above. Every involved old production function is byte-
    # identical to the candidate (the first case checked this before any fixture).
    verifier_raw = (OLD / 'verify_static.py').read_bytes()
    need(fp(verifier_raw)['sha256'] == '2280047243b163cdd0965595e916ed1d0ac69a60a8094e0414c2ad43709049b3', 'old verifier changed')
    verifier = load(OLD / 'verify_static.py', 'frozen_O_verifier')
    old_fixture_functions = ['support_reuse_fixtures', 'hb_f_reuse_fixtures', 'cutoff_k_reuse_fixtures', 'licensed_m_reuse_fixtures']
    for function, module in zip(old_fixture_functions, old_runner.PREVIOUSLY_ACCEPTED_TARGETS):
        binding = old_manifest['previously_accepted_targets'][module]['historical_group']['public_evidence']
        raw = (BASE / binding['path']).read_bytes()
        need(fp(raw) == {k: binding[k] for k in ('bytes', 'sha256')}, 'old public input changed')
        getattr(verifier, function)(old_runner, deepcopy(old_manifest), graph, dict(old_sources), json.loads(raw))
    CASES.extend({**row, 'case': 'original_O_logic:' + row['case']} for row in verifier.CASES)
    original_report = (OLD / 'STATIC_VERIFICATION.json').read_bytes()
    historical = json.loads(original_report)
    need(historical['fixture_count'] == 88, 'old 88-gate receipt differs')
    report = {
        'schema': 'p15_P_anchored_PerGroup_O_entrypoint_delta_verification_v1',
        'status': 'LOCAL_STATIC_AND_ISOLATED_FIXTURES_PASSED', 'source_anchor_commit': P,
        'inputs': {name: fp((HERE / name).read_bytes()) for name in
                   ('run_selected.py', 'SOURCE_MANIFEST.json', 'verify_delta.py', 'build_candidate.py')},
        'original_O': {'source_commit': O, 'driver': fp((OLD / 'run_selected.py').read_bytes()),
                       'manifest': fp((OLD / 'SOURCE_MANIFEST.json').read_bytes()),
                       'static_verifier': fp(verifier_raw), 'static_verification': fp(original_report),
                       'historical_fixture_count': 88, 'historical_88_fixture_receipt_preserved': True,
                       'all_historical_88_cases_rerun': False,
                       'reexecuted_original_fixture_functions': old_fixture_functions,
                       'reexecuted_original_fixture_case_count': len(verifier.CASES)},
        'unchanged_original_function_count': len(old_funcs) - 2,
        'all_original_function_bytes_preserved_except': ['source_manifest', 'preflight'],
        'changed_original_functions_only_add_classification_and_dispatch': True,
        'four_original_prior_identities_unchanged': True, 'only_AllK_source_row_changed': True,
        'all_360_local_frozen_source_bytes_checked_by_actual_source_manifest_function': True,
        'remote_Git_publication_requeried_by_this_suite': False,
        'AllK_scope': {'sources': 73, 'dependencies': 72}, 'remaining13_scope': {'sources': 157, 'dependencies': 144},
        'result_fixture_origin': 'Captured original RESULT content excluding display-only batch6/path keys.',
        'worker_fixture_origin': 'Synthetic WORKER shape derived from captured RESULT; no raw original digest claimed.',
        'new_adapter_fixtures_use_isolated_readers': True,
        'selection_RED_scope': 'O allowed PerGroup selection; this did not bypass its same-commit completed-owner reuse.',
        'cases': CASES, 'case_count': len(CASES),
        'driver_main_or_worker_executed': False, 'Lean_or_kernel_invoked': False, 'cloud_jobs_submitted': False,
        'Git_writes': False, 'original_base_tree_modified': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (HERE / 'STATIC_VERIFICATION.json').write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'status': report['status'], 'case_count': len(CASES),
                      'original_fixture_cases_reexecuted': len(verifier.CASES),
                      'unchanged_original_functions': len(old_funcs) - 2,
                      'report': fp((HERE / 'STATIC_VERIFICATION.json').read_bytes())}, indent=2))


if __name__ == '__main__':
    main()
