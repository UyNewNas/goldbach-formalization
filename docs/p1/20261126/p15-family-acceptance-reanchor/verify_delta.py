#!/usr/bin/env python3
"""Verify a truly R-bound candidate, with fixed local bytes and isolated readers."""
import ast
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import re
import sys
from types import ModuleType, SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
Q_DIR = HERE.parent / 'entrypoint'
BASE = Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
CASES = []


def load(path, name):
    mod = ModuleType(name); mod.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), mod.__dict__)
    return mod


def need(ok, message):
    if not ok: raise AssertionError(message)


def case(name, action, reject=False):
    try:
        value = action()
    except (ValueError, KeyError) as error:
        need(reject, name + ': ' + str(error))
        CASES.append({'case': name, 'result': 'EXPECTED_HOLD', 'reason': str(error)})
        return
    need(not reject, name + ': incorrectly allowed')
    CASES.append({'case': name, 'result': 'PASS'})
    return value


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def functions(raw):
    text = raw.decode()
    return {n.name: ast.get_source_segment(text, n) for n in ast.parse(text).body if isinstance(n, ast.FunctionDef)}


def imports(raw):
    return [n for line in re.findall(r'^import\s+([^\n]+)$', raw.decode(), re.M) for n in line.split()]


def main():
    need((HERE / 'PUBLISHED_INPUTS.json').is_file() and (HERE / 'BUILD_OUTPUT.json').is_file(),
         'actual R publication and generated candidate are required; no unbound success record')
    builder = load(HERE / 'build_candidate.py', 'frozen_builder')
    runner = load(HERE / 'run_selected.py', 'candidate_S')
    old = load(Q_DIR / 'run_selected.py', 'frozen_Q')
    inputs, build = [json.loads((HERE / n).read_bytes()) for n in ('PUBLISHED_INPUTS.json', 'BUILD_OUTPUT.json')]
    anchor, ALLK, ADM, FAMILY, Q = inputs['source_anchor_commit'], builder.ALLK, builder.ADM, builder.FAMILY, builder.Q
    manifest_path = Path(build['manifest_path'])
    manifest_raw = manifest_path.read_bytes()
    manifest, old_manifest = json.loads(manifest_raw), json.loads((Q_DIR / 'SOURCE_MANIFEST.json').read_bytes())
    graph = {n: row['imports'] for n, row in manifest['project_sources'].items()}
    sources = {n: row['sha256'] for n, row in manifest['project_sources'].items()}
    closure = builder.closure
    old_funcs, new_funcs = [functions(path.read_bytes()) for path in (Q_DIR / 'run_selected.py', HERE / 'run_selected.py')]
    public, result, worker = {}, {}, {}
    captured = {
        ALLK: json.loads(Path('/tmp/p15-q-evidence/AllK_final.json').read_bytes()),
        ADM: next(row for row in json.loads(Path('/tmp/p15-q-evidence/Q_later_records.json').read_bytes())
                  if row.get('batch6') == 'P15_CURRENT_CORRECTIONS_RESULT')}
    for module, key in [(ALLK, 'allk_public'), (ADM, 'admissible_public')]:
        public[module] = json.loads(builder.read_fixed(inputs['publications'][key]))
        result[module] = {k: v for k, v in captured[module].items() if k not in ('batch6', 'path')}
        worker[module] = {k: deepcopy(v) for k, v in result[module].items()
                          if k not in ('worker_exit_code', 'dispatch_error', 'all_selected_owners_accepted')}
        case('actual_original_RESULT_WORKER_bytes_recovered:' + module, lambda module=module: need(
            fp(encode(result[module])) == builder.FIXED_RUNS[module]['result'] and
            fp(encode(worker[module])) == builder.FIXED_RUNS[module]['worker'], 'captured canonical bytes differ from real run pins'))
    case('original_AllK_reuse_binding_is_exactly_same_in_both_real_Q_runs', lambda: need(
        result[ALLK]['acceptance_bindings'][ALLK] == result[ADM]['acceptance_bindings'][ALLK], 'AllK original reuse differs'))

    def preserved():
        need(fp((Q_DIR / 'run_selected.py').read_bytes()) == builder.Q_RUNNER_FP and
             fp((Q_DIR / 'SOURCE_MANIFEST.json').read_bytes()) == builder.Q_MANIFEST_FP, 'Q base differs')
        need(len(old_funcs) == 43 and [n for n in old_funcs if old_funcs[n] != new_funcs.get(n)] == ['source_manifest', 'preflight'],
             'Q functions changed beyond two fixed dispatch functions')
        need(set(new_funcs) - set(old_funcs) == {'q_prior_source_binding', 'require_q_prior_scope', 'retained_q_prior_target'},
             'new function set differs')
        need({n: runner.PREVIOUSLY_ACCEPTED_TARGETS[n] for n in old.PREVIOUSLY_ACCEPTED_TARGETS} == old.PREVIOUSLY_ACCEPTED_TARGETS,
             'one of the five original priors changed')
        need(runner.TARGETS == old.TARGETS and runner.SUPPLIER_IDENTITIES == old.SUPPLIER_IDENTITIES,
             'original target/supplier identities changed')
        block = ("        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:\n"
                 "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
                 "                    'Q prior classification differs: ' + module)\n"
                 "            q_prior_source_binding(s, graph, sources, module, prior)\n            continue\n")
        function = new_funcs['source_manifest'].replace(' | set(Q_PREVIOUSLY_ACCEPTED_TARGETS),', ',')
        need(function.count(block) == 1 and function.replace(block, '', 1) == old_funcs['source_manifest'],
             'source_manifest cannot reverse to exact Q bytes')
        block = ("        if module in Q_PREVIOUSLY_ACCEPTED_TARGETS:\n            retained_q_prior_target(s, spec, module)\n"
                 "        elif module == PERGROUP_O_MODULE:")
        need(new_funcs['preflight'].count(block) == 1 and
             new_funcs['preflight'].replace(block, '        if module == PERGROUP_O_MODULE:', 1) == old_funcs['preflight'],
             'preflight cannot reverse to exact Q bytes')
    case('41_Q_functions_and_five_old_priors_preserved_exact_two_splices', preserved)

    def manifest_checks():
        need(anchor == build['source_anchor_commit'] == runner.SOURCE_ANCHOR == manifest['source_anchor_commit'] and
             fp(manifest_raw) == build['manifest'] and fp(manifest_raw)['sha256'] == runner.MANIFEST_SHA and
             fp((HERE / 'run_selected.py').read_bytes()) == build['runner'], 'actual R/runner/manifest binding differs')
        need([n for n in graph if manifest['project_sources'][n] != old_manifest['project_sources'][n]] == [FAMILY] and
             [n for n in runner.TARGETS if manifest['target_source_origins'][n] != old_manifest['target_source_origins'][n]] == [FAMILY],
             'source/provenance change exceeds Family')
        for name in ('targets', 'accepted_suppliers', 'accepted_supplier_groups', 'fixed_dependencies',
                     'unaccepted_p3_dependencies', 'object_observation_binding'):
            need(manifest[name] == old_manifest[name], 'partition/policy changed: ' + name)
        for name in graph:
            need(all(manifest['project_sources'][name][k] == old_manifest['project_sources'][name][k]
                     for k in ('imports', 'all_imports')), 'literal imports changed: ' + name)
        origin = manifest['target_source_origins'][FAMILY]
        need(origin['source_reviews'][:-1] == old_manifest['target_source_origins'][FAMILY]['source_reviews'] and
             origin['canonical_source']['commit'] == anchor and
             origin['source_reviews'][-1] == {'commit': anchor, 'path': inputs['publications']['family_repair']['path'],
                **fp(builder.read_fixed(inputs['publications']['family_repair']))}, 'Family provenance append differs')
        for module in (ALLK, ADM):
            prior = runner.Q_PREVIOUSLY_ACCEPTED_TARGETS[module]
            need(prior == manifest['previously_accepted_targets'][module] and prior['source_commit'] == Q and
                 prior['historical_group']['public_evidence']['commit'] == anchor and
                 prior['historical_group']['source_graph']['commit'] == prior['historical_group']['driver']['commit'] == Q,
                 'Q acceptance rebound')
    case('actual_R_publications_only_Family_359_unchanged_and_receipts_stay_Q', manifest_checks)
    first, later_roots = closure(graph, [FAMILY]), manifest['selection_guidance']['subsequent_11_targets']
    later = closure(graph, later_roots)
    case('Family75_74_later11_157_146_watch160', lambda: need(
        (len(first), len(first - {FAMILY}), len(later), len(later - set(later_roots)), len(later | set(runner.TARGETS))) ==
        (75, 74, 157, 146, 160) and set(later_roots) == set(builder.LATER13) - {ALLK, ADM} and
        not later.intersection(manifest['unaccepted_p3_dependencies']), 'actual scopes differ'))
    for module in runner.PREVIOUSLY_ACCEPTED_TARGETS:
        case('historical_prior_not_selectable:' + module, lambda module=module: runner.selection([FAMILY, module]), True)
    case('Family_remains_selectable', lambda: need(runner.selection([FAMILY]) == [FAMILY], 'Family rejected'))

    def dispatch():
        loop = next(n for n in ast.walk(ast.parse(new_funcs['preflight'])) if isinstance(n, ast.For)
                    and 'previously_accepted_targets' in ast.unparse(n.iter))
        code = compile(ast.Module(body=[loop], type_ignores=[]), '<actual-S-prior-dispatch>', 'exec')
        for active, expected in [(first, {ALLK, ADM, runner.PERGROUP_O_MODULE, runner.LICENSED_M_MODULE, runner.HB_F_MODULE}),
                                  (later, set(runner.PREVIOUSLY_ACCEPTED_TARGETS))]:
            calls = []
            ns = dict(runner.__dict__, active=active, manifest=manifest, s=None, spec=None)
            for name in ('retained_q_prior_target', 'retained_pergroup_o_target', 'retained_licensed_m_target',
                         'retained_hb_f_target', 'retained_cutoff_k_target', 'retained_previous_target'):
                ns[name] = lambda s, spec, module, name=name: calls.append((name, module))
            exec(code, ns)
            need([module for _, module in calls] == sorted(expected) and
                 {module for name, module in calls if name == 'retained_q_prior_target'} == {ALLK, ADM},
                 'actual prior dispatch changed or enlarged active scope')
    case('actual_preflight_only_five_or_seven_priors_and_two_generic_Q_calls', dispatch)

    # Actual source_manifest, exact local frozen byte readers, no remote Git.
    inv, payloads, current = load(HERE / 'run_selected.py', 'local_source_inventory'), {}, 'a' * 40
    repair_path = inputs['publications']['family_repair']['path']
    local_special = {
        manifest['project_sources'][ALLK]['path']: HERE.parent / 'Part3AllKLambdaChartCorrection.lean',
        manifest['project_sources'][FAMILY]['path']: Path(inputs['family_source']['local_path']),
        'docs/p1/20261126/p15-allk-first-compile-repair/REPAIR_CANDIDATE.json': HERE.parent / 'REPAIR_CANDIDATE.json',
        repair_path: Path(inputs['publications']['family_repair']['local_path'])}
    for name, row in manifest['project_sources'].items():
        raw = local_special.get(row['path'], BASE / row['path']).read_bytes()
        for commit in (current, anchor): payloads[commit, row['path']] = raw
    for origin in manifest['target_source_origins'].values():
        for binding in [origin['canonical_source'], *origin['source_reviews']]:
            key = binding['commit'], binding['path']
            if key not in payloads:
                raw = local_special.get(binding['path'], BASE / binding['path']).read_bytes()
                need(fp(raw) == {k: binding[k] for k in ('bytes', 'sha256')}, 'provenance bytes differ: ' + binding['path'])
                payloads[key] = raw
    payloads[current, inv.MANIFEST] = manifest_raw
    payloads[current, inv.OBSERVATIONS] = (BASE / inv.OBSERVATIONS).read_bytes()
    inv.git_file = lambda commit, path: payloads[commit, path]
    inv_s = SimpleNamespace(h=SimpleNamespace(closure=closure, imports=imports,
        module_path=lambda m: m.replace('.', '/') + '.lean'), api=SimpleNamespace(sha=lambda raw: fp(raw)['sha256']))
    checked = case('actual_source_manifest360_provenance_and303_policies', lambda: inv.source_manifest(inv_s, current, [FAMILY]))
    need(checked[1] == graph and checked[2] == sources and checked[4]['selected_live_source_count'] == 75, 'source manifest output differs')
    for label, key, wrong in [
        ('unrelated_source', (current, manifest['project_sources'][ADM]['path']), b'changed\n'),
        ('old_Family_source', (current, manifest['project_sources'][FAMILY]['path']), (BASE / manifest['project_sources'][FAMILY]['path']).read_bytes()),
        ('missing_R_provenance', (anchor, repair_path), b'{}')]:
        saved, payloads[key] = payloads[key], wrong
        case(label + '_held_before_live_work', lambda: inv.source_manifest(inv_s, current, [FAMILY]), True)
        payloads[key] = saved

    for module in (ALLK, ADM):
        prior, pub, orig, work = runner.Q_PREVIOUSLY_ACCEPTED_TARGETS[module], public[module], result[module], worker[module]
        scope = lambda pub=pub, orig=orig, work=work, module=module, prior=prior: runner.require_q_prior_scope(module, prior, pub, orig, work)
        case('actual_published_Q_scope:' + module, scope)
        for field, value in [('source_commit', anchor), ('owner_live_source_closure_count', 74),
                             ('selected_owners_revalidated', [module]), ('current_read_live_source_count', 73),
                             ('normal_or_kernel_commands_executed', 1), ('original_run', 'runs/attempt-99999'),
                             ('original_group_worker_exit_code', 1 - builder.FIXED_RUNS[module]['exit_code'])]:
            changed = deepcopy(pub); changed[field] = value
            case('wrong_public_' + field + ':' + module, lambda changed=changed: scope(pub=changed), True)
        for label, mutate in [
            ('count', lambda p: p['owners'][module].update(public_count=999)),
            ('sixth_pin', lambda p: p['owners'][module]['receipt_bindings'].pop('owned_log')),
            ('receipt_path', lambda p: p['owners'][module]['receipt_paths'].update(normal='/wrong/NORMAL_PASS.json')),
            ('context', lambda p: p['original_context_pairs']['GIT']['after'].update(sha256='0' * 64))]:
            changed = deepcopy(pub); mutate(changed)
            case('wrong_public_' + label + ':' + module, lambda changed=changed: scope(pub=changed), True)
        for label, mutate in [
            ('acceptance_set', lambda r: r['accepted_owners'].append(FAMILY)),
            ('reused_identity', lambda r: r['reused_complete_selected_owners'].append(ADM)),
            ('rebound_commit', lambda r: r.update(source_commit=anchor))]:
            changed = deepcopy(orig); mutate(changed)
            case('wrong_original_' + label + ':' + module, lambda changed=changed: scope(orig=changed), True)
        changed = deepcopy(work); changed['acceptance_bindings'][module]['source_plus_five_outputs']['changed'] = True
        case('RESULT_WORKER_disagreement:' + module, lambda: scope(work=changed), True)
        if module == ALLK:
            changed = deepcopy(orig); changed.pop('final_stock_readiness')
            case('AllK_success_cannot_lose_final_stock', lambda: scope(orig=changed), True)
            changed = deepcopy(pub); changed['original_final_stock_readiness']['log']['path'] = '/wrong/final-stock-readiness.log'
            case('AllK_final_stock_path_cannot_change', lambda: scope(pub=changed), True)
        else:
            changed = deepcopy(orig); changed['final_stock_readiness'] = {'exit_code': 0}
            case('later13_failure_cannot_gain_final_stock', lambda: scope(orig=changed), True)
            changed = deepcopy(pub); changed['original_group_not_started_modules'] = pub['original_group_not_accepted_modules']
            case('later13_started_Family_cannot_be_hidden', lambda: scope(pub=changed), True)

        # Isolated retained bytes and generic-reader output; production pins and
        # captured original bytes above are never changed. Synthetic context/log
        # fingerprints below belong only to this temporary module namespace.
        r = load(HERE / 'run_selected.py', 'isolated_adapter_' + module.rsplit('.', 1)[-1])
        model_public, model_orig, model_work = deepcopy(pub), deepcopy(orig), deepcopy(work)
        fixed = prior['historical_group']; base = Path(fixed['evidence_root']) / Q; run = base / fixed['run']
        retained = {base / 'runs/attempt-00000/RESULT.json': encode(result[ALLK])}
        for stem in ('CONTEXT', 'GIT'):
            raw = ('isolated unchanged ' + stem).encode()
            for side in ('BEFORE', 'AFTER'): retained[run / (stem + '_' + side + '.json')] = raw
            model_public['original_context_pairs'][stem] = {'before': fp(raw), 'after': fp(raw)}
        if module == ALLK:
            stock = model_orig['final_stock_readiness']; log = b'isolated stock readiness log\n'
            stock.update(log_bytes=len(log), log_sha256=fp(log)['sha256'])
            model_work['final_stock_readiness'] = deepcopy(stock)
            retained[run / 'final-stock-readiness.log'] = log
            retained[run / 'final-stock-readiness-command.json'] = encode(stock)
            for key, name in [('command', 'final-stock-readiness-command.json'), ('log', 'final-stock-readiness.log')]:
                model_public['original_final_stock_readiness'][key] = {'path': str(run / name), **fp(retained[run / name])}
        for key, name, record in [('result', 'RESULT.json', model_orig), ('worker', 'WORKER_RESULT.json', model_work)]:
            retained[run / name] = encode(record)
            r.Q_PRIOR_RUNS[module][key] = fp(retained[run / name])
            model_public['original_' + ('result' if key == 'result' else 'worker_result')] = fp(retained[run / name])
        expected = orig['acceptance_bindings'][module]
        artifacts, source5 = deepcopy(expected['all_observed_target_artifacts']), deepcopy(expected['source_plus_five_outputs'])
        calls, after, current_spec = [], [lambda obj: None], [None]
        def make_spec():
            return SimpleNamespace(manifest=deepcopy(manifest), graph=graph, sources=dict(sources), active=first, selected={FAMILY},
                retained_inputs={}, historical_groups={}, historical_owners={}, supplier_evidence={}, dependency_pins={})
        def read(s, spec, path, expected):
            raw = retained[path]
            r.require(fp(raw) == expected, 'isolated retained pin differs')
            spec.retained_inputs[str(path)] = expected
            return raw
        def owner(s, shadow, selected_module, validate_live):
            need(selected_module == module and validate_live is True, 'fixed generic reader call differs')
            for key in ('active', 'graph', 'sources', 'retained_inputs', 'historical_groups', 'historical_owners', 'supplier_evidence', 'dependency_pins'):
                need(getattr(shadow, key) is getattr(current_spec[0], key), 'unshared original state: ' + key)
            need(shadow.manifest['accepted_suppliers'][module]['source_commit'] == Q and
                 shadow.manifest['accepted_supplier_groups'][prior['group']] == fixed and closure(graph, [module]) <= shadow.active,
                 'generic reader identity/active scope differs')
            calls.append((module, validate_live))
            shadow.supplier_evidence[module] = {'source_commit': Q, 'selected_supplier_live_closure_count': prior['live_source_closure_count'],
                'original_group_worker_exit_code': builder.FIXED_RUNS[module]['exit_code'],
                'owned_count': prior['owned_count'], 'public_count': prior['public_count'], 'audit_plan': expected['audits'][0]['plan']}
            after[0](shadow)
            return SimpleNamespace(isolated_reader_result=True)
        r.retained_read, r.retained_owner = read, owner
        r.published_binding = lambda binding: encode(model_public)
        r.module_artifacts = lambda s, selected_module: deepcopy(artifacts)
        stock_argv = result[ALLK]['final_stock_readiness']['argv']; prefix = stock_argv[:stock_argv.index('lake')]
        model_s = SimpleNamespace(h=SimpleNamespace(closure=closure, guard=lambda lane, cmd: prefix + cmd),
                                  d=SimpleNamespace(snapshot=lambda project, selected_module: deepcopy(source5)))
        def adapter(obj=None):
            current_spec[0] = make_spec() if obj is None else obj
            return r.retained_q_prior_target(model_s, current_spec[0], module)
        def valid_adapter():
            obj = make_spec(); saved = deepcopy(obj.manifest); got = adapter(obj)
            need(got.isolated_reader_result and calls == [(module, True)] and obj.manifest == saved and obj.active is first and
                 obj.dependency_pins == {module: expected['all_observed_target_artifacts']}, 'shared prior adapter changed partition/pins')
        case('shared_generic_reader_full21_source5_original_Q_identity:' + module, valid_adapter)
        for label, mutate in [('inactive', lambda obj: setattr(obj, 'active', set())),
                              ('selected', lambda obj: obj.selected.add(module)),
                              ('source', lambda obj: obj.sources.update({module: '0' * 64})),
                              ('collision', lambda obj: obj.manifest['accepted_suppliers'].update({module: {}}))]:
            calls.clear(); obj = make_spec(); mutate(obj)
            case('hold_before_reader_' + label + ':' + module, lambda obj=obj: adapter(obj), True)
            need(not calls, 'invalid prior reached generic reader')
        for name in ('WORKER_RESULT.json', 'CONTEXT_AFTER.json'):
            calls.clear(); path = run / name; saved = retained[path]; retained[path] += b'\n'
            case('hold_changed_' + name + ':' + module, adapter, True)
            need(not calls, 'changed retained evidence reached reader'); retained[path] = saved
        if module == ALLK:
            calls.clear(); path = run / 'final-stock-readiness.log'; saved = retained[path]; retained[path] += b'changed'
            case('AllK_final_stock_log_change_holds', adapter, True)
            need(not calls, 'changed final stock log reached reader'); retained[path] = saved
        else:
            calls.clear(); path = base / 'runs/attempt-00000/RESULT.json'; saved = retained[path]; retained[path] += b'\n'
            case('later13_reuse_requires_first_Q_RESULT_pin', adapter, True)
            need(not calls, 'changed original AllK result reached reader'); retained[path] = saved
        key = next(k for k, value in artifacts.items() if value is not None)
        calls.clear(); saved_artifact = artifacts[key]; artifacts[key] = None
        case('full21_prechange_holds:' + module, adapter, True)
        need(not calls, 'changed current artifact reached reader'); artifacts[key] = saved_artifact
        calls.clear(); source5['isolated_change'] = True
        case('source5_prechange_holds:' + module, adapter, True)
        need(not calls, 'changed source5 reached reader'); del source5['isolated_change']
        for label, mutate, reset in [
            ('full21', lambda obj: artifacts.update({key: None}), lambda: artifacts.update({key: saved_artifact})),
            ('source5', lambda obj: source5.update(isolated_change=True), lambda: source5.pop('isolated_change'))]:
            after[0] = mutate
            case(label + '_postchange_holds:' + module, adapter, True)
            need(not current_spec[0].dependency_pins, 'postchange installed dependency pins'); reset()
        for field, wrong in [('source_commit', anchor), ('public_count', 999), ('selected_supplier_live_closure_count', 157),
                             ('original_group_worker_exit_code', 1 - builder.FIXED_RUNS[module]['exit_code']),
                             ('audit_plan', {'path': '/wrong/audit/AUDIT_PLAN.json'})]:
            after[0] = lambda obj, field=field, wrong=wrong: obj.supplier_evidence[module].update({field: wrong})
            case('generic_reader_' + field + '_mismatch_holds:' + module, adapter, True)
            need(not current_spec[0].dependency_pins, 'reader disagreement installed dependency pins')

    old_verification = (Q_DIR / 'STATIC_VERIFICATION.json').read_bytes()
    need(fp(old_verification) == {'bytes': 23921, 'sha256': '2f206cde0012c561da5464b50716b3c793ead042aea3b0f34d512d3f4ad53fa2'} and
         json.loads(old_verification)['case_count'] == 116, 'original Q 116-case receipt changed')
    report = {'schema': 'p15_R_anchored_two_Q_priors_entrypoint_delta_verification_v1',
        'status': 'LOCAL_STATIC_AND_ISOLATED_FIXTURES_PASSED', 'source_anchor_commit': anchor,
        'inputs': {name: fp((HERE / name).read_bytes()) for name in
                   ('run_selected.py', 'q_prior_adapter.py', 'build_candidate.py', 'verify_delta.py', 'PUBLISHED_INPUTS.json')},
        'source_manifest': {'path': str(manifest_path), **fp(manifest_raw)},
        'original_Q': {'source_commit': Q, 'runner': builder.Q_RUNNER_FP, 'manifest': builder.Q_MANIFEST_FP,
                       'static_verification': fp(old_verification), '116_case_receipt_preserved': True,
                       'historical_fixture_suites_rerun': False},
        'unchanged_Q_function_count': 41, 'changed_Q_functions_only_add_fixed_prior_classification_and_dispatch': True,
        'five_old_prior_identities_unchanged': True, 'new_fixed_generic_functions': 3,
        'actual_original_RESULT_WORKER_bytes_recovered_and_matching_real_pins': True,
        'only_Family_source_row_changed': True, 'other_359_source_rows_and_all_imports_unchanged': True,
        'actual_source_manifest_function_360_source_provenance_303_fixed_policies_checked': True,
        'remote_Git_requeried': False, 'Family_scope': {'sources': 75, 'dependencies': 74},
        'later11_scope': {'sources': 157, 'dependencies': 146, 'all_roots_artifact_watch': 160},
        'joint_original_public_collection_scope_preserved': {'sources': 74, 'dependencies': 72},
        'original_AllK_success_final_stock_preserved': True, 'original_later13_partial_failure_preserved': True,
        'adapter_fixtures_use_synthetic_context_log_bytes_and_generic_reader_output': True,
        'cases': CASES, 'case_count': len(CASES),
        'driver_main_worker_or_installer_run': False, 'Lean_or_kernel_run': False, 'cloud_jobs': False,
        'Git_writes': False, 'old_Q_entrypoint_modified': False, 'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    output = manifest_path.parent / 'STATIC_VERIFICATION.json'
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(json.dumps({'status': report['status'], 'case_count': len(CASES), 'report_path': str(output), 'report': fp(output.read_bytes())}, indent=2))


if __name__ == '__main__':
    main()
