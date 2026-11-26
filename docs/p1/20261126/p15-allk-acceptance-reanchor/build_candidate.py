#!/usr/bin/env python3
"""Build the P-anchored candidate from frozen O inputs; no Git/cloud writes."""
import ast
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import pprint
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
REL = 'docs/p1/20261126/p15-current-corrections'
O = 'dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d'
P = 'b45d33fc0f8e2b2ac97a5919d5c7af120f11fa9f'
N = 'c47ea640bf40c22423aec7066c13e5b05956d349'
PG = 'ImbalancedChen.P5PerGroupIntegerHBAtlasPushforward'
ALLK = 'ImbalancedChen.Part3AllKLambdaChartCorrection'
PUBLIC_PATH = 'docs/p1/20261125/p15-current-public-acceptance/PERGROUP_O_PUBLIC_ACCEPTANCE.json'
REPAIR_PATH = 'docs/p1/20261126/p15-allk-first-compile-repair/REPAIR_CANDIDATE.json'


def fingerprint(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def frozen(path, count, digest):
    raw = path.read_bytes()
    assert fingerprint(raw) == {'bytes': count, 'sha256': digest}, str(path)
    return raw


def replace_once(text, before, after):
    assert text.count(before) == 1, before[:120]
    return text.replace(before, after, 1)


ADAPTER = r'''
# PerGroup remains accepted at O. P publishes only its bounded original receipts
# and the repaired AllK source; the failed fourteen-target run stays failed.
{constants}
PREVIOUSLY_ACCEPTED_TARGETS = {{
    **PREVIOUSLY_ACCEPTED_TARGETS, PERGROUP_O_MODULE: PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET}}


def pergroup_o_source_binding(s, graph, sources, prior):
    require(prior == PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET and
            sources[PERGROUP_O_MODULE] == prior['source_sha256'] and
            len(s.h.closure(graph, [PERGROUP_O_MODULE])) == prior['live_source_closure_count'] == 69,
            'fixed PerGroup@O source/69-module closure differs')


def require_pergroup_o_scope(prior, public, original, worker):
    fixed, module = prior['historical_group'], PERGROUP_O_MODULE
    expected = {{
        'schema': 'p15_O_original_accepted_prefix_public_acceptance_v1',
        'status': 'ORIGINAL_O_ACCEPTED_OWNERS_REVALIDATED_WITHOUT_EXECUTION',
        'source_commit': prior['source_commit'], 'source_anchor_commit': PERGROUP_O_SOURCE_ANCHOR,
        'compiler_job': fixed['compiler_job'], 'driver': fixed['driver'],
        'source_manifest': fixed['source_graph'], 'original_run': fixed['run'],
        'published_source_count': 360, 'original_group_live_closure_count': 157,
        'selected_owner_live_closure_count': 69, 'preserved_dependency_count': 68,
        'selected_owners_revalidated': [module], 'original_targets': PERGROUP_O_ORIGINAL_TARGETS,
        'original_group_accepted_owners': [module],
        'original_group_failed_modules': [PERGROUP_O_FAILED_MODULE],
        'original_group_not_accepted_modules': PERGROUP_O_ORIGINAL_TARGETS[1:],
        'original_group_not_started_modules': PERGROUP_O_ORIGINAL_TARGETS[2:],
        'original_group_worker_exit_code': 1, 'original_group_all_selected_owners_accepted': False,
        'original_result': PERGROUP_O_RESULT, 'original_worker_result': PERGROUP_O_WORKER,
        'source_runtime_and_original_receipts_unchanged': True,
        'normal_or_kernel_commands_executed': 0, 'types_or_archives_exported': False,
        'axiom_union_exported': False, 'whole_P1_5_complete': False,
        'original_final_stock_readiness': {{'recorded': False,
            'reason': 'original_attempt_stopped_after_owner_failure', 'executed_again_by_collector': False}},
    }}
    require(all(public.get(key) == value and type(public.get(key)) is type(value)
                for key, value in expected.items()) and set(public['owners']) == {{module}},
            'fixed PerGroup@O bounded public identity or original partial run differs')
    owner = public['owners'][module]
    require(owner['source_commit'] == prior['source_commit'] and
            owner['source_sha256'] == prior['source_sha256'] and
            type(owner['owned_count']) is int and type(owner['public_count']) is int and
            (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                (prior['owned_count'], prior['public_count'], prior['audit_id']) and
            owner['normal_kernel_full_owned_revalidated_without_execution'] is True and
            owner['source_plus_five_and_all_21_artifacts_bound_to_original_result'] is True and
            owner['receipt_rebound_to_current_commit'] is False and
            all(valid_fingerprint(owner['receipt_bindings'].get(key)) for key in
                ('normal', 'audit_plan', 'audit_result', 'owned_exports', 'owned_log', 'reused_normal_evidence')) and
            set(public['original_context_pairs']) == {{'CONTEXT', 'GIT'}} and
            all(set(pair) == {{'before', 'after'}} and valid_fingerprint(pair['before']) and
                pair['before'] == pair['after'] for pair in public['original_context_pairs'].values()),
            'PerGroup@O complete receipt/count/context pins differ')
    for record in (original, worker):
        require(record['source_commit'] == prior['source_commit'] and
                record['targets'] == PERGROUP_O_ORIGINAL_TARGETS and
                record['accepted_owners'] == [module] and set(record['acceptance_bindings']) == {{module}} and
                set(record['failures']) == {{PERGROUP_O_FAILED_MODULE}} and
                record['published_source_count'] == 360 and record['selected_live_source_count'] == 157 and
                record['whole_P1_complete'] is False and record['whole_P1_5_complete'] is False and
                record['accepted_supplier_recompile_requested'] is False and
                record['dependency_rebuild_requested'] is False and record['old_receipts_rebound'] is False and
                record['old_P3_REUSE_changed'] is False and record['reused_complete_selected_owners'] == [] and
                set(record['direct_import_readiness']) == {{module, PERGROUP_O_FAILED_MODULE}} and
                not any(key in record for key in ('context_error', 'final_context_error', 'git_error',
                                                 'final_stock_readiness')),
                'PerGroup@O original first-14 partial run differs')
    require('dispatch_error' not in worker and original['dispatch_error'] == 'serialized worker exited 1' and
            original['worker_exit_code'] == 1 and original['all_selected_owners_accepted'] is False and
            all(original[key] == worker[key] for key in
                ('targets', 'failures', 'acceptance_bindings', 'direct_import_readiness',
                 'original_supplier_acceptance_bindings')),
            'PerGroup@O original partial RESULT/WORKER identity differs')
    ready = original['direct_import_readiness'][module]
    require(ready['exit_code'] == 0 and ready['actual_built_modules'] == [] and
            ready['actual_failed_modules'] == [], 'PerGroup@O accepted owner import readiness differs')
    base = Path(fixed['evidence_root']) / prior['source_commit'] / module
    audit, receipts = base / 'audits' / owner['audit_id'], owner['receipt_bindings']
    binding = original['acceptance_bindings'][module]
    require(binding['module'] == module and binding['normal_receipt'] == {{
                'path': str(base / 'normal' / module / 'NORMAL_PASS.json'), **receipts['normal']}} and
            binding['audits'] == [{{
                'plan': {{'path': str(audit / 'AUDIT_PLAN.json'), **receipts['audit_plan']}},
                'result': {{'path': str(audit / 'lane-0/VALIDATION_RESULTS.json'), **receipts['audit_result']}}}}],
            'PerGroup@O public receipt paths/pins differ from original acceptance')


def retained_pergroup_o_target(s, spec, module):
    require(module == PERGROUP_O_MODULE and module in spec.active and module not in spec.selected,
            'PerGroup@O reuse is outside the actual dependency scope')
    prior = spec.manifest['previously_accepted_targets'][module]
    pergroup_o_source_binding(s, spec.graph, spec.sources, prior)
    require(module not in spec.manifest['accepted_suppliers'] and
            prior['group'] not in spec.manifest['accepted_supplier_groups'], 'PerGroup@O overlay group collides')
    fixed = prior['historical_group']
    public = json.loads(published_binding(fixed['public_evidence']))
    run = Path(fixed['evidence_root']) / prior['source_commit'] / fixed['run']
    original = json.loads(retained_read(s, spec, run / 'RESULT.json', PERGROUP_O_RESULT))
    worker = json.loads(retained_read(s, spec, run / 'WORKER_RESULT.json', PERGROUP_O_WORKER))
    require_pergroup_o_scope(prior, public, original, worker)
    for stem, pair in public['original_context_pairs'].items():
        require(retained_read(s, spec, run / (stem + '_BEFORE.json'), pair['before']) ==
                retained_read(s, spec, run / (stem + '_AFTER.json'), pair['after']),
                'PerGroup@O original context/Git differs')
    binding = original['acceptance_bindings'][module]
    expected = binding['all_observed_target_artifacts']
    require(set(expected) == set(artifact_paths(module)) and
            all(value is None or valid_fingerprint(value) for value in expected.values()) and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'PerGroup@O live source/full21 artifacts differ from original accepted binding')
    # Only this temporary manifest view exposes PerGroup to the original generic
    # historical_group/retained_owner readers. All state maps and active are shared.
    shadow = SimpleNamespace(**spec.__dict__)
    shadow.manifest = {{**spec.manifest,
        'accepted_suppliers': {{**spec.manifest['accepted_suppliers'], module: {{
            'group': prior['group'], 'source_commit': prior['source_commit'],
            'source_sha256': prior['source_sha256']}}}},
        'accepted_supplier_groups': {{**spec.manifest['accepted_supplier_groups'], prior['group']: fixed}}}}
    owner = retained_owner(s, shadow, module, validate_live=True)
    evidence, published_owner = spec.supplier_evidence[module], public['owners'][module]
    require(evidence['source_commit'] == prior['source_commit'] and
            evidence['selected_supplier_live_closure_count'] == 69 and
            evidence['original_group_worker_exit_code'] == 1 and
            evidence['owned_count'] == published_owner['owned_count'] and
            evidence['public_count'] == published_owner['public_count'] and
            Path(evidence['audit_plan']['path']).parent.name == published_owner['audit_id'] and
            module_artifacts(s, module) == expected and
            s.d.snapshot(PROJECT, module) == binding['source_plus_five_outputs'],
            'PerGroup@O full audit/count/source/full21 post-validation differs')
    spec.dependency_pins[module] = expected
    return owner


'''


def main():
    runner_raw = frozen(BASE / REL / 'run_selected.py', 87907,
        '9e673a755108d8cf58f02db2165654a1df97e701b0137275078e33da2136f5d9')
    manifest_raw = frozen(BASE / REL / 'SOURCE_MANIFEST.json', 339019,
        '0801ba4e04eacfa8c8d9f99ec657898035d1af3153bcc4023de54bb20833ed2f')
    public_raw = frozen(HERE.parent / 'PERGROUP_O_PUBLIC_ACCEPTANCE.json', 6477,
        '3d69364fab09231361e4f551c2318147966c092ba2e56f3c8292675d6fb196c6')
    repair_raw = frozen(HERE.parent / 'REPAIR_CANDIDATE.json', 2891,
        'dce78b863f0be44745b4f7e24a42973a189ed91df98b769aa3edcfa07c97ad9d')
    source = frozen(HERE.parent / 'Part3AllKLambdaChartCorrection.lean', 11416,
        '9d739aab99a7873daaf25f649cca910d11f02a08ae22a32a70f517734df67962')
    manifest, public, repair = map(json.loads, (manifest_raw, public_raw, repair_raw))
    assert public['source_commit'] == O and public['source_anchor_commit'] == N
    owner = public['owners'][PG]
    prior = {
        'group': 'pergroup_o', 'source_commit': O, 'source_sha256': owner['source_sha256'],
        'live_source_closure_count': 69,
        'historical_group': {
            'source_commit': O, 'compiler_job': public['compiler_job'],
            'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
            'run': public['original_run'], 'owners': [PG], 'driver': public['driver'],
            'source_graph': public['source_manifest'], 'published_source_count': 360,
            'public_evidence': {'commit': P, 'path': PUBLIC_PATH, **fingerprint(public_raw)},
            'evidence_kind': 'bounded_public_acceptance'},
        'owned_count': owner['owned_count'], 'public_count': owner['public_count'], 'audit_id': owner['audit_id']}
    before = deepcopy(manifest)
    manifest['source_anchor_commit'] = P
    row = manifest['project_sources'][ALLK]
    assert {key: row[key] for key in ('bytes', 'sha256', 'git_blob')} == repair['before']
    assert re.findall(r'^import\s+([^\n]+)$', source.decode(), re.M) == row['all_imports']
    row.update(repair['after'])
    origin = manifest['target_source_origins'][ALLK]
    origin['canonical_source'] = {'commit': P, 'path': row['path'], **fingerprint(source)}
    origin['source_reviews'].append({'commit': P, 'path': REPAIR_PATH, **fingerprint(repair_raw)})
    manifest['previously_accepted_targets'][PG] = prior
    guide = manifest['selection_guidance']
    guide['minimum_first_targets'] = [ALLK]
    guide['minimum_first_source_count'] = 73
    guide['minimum_first_dependency_count'] = 72
    guide['previously_accepted_not_compile_targets'].append(PG)
    remaining = [module for module in guide['subsequent_14_targets'] if module != PG]
    guide['remaining_project_graph_unblocked_compile_candidates'] = remaining
    guide['subsequent_13_targets'] = remaining
    guide['subsequent_13_source_count'] = 157
    guide['subsequent_13_dependency_count'] = 144
    guide['previous_target_live_reuse_condition'] = (
        'Only historical targets in the actual selected closure: AllK root73 revalidates '
        'PerGroup@O69, Licensed@M68 and HB@F67, without Support or Cutoff. '
        'Remaining13 closure157 separately reuses Support@B109, HB@F67, Cutoff@K68, '
        'Licensed@M68 and PerGroup@O69 under their original accepted source commits; '
        'none is a compilation target. The original O fourteen-target group remains partial failure. '
        'Prior subsequent_14/subsequent_15 lists are historical and are rejected by selection.')
    data = (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode()
    constants = {
        'PERGROUP_O_MODULE': PG, 'PERGROUP_O_FAILED_MODULE': ALLK,
        'PERGROUP_O_SOURCE_ANCHOR': N, 'PERGROUP_O_RESULT': public['original_result'],
        'PERGROUP_O_WORKER': public['original_worker_result'],
        'PERGROUP_O_ORIGINAL_TARGETS': public['original_targets'],
        'PERGROUP_O_PREVIOUSLY_ACCEPTED_TARGET': prior}
    declaration = '\n'.join(name + ' = ' + pprint.pformat(value, width=106, sort_dicts=False)
                            for name, value in constants.items())
    text = runner_raw.decode()
    text = replace_once(text, 'N-anchored 21-root', 'P-anchored 21-root')
    text = replace_once(text, 'Support@B, HB@F, Cutoff@K and Licensed@M',
                             'Support@B, HB@F, Cutoff@K, Licensed@M and PerGroup@O')
    text = replace_once(text, "SOURCE_ANCHOR = '" + N + "'", "SOURCE_ANCHOR = '" + P + "'")
    text = replace_once(text, "MANIFEST_SHA = '" + fingerprint(manifest_raw)['sha256'] + "'",
                             "MANIFEST_SHA = '" + fingerprint(data)['sha256'] + "'")
    text = replace_once(text, 'def require(ok, message):',
                             ADAPTER.format(constants=declaration).lstrip() + 'def require(ok, message):')
    text = replace_once(text,
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE, LICENSED_M_MODULE},",
        "set(previous) == {'ImbalancedChen.P1OriginalSingletonSupportData', HB_F_MODULE, CUTOFF_K_MODULE, LICENSED_M_MODULE, PERGROUP_O_MODULE},")
    text = replace_once(text, "    for module, prior in previous.items():\n",
        "    for module, prior in previous.items():\n"
        "        if module == PERGROUP_O_MODULE:\n"
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'PerGroup@O previous target classification differs')\n"
        "            pergroup_o_source_binding(s, graph, sources, prior)\n"
        "            continue\n")
    text = replace_once(text,
        "        if module == HB_F_MODULE:\n            retained_hb_f_target(s, spec, module)",
        "        if module == PERGROUP_O_MODULE:\n            retained_pergroup_o_target(s, spec, module)\n"
        "        elif module == HB_F_MODULE:\n            retained_hb_f_target(s, spec, module)")
    ast.parse(text)
    assert [m for m in before['project_sources'] if before['project_sources'][m] != manifest['project_sources'][m]] == [ALLK]
    (HERE / 'SOURCE_MANIFEST.json').write_bytes(data)
    (HERE / 'run_selected.py').write_text(text)
    print(json.dumps({'source_anchor_commit': P, 'runner': fingerprint(text.encode()),
                      'source_manifest': fingerprint(data), 'published_or_executed': False}, indent=2))


if __name__ == '__main__':
    main()
