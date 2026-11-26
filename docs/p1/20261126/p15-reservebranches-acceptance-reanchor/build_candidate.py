#!/usr/bin/env python3
"""Retain LowerTrim@AE and AtlasTrim@AE using the fixed U dual-owner mechanism.

AF must be the actual reviewed Reserve source publication. Until it is bound,
this builder stops before generating a runner or manifest. No cloud/Git work.
"""
from pathlib import Path
import argparse
import ast
import copy
import hashlib
import json
import pprint
import re
import sys

sys.dont_write_bytecode = True
AE = 'ca13f51c65d37870b96a6b1eb32ac30e92019fa2'
AD = 'e91af3a5c407bdeea243af7dd3c4248949d83e9b'
AF = 'b06429e9c2d8fbd5c654105d5f4e44f26c0865f4'
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
ATLASTRIM = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
RESERVE = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
ROUGH = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
DRIVER = 'docs/p1/20261126/p15-current-corrections/run_selected.py'
MANIFEST = 'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json'
PUBLIC_ROOT = 'docs/p1/20261125/p15-current-public-acceptance/'
AE_DRIVER = {'bytes': 306454, 'sha256': '2fac63da6dd93b54ded3a8c5c8542558f3a03a738092fcb43b2336ab8674705e'}
AE_MANIFEST = {'bytes': 364863, 'sha256': '6c5c0b8795a2c6fa1265e5030b12a9e77500efe651b8796b11b748a0ed47ada5'}
AE_METADATA = {'bytes': 13520, 'sha256': '6145eb2f0ebb8e1d6d3d0968e711d93478705bf01f44c08906eaa9ea74955fed'}
AE_READ = {'bytes': 45763, 'sha256': 'b630616bbcfe7e1b073ff0046efa7c606f4319ca66442286db7a7898d611075f'}
AE_PUBLICS = {
    LOWERTRIM: {'name': 'LOWERTRIM_AE_PUBLIC_ACCEPTANCE', 'bytes': 11615,
                'sha256': 'fac4e9665c918179f4f72fae8fc009a5ccb912f4674bc8d56dbf256906470681'},
    ATLASTRIM: {'name': 'ATLASTRIM_AE_PUBLIC_ACCEPTANCE', 'bytes': 7359,
                'sha256': '18201db1ec50df50b023d894abaae0f4675650f4c3a9e8efe619b344c9ada325'},
}
OWNER_SPECS = {
    LOWERTRIM: {'group': 'lowertrim_ae', 'run_index': 0, 'own_closure': 119,
                'owned': 10, 'public': 10, 'audit_id': 'e45153f0bb3e3268967a',
                'compiler_job': 'job_d3c60cd1867242fab3195258062e2290'},
    ATLASTRIM: {'group': 'atlastrim_ae', 'run_index': 1, 'own_closure': 153,
               'owned': 11, 'public': 9, 'audit_id': '25adbe91b10ca6f615bb',
               'compiler_job': 'job_698d39e25f9d4800a912dc27a0bfe84b'},
}
RESERVE_BEFORE = {'bytes': 8183, 'sha256': '8b8987b5208aa0ed201adeb84a03076119519ff2880fb442175de2385b3ad049'}
RESERVE_AFTER = {'bytes': 8197, 'sha256': 'd5945aa39ab54bc5c4aeb529a96299e7ab3bcf0c4fcb946296d3a697753a2bb7'}
RESERVE_REPAIR = {'bytes': 1521, 'sha256': 'f8cce20ff07f3665469c8d7feac2c9c47b8cf60f796eb25a842f5cc67701e37c'}
RESERVE_PROBE_JOB = 'job_27c97559f895492480be94780caf0551'
REPAIR_PATH = 'docs/p1/20261126/p15-reservebranches-first-compile-repair/REPAIR_CANDIDATE.json'


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(value):
    return {k: value[k] for k in ('bytes', 'sha256')}


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def functions(text):
    return {n.name: ast.get_source_segment(text, n) for n in ast.parse(text).body
            if isinstance(n, ast.FunctionDef)}


def replace_once(text, before, after):
    need(text.count(before) == 1, 'nonunique builder splice: ' + before[:100])
    return text.replace(before, after)


def closure(graph, modules):
    seen, pending = set(), list(modules)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module)
            pending.extend(graph[module])
    return seen


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-anchor', required=True)
    parser.add_argument('--actual-directory', type=Path, default=Path('/tmp/p15-ae-actual'))
    parser.add_argument('--repair-source', type=Path, required=True)
    parser.add_argument('--repair-candidate', type=Path, required=True)
    parser.add_argument('--repair-review-path', required=True)
    parser.add_argument('--output', type=Path, default=Path('/tmp/p15-entrypoint-ag'))
    args = parser.parse_args()
    need(AF is not None, 'HOLD: actual AF publication has not been bound')
    need(__debug__ and args.source_anchor == AF, 'exact published AF source anchor required')
    need(args.output.resolve() == Path('/tmp/p15-entrypoint-ag'), 'separate /tmp/p15-entrypoint-ag output required')
    need(args.repair_review_path == REPAIR_PATH, 'exact Reserve repair review path required')
    old = Path('/tmp/p15-entrypoint-ae/run_selected.py').read_bytes()
    manifest_raw = Path('/tmp/p15-entrypoint-ae/SOURCE_MANIFEST.json').read_bytes()
    need(fp(old) == AE_DRIVER and fp(manifest_raw) == AE_MANIFEST, 'frozen AE baseline differs')
    manifest = json.loads(manifest_raw)
    before_manifest = copy.deepcopy(manifest)
    graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
    metadata_raw = (args.actual_directory / 'ACTUAL_AE_METADATA.json').read_bytes()
    read_raw = (args.actual_directory / 'ACTUAL_AE_ACCEPTANCE_READ.json').read_bytes()
    need(fp(metadata_raw) == AE_METADATA and fp(read_raw) == AE_READ, 'actual AE metadata/collector pins differ')
    metadata, read = json.loads(metadata_raw), json.loads(read_raw)
    need(metadata['source_commit'] == read['source_commit'] == AE and
         read['source_anchor_commit'] == AD and read['selected_owners_revalidated'] == [LOWERTRIM, ATLASTRIM] and
         read['current_read_live_source_count'] == 153 and read['current_read_preserved_dependency_count'] == 151 and
         len(read['historical_owners_revalidated_in_current_read_scope']) == 25 and
         read['normal_or_kernel_commands_executed'] == 0 and read['new_lean_acceptance'] is False and
         read['source_runtime_artifacts_and_original_receipts_unchanged'] is True,
         'actual AE collector identity/joint scope differs')
    actual = []
    for index in (0, 1):
        raw = (args.actual_directory / ('attempt-%05d-RESULT.json' % index)).read_bytes()
        result = json.loads(raw)
        worker = {k: v for k, v in result.items()
                  if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
        wr = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
        bindings = metadata['runs']['attempt-%05d' % index]
        need(fp(raw) == pin(bindings['RESULT.json']) and fp(wr) == pin(bindings['WORKER_RESULT.json']),
             'actual AE RESULT/WORKER pins differ')
        actual.append(result)
    first, later = actual
    need(first['targets'] == first['accepted_owners'] == [LOWERTRIM] and first['failures'] == {} and
         first['worker_exit_code'] == 0 and first['all_selected_owners_accepted'] is True and
         first['reused_complete_selected_owners'] == [] and first['selected_live_source_count'] == 119 and
         first['final_stock_readiness']['exit_code'] == 0 and len(first['original_supplier_acceptance_bindings']) == 3 and
         later['targets'] == manifest['selection_guidance']['subsequent_4_targets'] == [LOWERTRIM, ATLASTRIM, RESERVE, ROUGH] and
         later['accepted_owners'] == [LOWERTRIM, ATLASTRIM] and
         later['reused_complete_selected_owners'] == [LOWERTRIM] and
         later['failures'] == {RESERVE: 'normal failed/scope differs: ' + RESERVE} and
         later['worker_exit_code'] == 1 and later['all_selected_owners_accepted'] is False and
         later['dispatch_error'] == 'serialized worker exited 1' and 'final_stock_readiness' not in later and
         later['selected_live_source_count'] == 157 and len(later['original_supplier_acceptance_bindings']) == 27 and
         later['acceptance_bindings'][LOWERTRIM] == first['acceptance_bindings'][LOWERTRIM],
         'original AE successful/partial run identities differ')
    priors, scopes, publics = {}, {}, {}
    for module, owner_spec in OWNER_SPECS.items():
        fixed_public = AE_PUBLICS[module]
        public_raw = (args.actual_directory / (fixed_public['name'] + '.json')).read_bytes()
        need(fp(public_raw) == pin(fixed_public), 'actual AE public pin differs: ' + module)
        public = json.loads(public_raw)
        index = owner_spec['run_index']
        original = actual[index]
        owner = public['owners'][module]
        run = 'runs/attempt-%05d' % index
        need(public == read['public_summaries'][fixed_public['name']] and
             public['schema'] == 'p15_AE_original_accepted_owner_public_acceptance_v1' and
             public['status'] == 'ORIGINAL_AE_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION' and
             public['source_commit'] == AE and public['source_anchor_commit'] == AD and
             public['compiler_job'] == owner_spec['compiler_job'] and public['original_run'] == run and
             public['selected_owners_revalidated'] == [LOWERTRIM, ATLASTRIM] and
             public['current_read_live_source_count'] == 153 and public['current_read_preserved_dependency_count'] == 151 and
             set(public['owners']) == {module} and
             public['driver'] == {'commit': AE, 'path': DRIVER, **AE_DRIVER} and
             public['source_manifest'] == {'commit': AE, 'path': MANIFEST, **AE_MANIFEST} and
             (owner['owned_count'], owner['public_count'], owner['audit_id']) ==
                 (owner_spec['owned'], owner_spec['public'], owner_spec['audit_id']) and
             owner['owner_live_source_closure_count'] == len(closure(graph, [module])) == owner_spec['own_closure'] and
             owner['source_sha256'] == manifest['project_sources'][module]['sha256'] and
             public['normal_or_kernel_commands_executed'] == 0 and public['new_lean_acceptance'] is False and
             public['whole_P1_5_complete'] is False,
             'actual AE public/own source/count/run/joint scope differs: ' + module)
        recorded = metadata['accepted_owners'][module]
        need((recorded['owned_count'], recorded['public_count'], recorded['first_accepting_run_index']) ==
             (owner_spec['owned'], owner_spec['public'], index) and
             recorded['normal'] == original['acceptance_bindings'][module]['normal_receipt'] and
             recorded['audit_plan'] == original['acceptance_bindings'][module]['audits'][0]['plan'] and
             recorded['audit_result'] == original['acceptance_bindings'][module]['audits'][0]['result'] and
             owner['source'] == recorded['source'], 'AE original owner/metadata identity differs: ' + module)
        run_pins = metadata['runs']['attempt-%05d' % index]
        need(public['original_result'] == pin(run_pins['RESULT.json']) and
             public['original_worker_result'] == pin(run_pins['WORKER_RESULT.json']) and
             all(pair[phase.lower()] == pin(run_pins[stem + '_' + phase + '.json'])
                 for stem, pair in public['original_context_pairs'].items() for phase in ('BEFORE', 'AFTER')),
             'AE original run/context public pins differ: ' + module)
        group = {'source_commit': AE, 'compiler_job': owner_spec['compiler_job'],
                 'evidence_root': '/workspace/p1-complete-proof/20261126-p15-current-corrections-v1',
                 'run': run, 'owners': [module], 'driver': public['driver'],
                 'source_graph': public['source_manifest'], 'published_source_count': 360,
                 'public_evidence': {'commit': AF, 'path': PUBLIC_ROOT + fixed_public['name'] + '.json', **fp(public_raw)},
                 'evidence_kind': 'bounded_public_acceptance'}
        priors[module] = {'group': owner_spec['group'], 'source_commit': AE,
                          'source_sha256': owner['source_sha256'], 'live_source_closure_count': owner_spec['own_closure'],
                          'historical_group': group, 'owned_count': owner_spec['owned'],
                          'public_count': owner_spec['public'], 'audit_id': owner_spec['audit_id']}
        scopes[module] = {'targets': original['targets'], 'accepted': original['accepted_owners'],
                          'reused': original['reused_complete_selected_owners'], 'failed': list(original['failures']),
                          'not_accepted': [x for x in original['targets'] if x not in original['accepted_owners']],
                          'not_started': [x for x in original['targets'] if x not in original['accepted_owners'] and x not in original['failures']],
                          'readiness': list(original['direct_import_readiness']), 'exit_code': original['worker_exit_code'],
                          'live_count': original['selected_live_source_count'], 'result': public['original_result'],
                          'worker': public['original_worker_result'], 'requested_targets': public['original_requested_targets'],
                          'context_pairs': public['original_context_pairs'], 'receipt_bindings': owner['receipt_bindings'],
                          'source': owner['source'], 'failure_messages': original['failures']}
        publics[module] = public
    reuse = publics[LOWERTRIM]['later_same_source_reuse']
    need(reuse == read['original_runs'][1] and publics[ATLASTRIM]['later_same_source_reuse'] is None and
         reuse['accepted_owners'] == [LOWERTRIM, ATLASTRIM] and reuse['reused_complete_selected_owners'] == [LOWERTRIM] and
         reuse['failed_modules'] == [RESERVE] and reuse['not_started_modules'] == [ROUGH] and
         reuse['original_final_stock_readiness']['recorded'] is False and
         all(pin(reuse['evidence_bindings'][key]) == pin(value)
             for key, value in metadata['runs']['attempt-00001'].items()) and
         pin(reuse['evidence_bindings']['executed-driver.py']) == AE_DRIVER,
         'original AE later partial/reuse public evidence differs')
    repair_raw, source_raw = args.repair_candidate.read_bytes(), args.repair_source.read_bytes()
    repair = json.loads(repair_raw)
    row = manifest['project_sources'][RESERVE]
    before = (Path('/workspace/scratch/76f3bdb16a38/goldbach-p15') / row['path']).read_bytes()
    need(fp(repair_raw) == RESERVE_REPAIR and
         repair['schema'] == 'p15_original_prime_atlas_reserve_branches_one_proof_splice_candidate_v1' and
         repair['source_base_commit'] == AE and repair['source'] == row['path'] and
         repair['before'] == pin(row) == fp(before) == RESERVE_BEFORE and
         repair['after'] == fp(source_raw) == RESERVE_AFTER and len(repair['splices']) == 1 and
         repair['declaration_count'] == 11 and repair['imports_unchanged'] is True and
         repair['declaration_headers_unchanged'] is True and repair['axioms_or_sorry_added'] is False and
         repair['compiler_probe_performed'] is True and repair['actual_whole_module_probe']['exit_code'] == 0 and
         repair['actual_whole_module_probe']['compiler_job'] == RESERVE_PROBE_JOB and
         repair['new_lean_acceptance'] is False and repair['whole_P1_5_complete'] is False,
         'reviewed Reserve proof repair/probe identity differs')
    pieces, end = [], 0
    for splice in repair['splices']:
        start, stop = splice['start'], splice['end']
        need(end <= start < stop <= len(before) and before[start:stop] == splice['before'].encode(),
             'Reserve splice preimage differs')
        pieces.extend((before[end:start], splice['after'].encode())); end = stop
    need(b''.join(pieces) + before[end:] == source_raw and
         re.findall(r'^import\s+(\S+)\s*$', source_raw.decode(), re.M) == row['all_imports'],
         'Reserve bytes outside reviewed splice or imports changed')
    code, old_functions = old.decode(), functions(old.decode())
    adapter = '\n\n\n'.join(old_functions[name] for name in
        ('u_prior_source_binding', 'require_u_prior_scope', 'retained_u_prior_target'))
    replacements = [
        ('u_prior_source_binding', 'ae_prior_source_binding'),
        ('require_u_prior_scope', 'require_ae_prior_scope'),
        ('retained_u_prior_target', 'retained_ae_prior_target'),
        ('U_WORD_MODULE', 'AE_LOWERTRIM_MODULE'), ('U_ALLGROUP_MODULE', 'AE_ATLASTRIM_MODULE'),
        ('p15_U_original_accepted_owner_public_acceptance_v1', 'p15_AE_original_accepted_owner_public_acceptance_v1'),
        ('ORIGINAL_U_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION', 'ORIGINAL_AE_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION'),
        ('later_same_U_reuse_run', 'later_same_AE_reuse_run'), ('U_', 'AE_'),
        ("'current_read_live_source_count': 139, 'current_read_preserved_dependency_count': 137",
         "'current_read_live_source_count': 153, 'current_read_preserved_dependency_count': 151"),
        ('Word', 'LowerTrim'), ('later10', 'later4'),
    ]
    for old_fragment, new_fragment in replacements:
        need(old_fragment in adapter, 'missing U adapter fragment: ' + old_fragment)
        adapter = adapter.replace(old_fragment, new_fragment)
    adapter = re.sub(r'\bU\b', 'AE', adapter)
    need(adapter + '\n' == Path(__file__).with_name('ae_prior_adapter.py.in').read_text(),
         'reviewed AE dual-owner three-function template differs')
    constants = {'AE_LOWERTRIM_MODULE': LOWERTRIM, 'AE_ATLASTRIM_MODULE': ATLASTRIM,
                 'AE_PRIOR_SOURCE_ANCHOR': AD, 'AE_PREVIOUSLY_ACCEPTED_TARGETS': priors,
                 'AE_PRIOR_RUNS': scopes, 'AE_PRIOR_LATER_REUSE': reuse}
    inserted = '\n\n# Fixed LowerTrim@AE run0 and AtlasTrim@AE partial run1 acceptance.\n'
    inserted += '\n'.join(key + ' = ' + pprint.pformat(value, width=110, sort_dicts=False)
                          for key, value in constants.items())
    inserted += '\nPREVIOUSLY_ACCEPTED_TARGETS = {**PREVIOUSLY_ACCEPTED_TARGETS, **AE_PREVIOUSLY_ACCEPTED_TARGETS}\n\n\n'
    inserted += adapter + '\n\n\n'
    code = replace_once(code, 'def require(ok, message):', inserted + 'def require(ok, message):')
    code = replace_once(code, ' | set(SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS),\n',
                        ' | set(SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS) | set(AE_PREVIOUSLY_ACCEPTED_TARGETS),\n')
    code = replace_once(code,
        '    for module, prior in previous.items():\n        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:',
        '    for module, prior in previous.items():\n'
        '        if module in AE_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
        "                    'AE dual-owner prior classification differs: ' + module)\n"
        '            ae_prior_source_binding(s, graph, sources, module, prior)\n'
        '            continue\n'
        '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code,
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:',
        "    for module in sorted(active & set(manifest['previously_accepted_targets'])):\n"
        '        if module in AE_PREVIOUSLY_ACCEPTED_TARGETS:\n'
        '            retained_ae_prior_target(s, spec, module)\n'
        '        elif module in SYNTHESIS_AC_PREVIOUSLY_ACCEPTED_TARGETS:')
    code = replace_once(code, "\nSOURCE_ANCHOR = '" + AD + "'", "\nSOURCE_ANCHOR = '" + AF + "'")
    code = replace_once(code, 'AD-anchored 21-root', 'AF-anchored 21-root')
    code = replace_once(code, 'Mean@AA and Synthesis@AC\n',
                        'Mean@AA, Synthesis@AC, LowerTrim@AE and AtlasTrim@AE\n')
    manifest['source_anchor_commit'] = AF
    row.update(**fp(source_raw), git_blob=hashlib.sha1(
        b'blob ' + str(len(source_raw)).encode() + b'\0' + source_raw).hexdigest())
    origin = manifest['target_source_origins'][RESERVE]
    origin['canonical_source'] = {'commit': AF, 'path': row['path'], **fp(source_raw)}
    origin['source_reviews'].append({'commit': AF, 'path': REPAIR_PATH, **fp(repair_raw)})
    manifest['previously_accepted_targets'].update(priors)
    guide = manifest['selection_guidance']
    guide.update(minimum_first_targets=[RESERVE], minimum_first_source_count=140,
                 minimum_first_dependency_count=139, minimum_first_artifact_watch_module_count=152,
                 minimum_first_historical_supplier_count=21)
    guide['previously_accepted_not_compile_targets'].extend([LOWERTRIM, ATLASTRIM])
    for module in (LOWERTRIM, ATLASTRIM):
        guide['remaining_project_graph_unblocked_compile_candidates'].remove(module)
    remaining = [module for module in guide['subsequent_4_targets'] if module not in priors]
    guide.update(subsequent_2_targets=remaining, subsequent_2_source_count=144,
                 subsequent_2_dependency_count=142, subsequent_2_artifact_watch_module_count=152,
                 subsequent_2_historical_supplier_count=24)
    active, first_active = closure(graph, remaining), closure(graph, [RESERVE])
    historical = set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers'])
    need(remaining == [RESERVE, ROUGH] and len(first_active) == 140 and
         len(first_active - {RESERVE}) == 139 and len(first_active | set(manifest['targets'])) == 152 and
         len(first_active & historical) == 21 and not (first_active & set(priors)) and
         len(active) == 144 and len(active - set(remaining)) == 142 and
         len(active | set(manifest['targets'])) == 152 and len(active & historical) == 24 and not (active & set(priors)) and
         len(closure(graph, [LOWERTRIM, ATLASTRIM])) == 153 and
         len(manifest['previously_accepted_targets']) == 16 and len(manifest['project_sources']) == 360 and
         len(manifest['fixed_dependencies']) == 303 and len(manifest['unaccepted_p3_dependencies']) == 19,
         'AG actual selected source/dependency/historical scope differs')
    guide['previous_target_live_reuse_condition'] = (
        'Only prior targets in the actual selected closure receive live owner/audit validation. Reserve first140/139 '
        'has 21 historical suppliers; later2 closure144/142 has 24. Both watch152 and neither reaches LowerTrim or '
        'AtlasTrim, so these two new historical priors are not given extra live audits outside the actual selected scope. '
        'The actual AE collector jointly revalidated153/151; own closures119 and153 remain distinct. LowerTrim keeps '
        'AE attempt-00000 successful acceptance and final stock; AtlasTrim keeps AE attempt-00001 partial acceptance, '
        'with LowerTrim reused, Reserve failed, RoughPrime unstarted and no final stock. Original run scopes119 and157 '
        'and supplier counts3 and27 stay fixed. Fourteen previous priors are unchanged. Old subsequent4/5/6/7/8/10/11/13/14/15 '
        'guidance remains historical. No prior is selected or rebound. The source installer is separate.')
    need({m: r for m, r in manifest['project_sources'].items() if m != RESERVE} ==
         {m: r for m, r in before_manifest['project_sources'].items() if m != RESERVE} and
         all(manifest['project_sources'][m][key] == r[key] for m, r in before_manifest['project_sources'].items()
             for key in ('imports', 'all_imports')), 'unrelated source/import change')
    need({m: r for m, r in manifest['target_source_origins'].items() if m != RESERVE} ==
         {m: r for m, r in before_manifest['target_source_origins'].items() if m != RESERVE}, 'unrelated source origin changed')
    need({m: r for m, r in manifest['previously_accepted_targets'].items() if m not in priors} ==
         before_manifest['previously_accepted_targets'], 'fourteen prior identities changed')
    for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
        need(manifest[key] == before_manifest[key], 'old policy changed: ' + key)
    mr = (json.dumps(manifest, indent=2, ensure_ascii=False) + '\n').encode()
    code = replace_once(code, "MANIFEST_SHA = '" + AE_MANIFEST['sha256'] + "'",
                        "MANIFEST_SHA = '" + fp(mr)['sha256'] + "'")
    new_functions = functions(code)
    changed = {name for name in old_functions if old_functions[name] != new_functions[name]}
    added = set(new_functions) - set(old_functions)
    need(len(old_functions) == 64 and len(new_functions) == 67 and
         changed == {'source_manifest', 'preflight'} and
         added == {'ae_prior_source_binding', 'require_ae_prior_scope', 'retained_ae_prior_target'},
         'unexpected existing/new function changes')
    args.output.mkdir(parents=True, exist_ok=True)
    for name, raw in {'run_selected.py': code.encode(), 'SOURCE_MANIFEST.json': mr,
                      'ae_prior_adapter.py': inserted.encode()}.items():
        (args.output / name).write_bytes(raw)
    report = {'schema': 'p15_AF_source_dual_AE_prior_generation_v1', 'source_anchor': AF,
              'runner': fp(code.encode()), 'manifest': fp(mr), 'adapter': fp(inserted.encode()),
              'original_AE_function_count': 64, 'unchanged_AE_functions': 62,
              'changed_functions': sorted(changed), 'new_functions': sorted(added),
              'fourteen_prior_identities_unchanged': True, 'other_359_sources_all_imports_303_19_policy_unchanged': True,
              'actual_AE_publics': {module: pin(value) for module, value in AE_PUBLICS.items()},
              'actual_AE_acceptance_read': AE_READ,
              'Reserve_repair': {'source': fp(source_raw), 'review': fp(repair_raw), 'splices': 1},
              'first': {'sources': 140, 'dependencies': 139, 'watch_modules': 152, 'historical_suppliers': 21, 'new_AE_priors_active': []},
              'later2': {'sources': 144, 'dependencies': 142, 'watch_modules': 152, 'historical_suppliers': 24, 'new_AE_priors_active': []},
              'actual_collector_joint_scope': {'sources': 153, 'preserved_dependencies': 151},
              'new_lean_acceptance': False, 'whole_P1_5_complete': False}
    (args.output / 'BUILD_OUTPUT.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
    print(json.dumps(report, sort_keys=True))


if __name__ == '__main__':
    main()
