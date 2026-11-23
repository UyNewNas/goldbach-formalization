#!/usr/bin/env python3
"""Publish existing cache-window receipts only; no builder or cache helper runs."""
from pathlib import Path
import collections
import hashlib
import json

OUT = Path('/workspace/blue-member-cache-window-publication')
AGG = Path('/workspace/blue-member-aggregate-evidence')
T01 = Path('/workspace/artifacts/member-t01-project90-20261123')
DEST = 'docs/verification/20261123-blue-compilation/member-cache-window'
REFERENCES = {}


def digest(path):
    with path.open('rb') as source:
        value = hashlib.file_digest(source, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': value}


def read(path):
    data = path.read_bytes()
    REFERENCES[str(path)] = {'path': str(path), 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
    return json.loads(data)


def save(name, value):
    path = OUT / name
    path.write_text(json.dumps(value, indent=2) + '\n')
    return path


def compact(path, omit):
    data = read(path)
    return data, {k: v for k, v in data.items() if k not in omit}


def canonical_sha(data):
    return hashlib.sha256(json.dumps(data, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def main():
    OUT.mkdir(exist_ok=True)
    final = read(AGG / 'CACHE_REUSE_FINAL.json')
    t01 = read(T01 / 'PUBLISHABLE_SUMMARY.json')
    stop = read(AGG / 'checkpoint-v1/OWNER_STOP_RECEIPT.json')
    stopped = read(AGG / 'OLD_CONTROLLER_COMPLETED.json')
    assert stopped == stop and stop['old_exec_final_exit_code'] == stop['root_observed_session_exit'] == 241
    assert stop['successful_selected_module_groups_preserved'] == 1242
    assert not stop['running_source_Lean_signaled'] and not stop['Prototype_tree_signaled']
    assert digest(AGG / 'old-root-tent-build.log')['sha256'] == stop['old_log_sha256']
    snapshot = read(AGG / 'checkpoint-v1/COMPLETED_MODULES_BEFORE_TERMINATION.json')
    assert snapshot['completed_selected_modules'] == len(snapshot['source_plus_five_outputs']) == 1242
    assert not snapshot['missing_last_success_olean_or_trace']
    assert all(len(v) == 6 for v in snapshot['source_plus_five_outputs'].values())
    save('CHECKPOINT_COMPACT.json', {
        'schema': 'member_cache_checkpoint_record_extraction_v1',
        'original_record': REFERENCES[str(AGG / 'checkpoint-v1/COMPLETED_MODULES_BEFORE_TERMINATION.json')],
        'original_stop_receipt': REFERENCES[str(AGG / 'checkpoint-v1/OWNER_STOP_RECEIPT.json')],
        'selected_successful_module_groups': 1242, 'facets_per_saved_group_including_source': 6,
        'reported_built_modules': len(snapshot['reported_Built_modules']),
        'no_missing_last_success_olean_or_trace': True,
        'original_stop_verified_source_and_five_output_hashes_unchanged': stop['source_plus_five_output_hashes_unchanged_after_stop'],
        'operator_exit': 241, 'exit_is_new_proof_failure': False,
        'known_earlier_source_failures_retained_in_original_log': stop['prior_module_failures_in_log'],
        'scope': 'Record extraction only. 1242 preservation was verified immediately across the authorized stop; this is not a claim that every working trace remained unchanged through later authorized cache adoption.'})

    copy = read(T01 / 'install-v1/COPY_COMPLETE.json')
    stock = read(T01 / 'install-v1/STOCK_RESULT.json')
    assert copy['copied_group_count'] == len(copy['accepted_groups']) == 8 and copy['copied_facet_count'] == 64
    assert len(copy['skipped_during_use']) == 18 and len(copy['blocked_by_original_qualification']) == 64
    assert stock['exit_code'] == 0 and stock['stock_pass_with_zero_Member_source_calls']
    assert stock['original_source_and_restored_artifacts_unchanged_after_stock']
    for key in ['copy_receipt', 'copy_journal']:
        row = t01['actual_copy'][key]
        assert digest(Path(row['path']))['sha256'] == row['sha256']
    for row in t01['helpers'].values():
        if isinstance(row, dict):
            assert digest(Path(row['path']))['sha256'] == row['executed_sha256']

    proto, proto_small = compact(AGG / 'prototype-qualified/INSTALL_RECEIPT.json', {'window_input_rechecks'})
    assert len(proto['installed_files']) == 72 and len(proto['copy_eligible_at_window']) == 9
    assert len(proto['already_existing_modules_not_overwritten']) == 23
    assert proto['no_clobber'] and not proto['source_files_modified'] and not proto['native_executables_installed']
    assert proto['stock']['exit_code'] == 3 and proto['stock']['Member_source_compiler_calls'] == 0
    proto_small.update(original_record=REFERENCES[str(AGG / 'prototype-qualified/INSTALL_RECEIPT.json')],
                       compact_extraction_only=True,
                       window_input_recheck_records_omitted=len(proto['window_input_rechecks']),
                       window_input_rechecks_canonical_sha256=canonical_sha(proto['window_input_rechecks']))
    save('PROTOTYPE_INSTALL_COMPACT.json', proto_small)

    native, native_small = compact(AGG / 'P6_SINGLE_NATIVE_INSTALL_RECEIPT.json', {'actual_import_rechecks'})
    assert native['import_facet_rechecks'] == len(native['actual_import_rechecks']) == 16622
    assert not native['blocked_imports'] and all(x['same_actual_object_bytes_reconfirmed'] for x in native['actual_import_rechecks'])
    assert len(native['installed_files']) == 8 and native['destination_stock']['exit_code'] == 0
    assert native['destination_stock']['source_compiler_calls_for_target'] == 0
    native_small.update(original_record=REFERENCES[str(AGG / 'P6_SINGLE_NATIVE_INSTALL_RECEIPT.json')],
                        compact_extraction_only=True,
                        actual_import_rechecks_omitted=len(native['actual_import_rechecks']),
                        actual_import_rechecks_canonical_sha256=canonical_sha(native['actual_import_rechecks']))
    save('P6_NATIVE_INSTALL_COMPACT.json', native_small)

    adoption = read(AGG / 'prototype-qualified/trace-adoption-v1/stage1-ADOPTION.json')
    final_trace = read(AGG / 'prototype-qualified/trace-adoption-v1/FINAL_RESULT.json')
    assert final_trace['status'] == 'PASS_AUTHENTIC_TRACE_ADOPTION_AND_STOCK_NO_MEMBER_SOURCE_CALLS'
    assert len(final_trace['stages']) == 1 and final_trace['stages'][0]['exit_code'] == 0
    assert final_trace['stages'][0]['Member_source_or_native_compiler_event_count'] == 0
    assert len(adoption['groups']) == 2
    trace_small = {k: v for k, v in adoption.items() if k != 'groups'}
    trace_small.update(original_record=REFERENCES[str(AGG / 'prototype-qualified/trace-adoption-v1/stage1-ADOPTION.json')],
                       compact_extraction_only=True, groups=[])
    completed_c = []
    for group in adoption['groups']:
        assert group['module'] in ['ImbalancedChen.HalfProductMassFibres', 'ImbalancedChen.ActualSieveGate']
        assert group['adopted_authentic_trace']['raw_bytes_identical']
        assert not group['adopted_authentic_trace']['trace_fields_edited']
        assert not group['adopted_authentic_trace']['synthetic_field_edited']
        assert not group['setup_written'] and not group['source_or_proof_written']
        assert digest(Path(group['original_trace']['backup']))['sha256'] == group['original_trace']['sha256']
        inputs = group['current_full_actual_import_parts']
        assert all(x['matched'] and x['producer']['sha256'] == x['consumer']['sha256'] for x in inputs)
        small = {k: v for k, v in group.items() if k != 'current_full_actual_import_parts'}
        small.update(actual_import_parts_omitted=len(inputs), actual_import_parts_canonical_sha256=canonical_sha(inputs),
                     all_recorded_actual_input_byte_pairs_equal=True)
        trace_small['groups'].append(small)
        completed_c.extend(group['missing_C_completion_before_trace_stability_boundary'])
    assert len(completed_c) == 4 and collections.Counter(x['suffix'] for x in completed_c) == {'.c': 2, '.c.hash': 2}
    trace_small['boundary_explanation'] = 'Four missing auxiliary facets (two .c and two .c.hash) were authentically completed first. The recorded nontrace stability boundary begins after that completion; then only two working .trace files were replaced with exact existing producer bytes. Original Member trace bytes were backed up. No trace field or expected hash was synthesized or rebased.'
    trace_small['not_executed_extra_trace_adoptions'] = ['ImbalancedChen.LogCutoffError', 'ImbalancedChen.PowerErrorBudget']
    save('AUTHENTIC_TRACE_AND_C_COMPLETION_COMPACT.json', trace_small)

    assert digest(Path(final['T01_stock_receipt']['path']))['sha256'] == final['T01_stock_receipt']['sha256']
    assert digest(Path(final['Prototype_stock_final']['path']))['sha256'] == final['Prototype_stock_final']['sha256']
    assert REFERENCES[str(AGG / 'P6_SINGLE_NATIVE_INSTALL_RECEIPT.json')]['sha256'] == final['P6_native_stock_receipt']['sha256']
    for record, log in [(proto['stock'], AGG / 'prototype-qualified/member-stock.log'),
                        (native['destination_stock'], AGG / 'member-single-native-stock.log'),
                        (final_trace['stages'][0], AGG / 'prototype-qualified/trace-adoption-v1/stage1-stock.log')]:
        assert digest(log)['sha256'] == record['log_sha256']
    save('STATIC_RECEIPT_CHAIN_REVIEW.json', {
        'schema': 'member_cache_window_publication_static_receipt_chain_review_v1',
        'review_result': 'PASS_RECORDED_COUNTS_HASH_LINKS_AND_SCOPE_BOUNDARIES',
        'reviewer': 'build_workflow',
        'actions_performed': ['Read existing JSON/log/helper bytes', 'Verify selected receipt, log, backup and helper digest links', 'Extract compact views while retaining full original record SHA256'],
        'source_compilers_kernel_checkers_or_builders_run': 0,
        'cache_or_trace_or_source_mutations': 0, 'qualification_replays_or_dependency_payload_rehashes': 0,
        'actual_portable_groups_copied': {'T01_project': 8, 'Prototype_project': 9, 'P6_native': 1},
        'actual_portable_facets_copied': {'T01': 64, 'Prototype': 72, 'P6_native': 8},
        'T01_qualified_before_window': 26, 'T01_qualified_but_became_present_before_copy': 18, 'T01_blocked': 64,
        'Prototype_already_present_native_groups_not_copied': 23,
        'working_trace_byte_replacements': 2, 'separate_missing_C_auxiliary_completions': 4,
        'prototype_initial_stock_exit': 3, 'prototype_final_stock_exit': 0,
        'final_destination_stock_zero_Member_source_calls': True,
        'new_theorem_or_node_credit': 0,
        'limitations': ['This packet is an extraction of completed historical receipts, not a fresh cache qualification or local proof acceptance.',
                        'Bulky import maps and compiled payloads remain local and are referenced by their original file identities.',
                        '1242-success preservation applies across the safe stop; two later authorized working-trace replacements are explicit exceptions.',
                        'Original records saying a new aggregate had not started describe their recorded historical window, not current build progress.']})

    selected = []
    def add(path, relative):
        identity = digest(path)
        selected.append({'source': str(path), 'destination': DEST + '/' + relative,
                         'sha256': identity['sha256'], 'bytes': identity['bytes']})
    aggregate_files = [
        'CACHE_REUSE_FINAL.json', 'COPY_WINDOW_ALL_COMPLETE.json', 'CHECKPOINT_PLAN.json',
        'CHECKPOINT_PLAN_WAITERS_ADAPTATION.json', 'REUSE_WINDOW_OPEN.json', 'STOCK_RELEASED.json',
        'OLD_CONTROLLER_COMPLETED.json', 'old-root-tent-build.log', 'checkpoint-v1-controller.log',
        'checkpoint-v1-operator.log', 'checkpoint-v1/GATE_ACQUIRED.json', 'checkpoint-v1/GATE_RELEASED.json',
        'checkpoint-v1/PROCESS_BEFORE_TERMINATION.json', 'checkpoint-v1/PROCESS_AFTER_TERMINATION.json',
        'checkpoint-v1/WAITING_WRAPPERS_FINAL_BEFORE_STOP.json',
        'PROTOTYPE_35_PRODUCER_STOCK.json', 'prototype-35-producer-stock.log',
        'prototype-qualified/SUMMARY.json', 'prototype-qualified/COPY_COMPLETE.json',
        'prototype-qualified/STOCK_COMPLETE.json', 'prototype-qualified/member-stock.log',
        'prototype-qualified/EXISTING_TWO_PRODUCER_PRECHECK.json', 'prototype-qualified/install-controller.log',
        'prototype-qualified/trace-adoption-v1/FINAL_RESULT.json',
        'prototype-qualified/trace-adoption-v1/stage1-STOCK.json',
        'prototype-qualified/trace-adoption-v1/stage1-stock.log',
        'prototype-qualified/trace-adoption-v1/stage1-ActualSieveGate-original-Member.trace',
        'prototype-qualified/trace-adoption-v1/stage1-HalfProductMassFibres-original-Member.trace',
        'authentic-trace-adoption-controller.log', 'P6_SINGLE_NATIVE_COPY_COMPLETE.json',
        'P6_SINGLE_NATIVE_PRODUCER_STOCK.json', 'p6-single-native-stock.log', 'member-single-native-stock.log']
    for relative in aggregate_files:
        add(AGG / relative, 'original/aggregate/' + relative)
    t01_files = ['PUBLISHABLE_SUMMARY.json', 'FINALIZATION_RECEIPT.json', 'READY.json',
                 'install-v1/COPY_COMPLETE.json', 'install-v1/RESTORE_JOURNAL.jsonl',
                 'install-v1/STOCK_RESULT.json', 'install-v1/stock.stdout', 'install-v1/stock.stderr']
    for relative in t01_files:
        add(T01 / relative, 'original/t01-new90/' + relative)
    helpers = [Path('/workspace/blue-build-tools') / name for name in [
        'hold_compiler_gate.py', 'qualify_member_t01_project90_v1.py', 'install_member_t01_project90_v1.py']]
    helpers += [AGG / name for name in ['stop_old_at_checkpoint.py', 'qualify_prototype_groups.py',
                                      'restore_prototype_groups.py', 'adopt_authentic_traces.py', 'reuse_one_native.py']]
    for path in helpers:
        add(path, 'executed-helper-snapshots/' + path.name)
    survey = Path('/workspace/artifacts/member-native-artifact-survey-20261123.json')
    add(survey, 'original/member-native-artifact-survey-20261123.json')
    save('OMITTED_LARGE_RECORDS.json', {
        'schema': 'member_cache_window_omitted_original_record_references_v1',
        'records_read_and_compacted': [REFERENCES[str(p)] for p in [
            AGG / 'checkpoint-v1/COMPLETED_MODULES_BEFORE_TERMINATION.json',
            AGG / 'prototype-qualified/INSTALL_RECEIPT.json', AGG / 'P6_SINGLE_NATIVE_INSTALL_RECEIPT.json',
            AGG / 'prototype-qualified/trace-adoption-v1/stage1-ADOPTION.json']],
        'other_original_map_bindings_from_prior_receipts_not_requalified_here': [
            {'path': str(AGG / 'prototype-qualified/MANIFEST.json'), 'sha256': proto['qualification_manifest_sha256'],
             'bytes': (AGG / 'prototype-qualified/MANIFEST.json').stat().st_size},
            t01['new_project_candidates']['candidate_manifest'], t01['new_project_candidates']['qualified_compact_manifest']],
        'compiled_payloads_included': False, 'archive': t01['archive_used'],
        'scope': 'Omitted maps are identity references, not portable cache payloads. No original map or expected hash was rewritten.'})
    save('PUBLICATION_SUMMARY.json', {
        'schema': 'member_completed_cache_window_compact_publication_v1',
        'scope': 'Historical cache reuse/operator evidence only; no new theorem or node credit',
        'safe_checkpoint': {'exit': 241, 'kind': 'authorized operator stop between compilers', 'successful_selected_groups_preserved_across_stop': 1242},
        'T01_new90': {'qualified': 26, 'actually_copied_groups': 8, 'copied_facets': 64, 'became_present_no_copy': 18, 'blocked': 64},
        'Prototype': {'copied_project_groups': 9, 'copied_facets': 72, 'native_groups_already_present_no_copy': 23,
                      'initial_stock_exit': 3, 'final_stock_exit': 0},
        'P6_native': {'module': native['module'], 'copied_groups': 1, 'copied_facets': 8, 'destination_stock_exit': 0},
        'explicit_working_trace_exceptions': [group['module'] for group in adoption['groups']],
        'authentic_auxiliary_completions_before_nontrace_stability_boundary': completed_c,
        'all_final_destination_stocks_zero_Member_source_calls': True,
        'source_proof_setup_frozen_archives_unchanged_by_trace_adoption': True,
        'all_working_traces_never_changed': False,
        'no_builds_or_qualifications_rerun_to_prepare_packet': True,
        'native_cache_transport_survey': {'path': str(survey), 'sha256': digest(survey)['sha256'],
                                           'status': 'metadata candidates only; no accessible existing transport established; no download/token/dispatch pursued'},
        'credit': 0})
    readme = '''The completed Member cache window restored 8 T01 project groups (64 facets),
9 Prototype project groups (72 facets), and the single P6 native TailPropagation
group (8 facets). T01 qualified 26 of 90 completed candidates: 18 were already
present by the copy window and were preserved; 64 were blocked by actual input
object differences. All 23 eligible Prototype native groups were already present.
These counts describe cache reuse and carry no new theorem or node credit.

The existing compiler lock was acquired after the running Lean exited naturally.
Only the old Lake controller and its captured waiting wrappers were stopped.
The final exit 241 is an authorized operator stop, not a new proof failure.
The original log retains nine earlier source failures. Its SHA and the original
stop receipt bind 1242 selected successes preserved immediately across the stop.

The first Prototype destination stock returned 3. With explicit authorization,
two working Member traces, HalfProductMassFibres and ActualSieveGate, were then
replaced with exact existing producer bytes. Their original raw Member traces
are retained. No depHash, output hash or synthetic field was edited. Four missing
auxiliary files (two generated .c files and their two .c.hash files) were copied
authentically first. Nontrace stability is asserted from AFTER this C completion
through trace adoption and stock. This packet does not claim all working traces
were unchanged. The optional LogCutoffError/PowerErrorBudget stage never ran.

The final T01, Prototype and native destination stocks returned 0 with zero
Member source/native compiler calls in their recorded scopes. Historical fields
saying the new aggregate had not started refer to this window, not current work.

This publication performs only static receipt-chain reading and compact extraction.
It runs no Lean, Lake, kernel checker, cache installer, qualifier or network request.
Large import maps and compiled payloads stay local; their original record hashes
are listed. The separate native-artifact survey remains metadata-only and does not
establish reusable cache objects or an accessible transport.

T01 helper snapshots match receipt-recorded executed SHA256 values. Other helper
snapshots are the existing scripts at the paths used by the retained controller
logs/receipts; those records do not uniformly contain an executed-file SHA field.
No historical execution digest is invented for them.
'''
    (OUT / 'README.md').write_text(readme)
    for path in sorted(OUT.iterdir()):
        if path.is_file() and path.name != 'PUBLISH_FILES.json':
            add(path, 'compact/' + path.name)
    assert len({item['destination'] for item in selected}) == len(selected)
    total = sum(item['bytes'] for item in selected)
    assert total < 1_000_000, total
    save('PUBLISH_FILES.json', {'schema': 'reviewable_publish_files_v1', 'source_root': str(OUT),
                               'destination_root': DEST, 'files': selected,
                               'total_selected_bytes': total,
                               'no_source_cache_trace_or_original_record_mutations': True,
                               'no_checks_or_compilers_rerun': True})
    print(json.dumps({'files': len(selected), 'selected_bytes': total,
                      'manifest_sha256': digest(OUT / 'PUBLISH_FILES.json')['sha256']}))


if __name__ == '__main__':
    main()
