#!/usr/bin/env python3
"""Audit the seven existing cell12 stress candidates without executing Lean."""
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import re
import sys
import tarfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DOCS = REPO / 'docs/verification/20261126-p26/scalable-geometry-cell12-stress-audit'
TAG = 'P2OriginalSaving19Geometry12Scalable'
RAW = 'ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12'
N = 14461008


def pin_data(data):
    return {'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}


def fp(path):
    path = Path(path)
    return {'path': str(path.relative_to(REPO)), **pin_data(path.read_bytes())}


def same(left, right):
    return all(left[key] == right[key] for key in ('bytes', 'sha256'))


def write_new(path, value):
    path = Path(path)
    data = value if isinstance(value, bytes) else value.encode() if isinstance(value, str) else (json.dumps(value, indent=2) + '\n').encode()
    if path.exists():
        assert path.read_bytes() == data, ('Frozen audit drift', str(path))
    else:
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open('xb') as out:
            out.write(data)


@lru_cache(None)
def shape(n):
    """Count the exact size-only packTreeGo shape, not Lean reduction time."""
    if n <= 256:
        return {'leaves': 1, 'nodes': 1, 'min_leaf_chars': n, 'max_leaf_chars': n, 'depth': 0}
    left, right = shape(n // 2), shape(n - n // 2)
    return {'leaves': left['leaves'] + right['leaves'], 'nodes': 1 + left['nodes'] + right['nodes'],
            'min_leaf_chars': min(left['min_leaf_chars'], right['min_leaf_chars']),
            'max_leaf_chars': max(left['max_leaf_chars'], right['max_leaf_chars']),
            'depth': 1 + max(left['depth'], right['depth'])}


def locate(n, pos, base=0, index=0):
    assert 0 <= pos < n
    if n <= 256:
        return {'index': index, 'start': base, 'count': n, 'within': pos}
    cut = n // 2
    if pos < cut:
        return locate(cut, pos, base, index)
    return locate(n-cut, pos-cut, base+cut, index+shape(cut)['leaves'])


def drop_cost(n, skip):
    if n <= 256:
        return {'drop_branch_tests': 0, 'recursive_count_node_visits_no_cache': 0,
                'recursive_count_leaf_visits_no_cache': 0}
    cut = n // 2
    counts = shape(cut)
    child = drop_cost(cut, skip) if skip < cut else drop_cost(n-cut, skip-cut)
    return {'drop_branch_tests': 1 + child['drop_branch_tests'],
            'recursive_count_node_visits_no_cache': counts['nodes'] + child['recursive_count_node_visits_no_cache'],
            'recursive_count_leaf_visits_no_cache': counts['leaves'] + child['recursive_count_leaf_visits_no_cache']}


def protected():
    base = REPO / 'docs/verification/20261126-p26'
    handoffs = [
        base / 'scalable-geometry-cell05/HANDOFF_STAGING_FILES.txt',
        base / 'scalable-geometry-cell05-complete/HANDOFF_STAGING_FILES_V3.txt',
        base / 'scalable-geometry-cell05-fields/workflow-v1/HANDOFF_STAGING_FILES.txt',
        base / 'scalable-geometry-cell05-connections/a_parse_decode/HANDOFF_STAGING_FILES.txt',
        base / 'scalable-geometry-cell05-connections/b_finite_shape/HANDOFF_STAGING_FILES.txt']
    paths = set()
    for handoff in handoffs:
        paths.update(handoff.read_text().splitlines())
    return [fp(REPO / path) for path in sorted(paths)]


def main():
    frozen = protected()
    pilot = REPO / 'tools/p26/scalable'
    sources = json.loads((pilot / 'SOURCE_MANIFEST.json').read_text())
    verifier = json.loads((pilot / 'ScalableGeometry_VERIFIER.json').read_text())
    source_rows = [row for row in sources['owners'] if row['cell'] == 12]
    old_targets = {row['module']: row for row in verifier['targets'] if 'Geometry12Scalable' in row['module']}
    old_suppliers = json.loads((pilot / 'SUPPLIER_PINS.json').read_text())
    suppliers = [row for row in old_suppliers['suppliers'] if 12 in row['cells']]
    assert len(source_rows) == len(old_targets) == 7 and len(suppliers) == 9
    supplied = {row['module']: row for row in suppliers}
    generic = set(supplied) - {RAW}
    graph = {row['module']: row['project_imports'] for row in suppliers + source_rows}

    def closure(module):
        seen, active = set(), set()
        def visit(name):
            assert name in graph and name not in active
            if name in seen:
                return
            active.add(name)
            for child in graph[name]:
                visit(child)
            active.remove(name)
            seen.add(name)
        for dependency in graph[module]:
            visit(dependency)
        return sorted(seen)

    targets, windows = [], []
    template = (pilot / 'owned-audits/P2OriginalSaving19Geometry05ScalableInput.lean').read_text()
    for row in source_rows:
        module = row['module']
        path = REPO / row['source']['path']
        text = path.read_text()
        assert same(fp(path), row['source']) and same(row['source'], old_targets[module]['source'])
        assert re.findall(r'(?m)^import\s+(ImbalancedChen\.\S+)', text) == row['project_imports']
        assert not re.search(r'\b(?:sorry|admit|native_decide|unsafe)\b|(?m:^\s*axiom\b)', text)
        audit = pilot / 'owned-audits' / (module.split('.')[-1] + '.lean')
        assert same(fp(audit), old_targets[module]['audit'])
        assert audit.read_text() == template.replace('ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput', module)
        entry = {'module': module, 'source': fp(path), 'audit': fp(audit),
                 'project_imports': row['project_imports'], 'transitive_dependencies': closure(module),
                 'planned_obligations': row['planned_obligations'], 'object': None, 'receipts': None,
                 'existing_mathematical_source_reusable_unchanged': True,
                 'current_known_status': 'SOURCE_ONLY_NO_ACCEPTED_CELL12_RECEIPT_IN_PUBLISHED_CHECKPOINT',
                 'cloud_success_census_before_execution_required': True, 'required_missing_steps': ['normal', 'kernel', 'owned']}
        targets.append(entry)
        if 'SimplicesBlock' in module:
            plan = row['planned_obligations']
            chunks = plan['selected_chunks']
            assert len(chunks) == 8 and all(chunk['after'] - chunk['first'] == 1 for chunk in chunks)
            assert all(a['end'] == b['start'] and a['after'] == b['first'] for a, b in zip(chunks, chunks[1:]))
            start, end = plan['raw_span']
            assert (start, end) == (chunks[0]['start'], chunks[-1]['end'])
            assert text.count('theorem block_original_prefix :') == 1
            assert f'(sourceRest {start}).take {end-start} = blockChars := by rfl' in text
            first_leaf, last_leaf = locate(N, start), locate(N, end-1)
            windows.append({'module': module, 'rows': [chunks[0]['first'], chunks[-1]['after']],
                            'raw_span': [start, end], 'raw_chars': end-start,
                            'terminates_original_array': chunks[-1]['final'],
                            'before_fuel_offset': chunks[0]['before_offset'],
                            'after_fuel_offset': chunks[-1]['after_offset'],
                            'packed_prefix_binding_theorems': 1,
                            'first_packed_leaf': first_leaf, 'last_packed_leaf': last_leaf,
                            'packed_leaves_touched_by_window': last_leaf['index']-first_leaf['index']+1,
                            **drop_cost(N, start)})
    assert sum(b-a for a,b in (row['rows'] for row in windows)) == 24
    assert len([row for row in windows if row['terminates_original_array']]) == 1

    archive = REPO / 'docs/verification/20261126-p26/geometry01-decoded-shape/suppliers.tar.xz'
    generic_evidence = []
    with tarfile.open(archive, 'r:xz') as tar:
        metadata = json.load(tar.extractfile('Geometry01Decoding_SUPPLIERS.json'))
        available = {row['module']: row for row in metadata['accepted']}
        for module in sorted(generic):
            record, expected = available[module], supplied[module]
            checked_members = []
            def checked(identity):
                member = identity['archive_member']
                item = tar.getmember(member)
                assert item.isfile()
                data = tar.extractfile(item).read()
                assert same(pin_data(data), identity)
                checked_members.append({'member': member, **pin_data(data)})
                return data
            for kind in ('source', 'object'):
                assert same(record[kind], expected[kind])
                checked(record[kind])
            assert same(fp(REPO / (module.replace('.', '/') + '.lean')), expected['source'])
            observed = {}
            for mode in ('normal', 'kernel'):
                receipt = record['receipts'][mode]
                document = json.loads(checked(receipt))
                command = document['commands'][receipt['embedded_command_index']] if 'embedded_command_index' in receipt else document
                assert command['module'] == module and command['exit_code'] == 0
                assert same(command['source'], expected['source']) and same(command['object'], expected['object'])
                log = checked(receipt['log'])
                argv = command.get('argv', command.get('command'))
                assert argv and argv[0].split('/')[-1] == ('leanchecker' if mode == 'kernel' else 'lean')
                if mode == 'kernel':
                    assert argv[1:] == ['--verbose', module]
                    assert log.decode().strip() == 'replaying ' + module
                else:
                    assert '-o' in argv and argv[argv.index('-o')+1] == command['object']['path']
                    assert argv[-1] == command['source']['path'] or argv[-1] == module.replace('.', '/') + '.lean'
                assert same(command['log'], receipt['log'])
                observed[mode] = {'receipt': receipt, 'argv': argv, 'cwd': command.get('cwd', document.get('working_directory')),
                                  'exit_code': 0, 'source_object_and_log_pins_rechecked': True}
            generic_evidence.append({'module': module, 'source': expected['source'], 'object': expected['object'],
                                     'project_imports': expected['project_imports'],
                                     'status': 'PUBLISHED_ACCEPTED_NORMAL_KERNEL_BYTES_RECHECKED',
                                     'independent_kernel_receipt_materialized': True,
                                     'checked_archive_members': checked_members, 'receipts': observed,
                                     'existing_source_object_bodies_must_not_be_recompiled': True})

    reused_path = REPO / ('tools/p26/scalable-cell05-complete/baseline/raw05-history/previous-p1-evidence/'
                         'runs/attempt-00000/REUSED_PRECEDING_ACCEPTANCE.json')
    raw_history = next(row for row in json.loads(reused_path.read_text()) if row['module'] == RAW)
    raw_expected = supplied[RAW]
    original = next(row for row in sources['inputs'] if row['cell'] == 12)
    assert original['input']['bytes'] == N
    source_targets = REPO / 'docs/verification/20261125-p26/archive-core-continuation/SOURCE_TARGETS.json'
    original_core = next(row for row in json.loads(source_targets.read_text())['original_loader_inputs']
                         if row['family'] == 'geometry' and row['cell'] == 12)
    assert same(original['input'], original_core)
    raw_supplier = {**raw_expected, 'status': 'EXACT_OBJECT_USAGE_PIN_AND_HISTORICAL_LOCATORS_ONLY',
                    'historical_receipt_bytes_materialized_here': False,
                    'independent_current_context_kernel_closed': False,
                    'normal_recompile_to_recover_missing_evidence_forbidden': True,
                    'normal_locator': raw_history['normal_receipt'], 'audit_locators': raw_history['audit_receipts'],
                    'successful_wrapper_locators': raw_history['successful_wrapper_runs']}
    write_new(DOCS / 'SUPPLIER_MAP.json', {
        'schema': 'cell12_stress_supplier_map_v1', 'generic_archive': fp(archive),
        'generic_suppliers': generic_evidence, 'raw12_supplier': raw_supplier,
        'old_supplier_count': 9, 'generic_suppliers_with_actual_receipt_bytes_rechecked': 8,
        'full_supplier_kernel_closed': False,
        'runtime': json.loads((REPO / 'tools/p26/scalable-cell05-complete/SUPPLIER_REGISTRY.json').read_text())['runtime_binaries']})
    write_new(DOCS / 'RAW12_HISTORY_LOCATORS.json', {
        'schema': 'cell12_raw_history_locators_v1', 'locator_source': fp(reused_path),
        'original_input': original_core, 'exact_source': raw_expected['source'], 'exact_object': raw_expected['object'],
        'module': RAW, 'historical_locations': raw_history,
        'locator_is_acceptance': False, 'current_context_compatibility_pending': True,
        'eight_current_generic_suppliers': [{key: row[key] for key in ('module', 'source', 'object')}
                                           for row in generic_evidence]})
    order = [TAG + suffix for suffix in ['Input', 'SimplicesBlock824', 'TypedRows824',
                                         'SimplicesBlock000', 'TypedRows000', 'SimplicesBlock412', 'TypedRows412']]
    by_module = {row['module']: row for row in targets}
    ordered = [by_module['ImbalancedChen.' + module] for module in order]
    known = set(supplied)
    for row in ordered:
        assert set(row['project_imports']) <= known
        known.add(row['module'])
    write_new(DOCS / 'STRESS_EXECUTION_PLAN.json', {
        'schema': 'cell12_existing_seven_owner_stress_plan_v1', 'status': 'SOURCE_REUSABLE_SUPPLIER_GATE_PENDING',
        'targets': ordered, 'target_count': 7, 'maximum_new_steps': 21,
        'new_steps_run': 0, 'accepted_new_steps': 0,
        'source_bytes': sum(row['source']['bytes'] for row in targets),
        'current_known_accepted_cell12_owners': [],
        'cloud_object_and_receipt_census_not_yet_run': True,
        'required_gates': ['recover_and_validate_raw12_historical_normal_kernel_owned_bytes',
                           'compare_historical_and_current_dependency_objects_and_runtime',
                           'if_context_differs_one_raw12_kernel_compatibility_addendum_without_normal_replay',
                           'inventory_prior_cell12_objects_and_all_success_markers_before_any_proof_command',
                           'freeze_one_namespace_stage_nine_suppliers_and_seven_target_context',
                           'review_adapted_v3_runner_before_proof_execution'],
        'preferred_phases': [{'phase': 'input', 'owners': 1, 'new_steps_if_missing': 3},
                             {'phase': 'end_final_delimiter', 'owners': 2, 'new_steps_if_missing': 6},
                             {'phase': 'begin_largest_selected_window', 'owners': 2, 'new_steps_if_missing': 6},
                             {'phase': 'middle', 'owners': 2, 'new_steps_if_missing': 6}],
        'all_receipt_reuse_requires_same_context_strict_v3_validator': True,
        'broken_or_missing_success_chain_requires_exact_recovery_not_recompilation': True,
        'node_owner_in_existing_seven': False, 'separated_blocks_cannot_be_directly_composed': True,
        'optional_later_adjacency_probe': {'new_owners': 3, 'rows': [8,16],
            'names': [TAG+'SimplicesBlock001', TAG+'TypedRows001', TAG+'RowsNode000To001'],
            'source_authored': False, 'requires_original_raw12_bytes_locally': True,
            'runs_only_after_initial_seven_and_root_scheduling': True},
        'whole_cell12_parse_or_decode': False, 'P2_6_complete': False})
    write_new(DOCS / 'STRUCTURAL_COST_MODEL.json', {
        'schema': 'cell12_packed_offset_source_structural_model_v1',
        'status': 'HOST_STRUCTURAL_ANALYSIS_NOT_MEASURED_LEAN_COST',
        'assumptions': ['published_original_input_is_ASCII_with_N_characters',
                        'exact_published_loader_quotes_packTreeGo_using_blockLimit_256',
                        'Tree.count_visits_are_counted_without_evaluator_memoization'],
        'source_bindings': [fp(REPO/'ImbalancedChen/P2OriginalSaving19PackedChars.lean'),
                            fp(REPO/'ImbalancedChen/P2OriginalSaving19ArchivePackedLoader.lean')],
        'input': original, 'cell05_comparison': shape(201042), 'cell12_tree': shape(N), 'windows': windows,
        'offset_is_only_logarithmic_cost_claimed': False, 'runtime_or_memory_prediction_claimed': False,
        'input_count_theorem_traverses_entire_tree': True,
        'block_prefix_reads_only_selected_character_window_after_tree_drop': True,
        'generic_drop_transport_does_not_reparse_skipped_json': True})
    assert protected() == frozen
    write_new(DOCS / 'LOCAL_AUDIT.json', {
        'schema': 'cell12_stress_local_static_audit_v1',
        'status': 'PASS_EXISTING_SOURCE_AUDIT_PIN_AND_PUBLISHED_GENERIC_RECEIPT_READBACK',
        'frozen_sources_unchanged': 7, 'frozen_owned_audits_unchanged': 7,
        'existing_generic_normal_kernel_receipts_rechecked': 16,
        'raw12_historical_receipts_still_locators_only': True,
        'original_input_bytes_pinned': N, 'original_input_bytes_present_locally': False,
        'source_only_selected_rows': 24, 'new_Lean_steps_run': 0, 'new_mathematical_sources_generated': 0,
        'protected_files': frozen, 'audit_tool': fp(Path(__file__)),
        'complete_cell12_or_geometric_integral_claims': False,
        'old_unpublished_Geometry02To12Decoding_FEASIBILITY_available_after_reset': False})
    print(json.dumps({'status': 'STATIC_AUDIT_COMPLETE_RAW12_EVIDENCE_GATE_PENDING',
                      'sources': 7, 'audits': 7, 'source_bytes': sum(row['source']['bytes'] for row in targets),
                      'generic_suppliers_checked': 8, 'generic_receipts_checked': 16,
                      'protected_files_unchanged': len(frozen), 'new_Lean_steps_run': 0}))


if __name__ == '__main__':
    main()
