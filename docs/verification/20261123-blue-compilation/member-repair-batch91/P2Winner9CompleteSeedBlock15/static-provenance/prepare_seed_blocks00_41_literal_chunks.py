from pathlib import Path
import ast
import datetime
import difflib
import hashlib
import json
import os
import re
import stat

W = Path('/workspace')
P = W / 'p1-complete-proof'
O = P / 'static-seed-blocks00-41-literal-chunks'
T = P / 'static-seed-block42-literal-chunks'
CONTEXT = P / 'modern-p1-build/incremental-six-root-after-source-repairs/SOURCE_CONTEXT.json'
FAILURE_DIR = CONTEXT.parent / 'failure-observation-0006'
ORIGINAL_SCRIPT = Path('/tmp/prepare_seed_block42_literal_chunks.py')
SEED42_LEAF = W / 'blue-member-repair-batch84/seed42-owned-only/SEED42_COMPLETE_OWNED_SUPPLEMENT_RESULT.json'
SCHEMA = W / 'blue-member-build/ImbalancedChen/P2Winner9CompleteSeedTypes.lean'
UTC = datetime.datetime.now(datetime.timezone.utc).isoformat()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def token(s):
    return [s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns]


def stable_read(path):
    pre = path.stat()
    assert stat.S_ISREG(pre.st_mode)
    with path.open('rb') as stream:
        opened = os.fstat(stream.fileno())
        raw = stream.read()
        closed = os.fstat(stream.fileno())
    post = path.stat()
    assert token(pre) == token(opened) == token(closed) == token(post), str(path)
    assert len(raw) == pre.st_size
    return raw, {'path': str(path), 'bytes': len(raw), 'sha256': sha(raw),
                 'before_open_after_stat_token': token(pre),
                 'single_source_read_stable': True}


assert not O.exists(), 'Never overwrite a prior packet or repeat live source reads.'
original_script, original_script_record = stable_read(ORIGINAL_SCRIPT)
original_text = original_script.decode()
core_start = original_text.index("header=b'def rows : Array RawRow :='")
core_end = original_text.index('\nfailure_dir=', core_start)
original_core = original_text[core_start:core_end]
adapted_core = original_core
substitutions = [
    ("b']\\r\\n\\r\\nend ImbalancedChen.P2Winner9CompleteSeedBlock42\\r\\n'",
     "b']\\r\\n\\r\\nend '+module.encode()+b'\\r\\n'", 1),
    ('list(range(10752,11008))', 'list(range(seed_index*256,(seed_index+1)*256))', 1),
    ("schema_path=W/'blue-member-build/ImbalancedChen/P2Winner9CompleteSeedTypes.lean';schema=schema_path.read_bytes();schema_fields=[m.group(1).decode()for m in re.finditer(rb'(?m)^  (\\w+) : ',schema)];assert len(schema_fields)==27",
     'assert len(schema_fields)==27', 1),
    ('10752+16*n', 'seed_index*256+16*n', 2),
]
for old, new, count in substitutions:
    assert adapted_core.count(old) == count, repr(old)
    adapted_core = adapted_core.replace(old, new)
assert '744cc6' not in adapted_core and '11008' not in adapted_core
function_source = ('def transform(before, module, seed_index, schema_fields):\n' +
                   ''.join('    ' + line + '\n' for line in adapted_core.splitlines()) +
                   '    return locals()\n')
ast.parse(function_source)
namespace = {'re': re, 'sha': sha}
exec(compile(function_source, 'EXACT_PARAMETERIZED_TEMPLATE_CORE.py', 'exec'), namespace)
transform = namespace['transform']

context_raw, context_record = stable_read(CONTEXT)
assert sha(context_raw) == 'db2dfc6e2ae8357ded33da4d3f5f938284db78ebaf5d6caa17d097d4ff5f3538'
context = json.loads(context_raw)
failure_raw, failure_record = stable_read(FAILURE_DIR / 'ACTUAL_FAILURES.json')
assert sha(failure_raw) == '4106f851de6944289f824b9cd26a6996e6b2118819e6e234a8f725e7a82f5600'
failures = json.loads(failure_raw)
failure_map = {row['module']: row for row in failures['modules']}
schema_raw, schema_record = stable_read(SCHEMA)
assert sha(schema_raw) == 'c291fe7225785a7b52807f7c799ccafbd7aae00c9944848785fd5cb8411be34d'
schema_fields = [m.group(1).decode() for m in re.finditer(rb'(?m)^  (\w+) : ', schema_raw)]
assert len(schema_fields) == 27
leaf_raw, leaf_record = stable_read(SEED42_LEAF)
assert sha(leaf_raw) == 'ce68a26adb94dbfc26fff5b9ddd8a2b4d91ea977320a6b7e72e808bbd27a30c4'
leaf = json.loads(leaf_raw)
assert leaf['source_sha256'] == 'b73e0d902f6ef7e494b2698b45b74978f3aa98e979b852eb45f9ea680720e8d8'
assert (leaf['owned_total'], leaf['public_total'], leaf['private_total']) == (17, 1, 16)
assert leaf['source_plus_five_outputs_stable'] and leaf['actual_audit_command']['exit_code'] == 0

O.mkdir()
artifacts = []


def put(relative, raw):
    path = O / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('xb') as stream:
        stream.write(raw)
    record = {'path': path.relative_to(O).as_posix(), 'bytes': len(raw), 'sha256': sha(raw)}
    artifacts.append(record)
    return record


def put_json(relative, value):
    return put(relative, (json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode())


put('prepare_seed_blocks00_41_literal_chunks.py', Path(__file__).read_bytes())
put('bound-inputs/ORIGINAL_SEED42_PREPARATION.py', original_script)
put('recipe/ORIGINAL_TEMPLATE_CORE.py.txt', original_core.encode())
put('recipe/EXACT_PARAMETERIZED_TEMPLATE_CORE.py', function_source.encode())
put('recipe/CORE_ADAPTATION.patch', ''.join(difflib.unified_diff(
    original_core.splitlines(True), adapted_core.splitlines(True),
    fromfile='original-Seed42-core', tofile='same-core-module-and-ordinal-parameters')).encode())
put('bound-inputs/SOURCE_CONTEXT.json', context_raw)
put('bound-inputs/ACTUAL_FAILURES_0006.json', failure_raw)
put('bound-inputs/P2Winner9CompleteSeedTypes.lean', schema_raw)
put('bound-inputs/SEED42_COMPLETE_OWNED_SUPPLEMENT_RESULT.json', leaf_raw)
bound_reuse = []
for name, expected in [
    ('SOURCE_SELECTION.json', '013b842c991d1d78bd7773d7876229407bf3b04be2d1bf43700a30ee6cc83501'),
    ('REPRESENTATION_AND_REVERSE.json', 'bde58aceae290ff84d63bc8df11b6d9d7bc7bd5780748182f4e5b2be5e18e889'),
    ('INDEPENDENT_ROOT_STATIC_REVIEW.json', '836cfe049235aad82a78c8608906650a9d574c92ae39be99bab8fc4071c3cd67'),
    ('EXISTING_FAMILY_AND_CORE_API.json', '120065edf6ae7fb273502dd00f64e32a8d6cb2009ceca08a2d8543b627d22a49'),
]:
    raw, record = stable_read(T / name)
    assert sha(raw) == expected
    copied = put('bound-inputs/template42-' + name, raw)
    bound_reuse.append({'original': record, 'package_copy': copied})

put_json('RECIPE_REUSE_AND_BOUNDARIES.json', {
    'schema': 'exact_accepted_seed42_recipe_parameterization_v1',
    'author': '/root/omega_review', 'prepared_utc': UTC,
    'original_script': original_script_record,
    'original_core_sha256': sha(original_core.encode()),
    'adapted_core_sha256': sha(adapted_core.encode()),
    'only_core_substitutions': [{'old': a, 'new': b, 'occurrences': n} for a, b, n in substitutions],
    'function_wrapper': 'Indent the adapted core inside transform(before,module,seed_index,schema_fields) and return its locals; no conversion algorithm changes.',
    'shared_schema_io': 'Read exactly once outside the 42-module loop; pass the same 27 field names to the original core.',
    'exact_template_metadata_copies': bound_reuse,
    'template_acceptance_leaf': leaf_record,
    'accepted_template_public_header': 'def rows : Array RawRow :=',
    'accepted_template_postimage_sha256': leaf['source_sha256'],
    'accepted_template_owned_counts': {'total': 17, 'public': 1, 'private': 16},
    'template_acceptance_is_not_acceptance_of_any_new_candidate': True,
    'existing_Array_flatten_API_binding_reused_without_reopening_core_or_Seed42_data': True,
    'excluded_sources': ['ImbalancedChen.P2Winner9CompleteSeedBlock42', 'ImbalancedChen.P2Winner9CompleteSeedBlock43'],
    'excluded_Seed42_43_source_and_row_data_reads': 0,
    'history_import_map_cache_or_numeric_algorithm_scans': 0,
    'Lean_Lake_kernel_type_axiom_checker_calls': 0,
    'live_source_cache_guard_controller_queue_writes': 0,
})

summary_rows = []
live_reads = []
decl_pattern = rb'(?m)^(?:(private) )?def (\w+)\s*:'
for seed_index in range(42):
    short = f'P2Winner9CompleteSeedBlock{seed_index:02d}'
    module = 'ImbalancedChen.' + short
    source = W / 'blue-member-build/ImbalancedChen' / (short + '.lean')
    binding = context['effective_source_bindings'][module]
    failed = failure_map[module]
    assert binding['path'] == str(source)
    assert failed['source_sha256_at_initial_failure'] == binding['sha256']
    assert failed['current_sha256_at_observation'] == binding['sha256']
    assert failed['actual_lean_exit_code'] == 1
    before, read_record = stable_read(source)  # The only live read of this block.
    assert (sha(before), len(before)) == (binding['sha256'], binding['bytes']), module
    result = transform(before, module, seed_index, schema_fields)
    after = result['after']
    assert len(after) - len(before) == 1064
    old_decls = re.findall(decl_pattern, before)
    new_decls = re.findall(decl_pattern, after)
    assert old_decls == [(b'', b'rows')]
    assert new_decls == [(b'private', f'rowsChunk{n:02d}'.encode()) for n in range(16)] + old_decls
    assert re.findall(rb'(?m)^(?:theorem|lemma|axiom|opaque|abbrev|instance|set_option)\b', after) == []
    assert re.findall(rb'\b(?:sorry|admit|native_decide|run_tac)\b', after) == []
    assert after.replace(b'\r\n', b'').count(b'\n') == 0
    assert len(result['row_records']) == 256
    assert sum(len(x['fields_in_original_order']) for x in result['row_records']) == 6912
    assert len(result['chunk_records']) == 16
    assert result['reconstructed'] == before
    assert result['prefix'] == before[:result['h']] and after.endswith(result['suffix'])
    slice_path = FAILURE_DIR / failed['raw_failure_slice']
    assert slice_path.name == short + '.failure.log'
    failure_slice, slice_record = stable_read(slice_path)
    assert sha(failure_slice) == failed['slice_sha256']
    assert len(failure_slice) == failed['raw_byte_end_exclusive'] - failed['raw_byte_start']
    assert b':7:4: maximum recursion depth has been reached' in failure_slice
    assert b'-DmaxRecDepth=100000' in failure_slice
    assert b'memory_exception' not in failure_slice
    relative = short + '/'
    module_start = len(artifacts)
    baseline_record = put(relative + 'baseline.lean', before)
    candidate_record = put(relative + 'candidate.lean', after)
    put(relative + 'candidate.patch', ''.join(difflib.unified_diff(
        before.decode().splitlines(True), after.decode().splitlines(True),
        fromfile='original/' + short + '.lean',
        tofile='same-accepted-16x16-recipe/' + short + '.lean')).encode())
    failure_copy = put(relative + 'ACTUAL_FAILURE_SLICE.log', failure_slice)
    row_record = put_json(relative + 'ALL_256_ROWS_AND_6912_FIELDS.json', {
        'schema': 'exact_raw_literal_row_and_field_span_preservation_v1',
        'module': module, 'baseline': baseline_record, 'candidate': candidate_record,
        'row_count': 256, 'field_count_per_row': 27, 'total_field_spans': 6912,
        'first_ordinal': seed_index * 256, 'last_ordinal': (seed_index + 1) * 256 - 1,
        'schema_field_order': schema_fields,
        'original_concatenated_raw_row_bytes_sha256': sha(b''.join(result['rows'])),
        'candidate_concatenated_raw_row_bytes_sha256': sha(b''.join(result['new_rows'])),
        'all_original_raw_rows_and_fields_equal_at_recorded_candidate_spans': True,
        'rows': result['row_records'],
        'semantic_numerical_recomputation_performed': False,
    })
    representation_record = put_json(relative + 'REPRESENTATION_AND_REVERSE.json', {
        'schema': 'same_accepted_seed42_literal_representation_and_whole_reverse_v1',
        'module': module, 'baseline': baseline_record, 'candidate': candidate_record,
        'original_public_header': result['header'].decode(),
        'candidate_public_header': result['header'].decode(),
        'public_header_sha256': sha(result['header']),
        'public_definition_BODY_changed': True,
        'original_unelaborated_definition_kernel_value_equality_claimed': False,
        'new_public_rhs': result['public_rhs'].decode(),
        'new_public_rhs_sha256': sha(result['public_rhs']),
        'original_public_body_sha256': sha(before[result['body_start']:result['suffix_start'] + 1]),
        'private_chunks': result['chunk_records'],
        'raw_prefix_bytes': len(result['prefix']), 'raw_prefix_sha256': sha(result['prefix']),
        'raw_suffix_bytes': len(result['suffix']), 'raw_suffix_sha256': sha(result['suffix']),
        'unchanged_source_ranges': ['entire original prefix before public rows header', 'public rows header', 'all original raw rows and fields in original order', 'entire original suffix after original array closing bracket'],
        'entire_original_source_reverse_reconstructed_sha256': sha(result['reconstructed']),
        'whole_reverse_byte_exact': True,
        'reconstruction_recipe': 'Take the 256 candidate raw row spans in chunk00..15 order; preserve every original comma+CRLF separator and final CRLF. Prepend the original prefix, exact public header, and literal opener; append the original closing bracket and unchanged suffix. The result equals baseline.lean byte for byte.',
        'all_imports_options_namespace_comments_other_headers_and_EOF_preserved': True,
        'CRLF_preserved': True,
        'original_named_declarations': [{'kind': 'public def', 'name': 'rows', 'header': result['header'].decode()}],
        'candidate_named_declarations': [{'kind': 'private def', 'name': f'rowsChunk{n:02d}', 'header': f'private def rowsChunk{n:02d} : Array RawRow :='} for n in range(16)] + [{'kind': 'public def', 'name': 'rows', 'header': result['header'].decode()}],
        'original_other_definitions_or_proofs': 0,
        'new_checker_numeric_algorithm_licence_hypothesis_rows_or_fields': False,
        'imports_options_budget_increases': False,
        'raw_row_and_field_evidence': row_record,
    })
    selection_record = put_json(relative + 'SOURCE_SELECTION.json', {
        'schema': 'seed_block00_41_exact_accepted_recipe_representation_candidate_v1',
        'author': '/root/omega_review', 'prepared_utc': UTC,
        'status': 'ISOLATED_UNCOMPILED_NOT_ADOPTION_AUTHORIZATION',
        'module': module, 'block': seed_index, 'live_source_read': read_record,
        'original_selected_context_binding': binding,
        'baseline': baseline_record, 'candidate': candidate_record,
        'actual_failure_classification': 'CONFIRMED_COMPLETED_ORIGINAL_UNIT_FAILURE_RECURSION_DEPTH',
        'actual_failure_observation': 'bound-inputs/ACTUAL_FAILURES_0006.json',
        'actual_failure_ledger_entry': failed, 'actual_failure_slice': failure_copy,
        'actual_failure_slice_original': slice_record,
        'failure_is_not_memory_exception': True,
        'authorized_representation_exception': 'Sixteen typed private Array RawRow definitions with 16 untouched original records each; original public rows name/type/header retained with same ordered array-of-chunks.flatten RHS as actually accepted Seed42.',
        'original_public_definition_BODY_changed': True,
        'old_unelaborated_definition_kernel_value_equality_claimed': False,
        'all_256_rows_and_27_fields_per_row_raw_byte_exact': True,
        'row_field_payload_order_values_changed': False,
        'whole_source_reverse_byte_exact': True,
        'new_private_chunks': 16, 'public_header_raw_preserved': True,
        'candidate_syntactic_named_definition_counts_not_actual_owned_audit': {'public': 1, 'private': 16},
        'same_template_recipe': 'recipe/EXACT_PARAMETERIZED_TEMPLATE_CORE.py',
        'representation_and_reverse': representation_record,
        'raw_rows_and_field_spans': row_record,
        'Lean_Lake_kernel_type_axiom_checker_calls': 0,
        'live_main_Member_siblings_cache_guard_queue_controller_or_old_record_mutations': False,
        'owner_must_recheck_actual_preimage_active_and_queued_writers_before_adoption': True,
        'actual_normal_kernel_and_full_owned_acceptance_required_per_module': True,
        'Seed42_acceptance_does_not_credit_this_module_or_whole_SeedData_or_P1': True,
    })
    module_files = artifacts[module_start:]
    put_json(relative + 'FILES_MANIFEST.json', {
        'schema': 'relative_seed_block_representation_candidate_files_v1',
        'module': module, 'paths_relative_to_family_packet': True,
        'files': list(module_files), 'manifest_excludes_itself': True,
    })
    live_reads.append(read_record)
    summary_rows.append({
        'module': module, 'block': seed_index,
        'initial_selected_source_sha256': binding['sha256'],
        'actual_failure_exit_code': 1,
        'actual_failure_classification': 'CONFIRMED_COMPLETED_ORIGINAL_UNIT_FAILURE_RECURSION_DEPTH',
        'baseline': baseline_record, 'candidate': candidate_record,
        'source_selection': selection_record,
        'representation_and_reverse': representation_record,
        'raw_rows_and_field_spans': row_record,
        'row_count': 256, 'field_count': 6912, 'private_chunks': 16,
        'first_ordinal': seed_index * 256, 'last_ordinal': (seed_index + 1) * 256 - 1,
        'whole_reverse_byte_exact': True,
        'actual_candidate_normal_kernel_owned_acceptance': False,
    })
    print(json.dumps({'prepared': module, 'post_sha256': sha(after), 'rows': 256, 'fields': 6912, 'whole_reverse_exact': True}), flush=True)

assert len(summary_rows) == len(live_reads) == 42
assert sum(row['row_count'] for row in summary_rows) == 10752
assert sum(row['field_count'] for row in summary_rows) == 290304
assert sum(row['private_chunks'] for row in summary_rows) == 672
assert [row['block'] for row in summary_rows] == list(range(42))
assert summary_rows[0]['first_ordinal'] == 0 and summary_rows[-1]['last_ordinal'] == 10751
put_json('LIVE_SOURCE_SINGLE_READ_RECEIPTS.json', {
    'schema': 'single_read_stat_stability_of_only_42_authorized_live_seed_sources_v1',
    'read_utc': UTC, 'live_block_source_reads': 42, 'sources': live_reads,
    'shared_schema_single_read': schema_record,
    'source_context': context_record, 'actual_failure_ledger': failure_record,
    'Seed42_Seed43_source_data_reads': 0,
    'no_final_live_reread': 'Owner must compare current preimage again at its later safe adoption window. This is an isolated source snapshot, not a concurrency/queue clearance.',
})
put_json('FAMILY_SOURCE_SELECTION.json', {
    'schema': 'seed_blocks00_through41_exact_recipe_source_only_family_v1',
    'author': '/root/omega_review', 'prepared_utc': UTC,
    'status': 'ISOLATED_UNCOMPILED_ALL_42_AWAIT_ROOT_NONAUTHOR_GATE_AND_OWNER_ACTUAL_VALIDATION',
    'modules': summary_rows,
    'module_count': 42, 'included_block_indices': list(range(42)),
    'excluded_already_accepted_block': 42, 'excluded_original_18_row_block': 43,
    'all_42_original_units_actually_failed_in_bound_0006_ledger': True,
    'source_context': context_record, 'failure_observation': failure_record,
    'actual_failure_master_prefix_is_bound_by_frozen_owner_ledger_not_rescanned_here': True,
    'old_0005_and_0b52_records_unchanged_not_reinterpreted': True,
    'row_count': 10752, 'field_count_per_row': 27, 'field_count': 290304,
    'new_private_chunks': 672, 'records_per_chunk': 16,
    'public_headers_unchanged': 42,
    'public_definition_BODY_representation_exceptions': 42,
    'old_unelaborated_kernel_value_equality_claimed': False,
    'all_original_row_field_bytes_order_ordinals_imports_options_namespaces_comments_and_EOF_preserved': True,
    'whole_original_source_reverse_byte_exact_per_module': True,
    'template_accepted_leaf': leaf_record,
    'template_acceptance_does_not_transfer_to_new_modules': True,
    'candidate_sources_actual_normal_kernel_owned_audits_performed_here': 0,
    'numeric_recomputation_checker_redesign_or_budget_increase': False,
    'live_main_Member_sources_or_caches_or_guard_runtime_or_queues_or_controllers_modified': False,
    'old_records_modified': False,
    'owner_only_adoption': 'Root reviews this exact family. Soleowner must verify current preimages and no active/queued writer, then adopt and validate through original guards without changing budgets. No installation/build/controller script is included.',
    'whole_P1_complete': False,
})
put('README.md', (
    '# Seed00–41 isolated representation candidates\n\n'
    'This packet prepares exactly 42 modules, blocks 00 through 41 inclusive. '
    'Block42 is already accepted and block43 remains its original 18-row source; neither source/data was read or changed here.\n\n'
    'The conversion core is copied from the accepted b73 Seed42 preparation script. '
    'The only core substitutions are module EOF name, block ordinal offset, and factoring one shared RawRow-schema read out of the loop. '
    'The full original core, parameterized function, exact adaptation diff, and original script are retained. '
    'Root static review836c and Seed42 normal/kernel/full-owned acceptance are template evidence only.\n\n'
    'Every module retains its original public `def rows : Array RawRow :=` header, imports, namespace, comments, source options and EOF. '
    'Its public BODY changes representation to the same 16-item ordered `.flatten` expression after sixteen private 16-record arrays. '
    'No old unelaborated kernel-value equivalence is claimed. The 256 original raw rows and all 6,912 original field spans per module '
    'are byte-bound at original and candidate offsets; reconstruction from candidate rows reproduces the whole baseline exactly. '
    'Across the family this is 10,752 rows, 290,304 fields and 672 new private chunks. '
    'Values are never recomputed, filtered, deduplicated or reordered.\n\n'
    'The frozen 0006 owner ledger records all 42 original units as actual recursion-depth failures at the original 100000 setting. '
    'Its exact source SHA values agree with db2 initial source context and each one-read live snapshot. '
    'The ledger and individual raw failure slices are copied byte-exact. No current master-log or history/import-map scan was performed.\n\n'
    'These new candidates are UNCOMPILED. The source-level count17 per module is not an actual environment audit. '
    'Root is the independent family gate; only soleowner may check current preimages and active/queued writers, adopt a safe module, '
    'and perform original-budget normal/kernel/full-owned validation. This packet does not clear queues, install sources, '
    'reuse proof objects, or establish complete SeedData/P1 acceptance.\n'
).encode())
put_json('FAMILY_FILES_MANIFEST.json', {
    'schema': 'relative_seed_blocks00_41_source_only_packet_files_v1',
    'author': '/root/omega_review', 'prepared_utc': UTC,
    'status': 'SOURCE_ONLY_UNCOMPILED',
    'files': sorted(artifacts, key=lambda x: x['path']),
    'manifest_excludes_itself': True,
    'old_records_unchanged': True,
})
for name in ['FAMILY_SOURCE_SELECTION.json', 'FAMILY_FILES_MANIFEST.json', 'RECIPE_REUSE_AND_BOUNDARIES.json']:
    record = next(row for row in artifacts if row['path'] == name)
    print(json.dumps({'final': record}), flush=True)
