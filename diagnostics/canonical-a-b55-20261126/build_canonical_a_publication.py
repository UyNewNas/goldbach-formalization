from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT = Path('/tmp/p24-integration-repairs-20261126')
OUT = ROOT / 'canonical-a-publication'
OUT.mkdir(exist_ok=True)
PREFIX = 'docs/source-only/20261125-p24-original-compact'
EVIDENCE = PREFIX + '/canonical-a-b55'
DIAGNOSTICS = 'diagnostics/canonical-a-b55-20261126'
PARENT = '12eefd99552b6a8540600a6334383d9724ec3c17'
BASE_TREE = 'f1f520791707ef604a94b2b7e6ef2620875a5f23'
SOURCE = 'b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
rows, elements, seen = [], [], set()

def sha(b):
    return hashlib.sha256(b).hexdigest()

def add(path, raw, origin, role):
    assert path not in seen
    seen.add(path)
    text = raw.decode('utf-8')
    assert text.encode('utf-8') == raw
    elements.append({'path': path, 'mode': '100644', 'type': 'blob', 'content': text})
    rows.append({'path': path, 'bytes': len(raw), 'sha256': sha(raw),
                 'origin': str(origin), 'role': role})

def add_file(path, source, role):
    source = Path(source)
    add(path, source.read_bytes(), source, role)

previous = json.loads((ROOT / 'joint321-publication/publication-files.json').read_bytes())
previous_by_origin = {r['origin']: r for r in previous['files']}
excluded = {'strict321-transfer-0.txt', 'strict321-transfer-1.txt'}
for source in sorted(ROOT.iterdir()):
    if not source.is_file() or source.name in excluded or source.suffix not in {
            '.json', '.log', '.py', '.sh', '.md', '.patch', '.lean'}:
        continue
    if str(source) in previous_by_origin:
        assert sha(source.read_bytes()) == previous_by_origin[str(source)]['sha256'], source
        continue
    target = DIAGNOSTICS if source.suffix in {'.sh', '.py', '.lean', '.patch'} else EVIDENCE
    add_file(target + '/' + source.name, source,
             'new actual task evidence or explicitly labelled prepared workflow')

for folder in ['a-capacity-diagnostic', 'storage-readonly']:
    for source in sorted((ROOT / folder).rglob('*')):
        if not source.is_file() or source.suffix not in {'.json', '.log', '.py', '.sh', '.md', '.patch', '.lean'}:
            continue
        if str(source) in previous_by_origin:
            assert sha(source.read_bytes()) == previous_by_origin[str(source)]['sha256'], source
            continue
        add_file(EVIDENCE + '/' + folder + '/' + source.relative_to(ROOT / folder).as_posix(),
                 source, 'capacity-only result or read-only storage evidence; no canonical audit credit')

for name in ['independent-publication-review.json', 'published-and-refetched.json']:
    source = ROOT / 'joint321-publication' / name
    add_file(EVIDENCE + '/prior-joint321-' + name, source, 'exact prior publication verification')

archive = ROOT / 'a-capacity-owned-eleven.tar.gz'
archive_raw = archive.read_bytes()
archive_desc = json.loads((ROOT / 'a-capacity-owned-eleven-evidence-descriptor.json').read_bytes())
archive_blob = json.loads((ROOT / 'a-capacity-owned-eleven-evidence-blob.json').read_bytes())
assert len(archive_raw) == archive_desc['bytes'] == 55692
assert sha(archive_raw) == archive_desc['sha256'] == '5ef0604e9008373524a1b82e5959258f0b6026f92a2c76c4bd96b1654db339a1'
git_blob = hashlib.sha1(b'blob ' + str(len(archive_raw)).encode() + b'\0' + archive_raw).hexdigest()
assert archive_blob['sha'] == git_blob
archive_target = EVIDENCE + '/a-capacity-owned-eleven.tar.gz'
elements.append({'path': archive_target, 'mode': '100644', 'type': 'blob', 'sha': git_blob})
rows.append({'path': archive_target, 'bytes': len(archive_raw), 'sha256': sha(archive_raw),
             'git_blob_sha': git_blob, 'origin': str(archive),
             'role': 'complete original A module log/record plus exact capacity and eleven-audit metadata'})

a = json.loads((ROOT / 'finite-a-b55-final-summary.json').read_bytes())
a_capture = json.loads((ROOT / 'finite-a-b55-final-capture.json').read_bytes())
a_task = a_capture['task']
a_raw = (ROOT / 'finite-a-b55-final.log').read_bytes()
assert a_task['status'] == 'succeeded' and a_task['exit_code'] == 0
assert not a_task['log_truncated'] and a_task['log_discarded_bytes'] == 0
assert len(a_raw) == a_task['log_bytes'] == 542967
assert sha(a_raw) == '2385df267ec1df7f4a9cca8faaa6795f9b9f44c4594166a3f05ef9f7f35d47b8'
assert a['source_pin'] == SOURCE and a['finite_A_compile_passed']
assert a['runner_exit_code'] == a['wrapper_exit_code'] == 0
assert len(a['postchecks']) == 10 and all(a['postchecks'].values()) and not a['postcheck_errors']
assert a['original_summary']['successful_closure'] == 102 and a['original_summary']['reused'] == 101
assert b'P24_Q80_ARCHIVED_DONE checked_blocks=2048 computed_nodes=131072 query_index=163840' in a_raw

capacity = json.loads((ROOT / 'a-capacity-diagnostic/capacity-b55-final-summary.json').read_bytes())
capacity_task = json.loads((ROOT / 'a-capacity-diagnostic/capacity-b55-final-task.json').read_bytes())
assert capacity_task['status'] == 'succeeded' and capacity_task['exit_code'] == 0
assert capacity['diagnostic_passed'] and capacity['exit_code'] == 0 and not capacity['errors']
assert capacity['raw_three_files_bytes'] == 485251971
assert capacity['canonical_audit_credit'] is False and capacity['independent_replay_performed'] is False

selection = json.loads((ROOT / 'receipt-selection-b55-final-summary.json').read_bytes())
selection_task = json.loads((ROOT / 'receipt-selection-b55-final-task.json').read_bytes())
assert selection_task['exit_code'] == selection['wrapper_exit_code'] == 125
assert selection['selection_passed'] is False and selection['zero321_exit_code'] == 0
assert all(selection['checks'].values())
selection_error_objects = [json.loads(line) for line in
    (ROOT / 'receipt-selection-b55-error-retrieval.log').read_text().splitlines()]
selection_error = next(v['data'] for v in selection_error_objects if v.get('file', '').endswith('errors.json.gz'))
assert len(selection_error) == 1
assert selection_error[0]['error'] == 'Duplicate owned declaration names across selected modules'
owned = json.loads((ROOT / 'owned-eleven-b55-final-summary.json').read_bytes())
owned_task = json.loads((ROOT / 'owned-eleven-b55-final-task.json').read_bytes())
assert owned_task['exit_code'] == owned['wrapper_exit_code'] == owned['original_runner_exit_code'] == 0
assert owned['canonical_owned_eleven_passed'] and owned['original_summary']['accepted'] == 11
assert len(owned['postchecks']) == 17 and all(owned['postchecks'].values()) and not owned['postcheck_errors']
assert sum(v['declarations'] for v in owned['original_summary']['modules'].values()) == 1041
b = json.loads((ROOT / 'finite-b-b55-final-summary.json').read_bytes())
b_task = json.loads((ROOT / 'finite-b-b55-final-task.json').read_bytes())
assert b_task['exit_code'] == b['runner_exit_code'] == b['wrapper_exit_code'] == 1
assert b['B_record']['seconds'] == 4.312 and not b['finite_B_compile_passed']
assert len(b['postchecks']) == 9 and all(b['postchecks'].values()) and not b['postcheck_errors']

latest_path = ROOT / 'canonical-a-publication-observed-tasks.json'
latest = json.loads(latest_path.read_bytes())
state = {
    'as_of_utc': latest['as_of_utc'], 'publication_parent': PARENT,
    'source_pin': SOURCE, 'actual_P2_pin': SOURCE, 'production_source_changes': [],
    'original_strict321': {'complete': True, 'task_id': 'caeb84c54d744748a036826b55c6126c',
        'successful': 321, 'reused': 317, 'fresh': 4, 'all_seven_postchecks_passed': True},
    'canonical_A_compile': {'task': a_task, 'complete': True, 'result': a,
        'complete_stdout_bytes': len(a_raw), 'complete_stdout_sha256': sha(a_raw),
        'independent_replay_complete': False, 'canonical_owned_audit_complete': False,
        'canonical_shape_check_complete': False},
    'capacity_diagnostic': {'task': capacity_task, 'result': capacity,
        'raw_three_files_bytes': 485251971, 'required_reserve_bytes': 33554432,
        'raw_three_files_plus_reserve_bytes': 518806403,
        'additional_wrapper_and_other_artifacts_not_in_that_sum': True,
        'original_runner_main_called': False, 'independent_replay_credit': False,
        'canonical_owned_audit_credit': False},
    'first_current_full324_receipt_selection': {'task': selection_task, 'result': selection,
        'current_accepted_count_unknown': True, 'error_details': selection_error,
        'all_protected_inputs_unchanged': True, 'compile_failure': False},
    'eleven_changed_module_canonical_owned_audit': {'task': owned_task, 'result': owned,
        'complete': True, 'owned_declarations': 1041, 'all_fresh_original_audits': True},
    'canonical_B_original_compile_attempt': {'task': b_task, 'result': b,
        'status': 'failed', 'failure': 'original rfl did not establish cachedHistoricalEndpointCheck = true',
        'not_a_timeout_or_OOM': True, 'original_322_prerequisites_remain_valid': True},
    'complete_retrieved_evidence_archive': archive_desc,
    'observed_remaining_tasks': latest,
    'canonical_B_compile_complete': False, 'canonical_W_compile_complete': False,
    'full324_canonical_owned_audit_complete': False, 'final_original_export_complete': False,
    'diagnostic_metadata_release_performed_at_this_checkpoint': False,
    'native_sources_objects_actual_audit_logs_preserved': True,
    'P2_4_complete': False, 'P2_complete': False, 'main_theorem_complete': False,
    'claim_6_809': False,
}
state_raw = (json.dumps(state, ensure_ascii=False, indent=2) + '\n').encode()
(OUT / 'state.json').write_bytes(state_raw)
add(PREFIX + '/p24-canonical-a-b55-checkpoint-20261126.json', state_raw,
    OUT / 'state.json', 'bounded current A compile acceptance and distinct capacity-only evidence')

block = f'''# Current checkpoint: canonical A compile PASS at b55

As of **{latest['as_of_utc']}**, the canonical P2 source pin remains `{SOURCE}`.
This publication changes evidence and diagnostic scripts only. The original strict321
result remains 321/321 successful with all seven postchecks passed.

Canonical A task `b969b7262ac5492587102cbd5b969e38` completed with exit 0:
102/102 successful, 101 reused and one fresh A compile. A itself took 2368.758 seconds,
the original driver reported 2418.302 seconds, and the outer task took 2558.517099 seconds.
All ten postchecks passed, including original A102 and prerequisite321 compilation bindings,
all 324 source/order bindings, unchanged non-A records/objects and qualified native inputs.
The complete 542,967-byte task log is retained without truncation. It records 2,048 checked
blocks, 131,072 computed nodes and query index 163,840. This is current-pin compilation
credit; independent replay, canonical complete-owned audit and canonical block-shape
inspection remain separate gates.

Capacity-only task `52c6614aa398474dabadd5475c4da443` also finished successfully. The
original template and original parser measured **485,251,971 bytes** for the three complete
canonical A audit files in their original formats. With the existing 32 MiB reserve, at least
**518,806,403 free bytes**, plus wrapper and other output overhead, are required. Its complete
diagnostic stdout was streamed to lossless gzip; this run did not call the original audit
runner main or perform independent replay, and it grants no canonical audit acceptance.

The first current full324 receipt-selection wrapper, task
`307f0fbb8e854c058399913d9133c9d2`, exited 125 before producing a selected partition.
Its original zero321 gate and all protected-input/final-snapshot checks passed. The exact
exception is `Duplicate owned declaration names across selected modules`, from the frozen
selector helper's duplicate-name guard. Its full traceback is retained. No current accepted
count is inferred from this failed selection. The unchanged helper is being used to identify
the exact overlapping receipt inventories; this does not revoke compilation.

The eleven repaired modules' original audit, task `30a5a171e3fe49e0be8d45c0f2fd4fb3`,
passed with 11/11 accepted and 1,041 complete owned declarations. All eleven audits were
fresh, and all seventeen postchecks passed. The original runner took 378.881909 seconds;
the outer task took 548.644542 seconds. Its canonical complete logs, declarations and types
remain at the original attempt paths. A 12-member lossless evidence archive also retains
the exact original A module log/record and complete capacity/eleven-audit metadata.

B's original attempt `e8a3e965a5dd4185b15e8cca81de00b6` then failed at its unchanged
`rfl` proof after 4.312 seconds. Its original zero322 prerequisite gate had passed; the B103
driver reported 102 reused modules and one failed B module. All nine failure postchecks
passed, including unchanged non-B objects and valid original322 bindings. This was not a
timeout or memory exhaustion. B requires further diagnosis before W can be compiled.
The earlier
queued B task `cc642fee3c9240ccb709674df8929281` was cancelled before it started solely to
place read-only error retrieval ahead of it; the identical B command was requeued as
`e8a3e965a5dd4185b15e8cca81de00b6`. That unstarted cancellation itself grants no compile result.

**P2.4 remains incomplete:** B, W, canonical A replay/full-owned/shape, current complete324
owned acceptance and the unchanged original full export still require their actual outcomes.
No native inputs, Lean sources, objects or actual audit logs have been removed. Diagnostic
metadata preservation has been submitted separately; no duplicate release has occurred at
this checkpoint. No full-P2, main-theorem
or 6.809 claim is made. Earlier checkpoints below retain their own historical timestamps.

---

'''
for name in ['p24-memory-and-audit-checkpoint-20261126.md', 'p24-source-node-blocks-promotion-20261126.md']:
    raw = block.encode() + (ROOT / 'joint321-publication' / name).read_bytes()
    (OUT / name).write_bytes(raw)
    add(PREFIX + '/' + name, raw, OUT / name, 'latest bounded checkpoint with earlier history retained')

assert all(e['path'].startswith(('docs/', 'diagnostics/')) for e in elements)
manifest = {'parent_sha': PARENT, 'base_tree_sha': BASE_TREE,
    'source_pin': SOURCE, 'production_files_changed': [], 'files': rows,
    'files_count_without_manifest_itself': len(rows), 'P2_4_complete': False}
raw = (json.dumps(manifest, ensure_ascii=False, indent=2) + '\n').encode()
(OUT / 'publication-files.json').write_bytes(raw)
add(PREFIX + '/p24-canonical-a-b55-publication-files-20261126.json', raw,
    OUT / 'publication-files.json', 'exact publication manifest excluding itself')
(OUT / 'tree.json').write_bytes((json.dumps(elements, ensure_ascii=False, separators=(',', ':')) + '\n').encode())
print(json.dumps({'entries': len(elements), 'tree_bytes': (OUT / 'tree.json').stat().st_size,
    'manifest_sha256': sha(raw), 'state_sha256': sha(state_raw), 'production_files_changed': []}))
