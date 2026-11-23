"""Independent read-only metadata review; never import or call the validator."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json

ROOT = Path(__file__).resolve().parent
BATCH = Path('/workspace/blue-member-repair-batch66')
MEMBER = Path('/workspace/blue-member-build')
OLD = BATCH / 'run_validation.revision4_p6_original_single_state_collector.py'
NEW = BATCH / 'run_validation.py'
CORRECTION = BATCH / 'MIXED_RUNTIME_COLLECTOR_CORRECTION.json'
MEMBER_STATE = Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
P6_STATE = Path('/workspace/blue-build-tools/runtime-evidence/state.json')
THREE = ['ImbalancedChen.P2OriginalSelectedBoxGateMargin',
         'ImbalancedChen.P5OriginalCommonBetaVariableCutoffReserve',
         'ImbalancedChen.Part5RenewalTablePrimitive']
RETRY = 'ImbalancedChen.P4AOriginalSixthLaterSemantics'

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def ident(path):
    raw = Path(path).read_bytes()
    return dict(path=str(path), bytes=len(raw), sha256=sha(raw))

def save(path, obj):
    with path.open('x') as stream:
        stream.write(json.dumps(obj, ensure_ascii=False, indent=2) + '\n')
    return ident(path)

def receipt_state(receipt):
    argv = receipt['argv']
    assert argv.count('--state') == 1
    return Path(argv[argv.index('--state') + 1])

old_bytes, new_bytes = OLD.read_bytes(), NEW.read_bytes()
correction_bytes = CORRECTION.read_bytes()
correction = json.loads(correction_bytes)
assert sha(old_bytes) == correction['old_driver_sha256']
assert sha(new_bytes) == correction['future_validator_sha256']
old, new = old_bytes.decode(), new_bytes.decode()
begin = 'state=json.loads(STATE.read_text());targets='
end = 'owned_counts={m:sum('
old_prefix, old_rest = old.split(begin, 1)
new_prefix, new_rest = new.split(begin, 1)
old_block, old_suffix = old_rest.split(end, 1)
new_block, new_suffix = new_rest.split(end, 1)
assert old_prefix == new_prefix
assert old_suffix == new_suffix
assert "STATE=Path('/workspace/blue-build-tools/runtime-evidence/state.json')" in new_prefix
assert "if recpath.exists():\n  x=json.loads(recpath.read_text());assert x['exit_code']==0,('previous_failure',name);return x" in new_prefix
assert "if pending:\n write(R/'PENDING_REPAIRS.json',pending);print('PENDING_REPAIRS',pending,flush=True);raise SystemExit(1)" in new_prefix
assert "target_states[target]==actual_state_path" in new_block
assert "'legacy_state_fields_scope':'CURRENT_RETRY_AND_AUDIT_ONLY'" in new_block
assert "'per_target_authentic_runtime_state'" in new_block and "'runtime_states'" in new_block

# Inspect only the new collector block's AST. Its only write call targets batch
# metadata ACTUAL_RUNTIME_COMMANDS.json; states and journals are read_text only.
collector_ast = ast.parse(begin + new_block)
write_calls = [n for n in ast.walk(collector_ast) if isinstance(n, ast.Call)
               and isinstance(n.func, ast.Name) and n.func.id == 'write']
assert len(write_calls) == 1
assert ast.unparse(write_calls[0].args[0]) == "R / 'ACTUAL_RUNTIME_COMMANDS.json'"
assert not any(isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
               and n.func.attr in ['write_text', 'write_bytes', 'open', 'unlink', 'rename']
               for n in ast.walk(collector_ast))
replace_calls = [n for n in ast.walk(collector_ast) if isinstance(n, ast.Call)
                 and isinstance(n.func, ast.Attribute) and n.func.attr == 'replace']
assert all(isinstance(n.func.value, ast.Name) and n.func.value.id in {'m', 'mod'}
           for n in replace_calls), 'Only the string module-name replacement is allowed'

state_before = {p: p.read_bytes() for p in [MEMBER_STATE, P6_STATE]}
states = {p: json.loads(raw) for p, raw in state_before.items()}
journals = {}
for state_path, state in states.items():
    path = Path(state['log'])
    raw = path.read_bytes()
    stat = path.stat()
    complete = raw[:raw.rfind(b'\n') + 1]
    events = [json.loads(line) for line in complete.splitlines()]
    journals[state_path] = dict(path=path, raw=raw, events=events, dev=stat.st_dev, ino=stat.st_ino,
        parsed_complete_lines=len(events), incomplete_tail_bytes=len(raw)-len(complete))

expected_path = BATCH / 'EXPECTED_SOURCES.json'
expected_bytes = expected_path.read_bytes()
expected = json.loads(expected_bytes)
assert set(expected) == set(THREE + [RETRY])
success = []
target_states = {}
receipt_files = []
for mod in THREE:
    normal_path = BATCH / (mod.split('.')[-1] + '-normal-command.json')
    kernel_path = BATCH / (mod.split('.')[-1] + '-kernel-command.json')
    normal, kernel = json.loads(normal_path.read_bytes()), json.loads(kernel_path.read_bytes())
    assert normal['exit_code'] == kernel['exit_code'] == 0
    assert receipt_state(normal) == receipt_state(kernel) == MEMBER_STATE
    assert normal['argv'][-3:] == ['lake', 'build', mod + ':olean']
    assert kernel['argv'][-4:] == ['lake', 'env', 'leanchecker', '--verbose', mod][-4:]
    for record in [normal, kernel]:
        log = BATCH / record['log']
        assert ident(log)['sha256'] == record['log_sha256']
        receipt_files.append(ident(log))
    receipt_files.extend([ident(normal_path), ident(kernel_path)])
    target = str(MEMBER / (mod.replace('.', '/') + '.lean'))
    target_states[target] = MEMBER_STATE
    success.append(dict(module=mod, normal=ident(normal_path), kernel=ident(kernel_path),
                        authentic_state=str(MEMBER_STATE), success_commands_not_reexecuted=True))

lane_path = BATCH / 'VALIDATION_LANE_REVISION5_P6.json'
lane = json.loads(lane_path.read_bytes())
assert lane['state'] == str(P6_STATE)
assert lane['state_sha256'] == sha(state_before[P6_STATE])
retry_receipt_path = BATCH / (RETRY.split('.')[-1] + '-normal-command.json')
retry_source = 'CURRENT_DRIVER_P6_STATE_AND_ORIGINAL_REVISION5_LANE_RECEIPT_NOT_A_SUCCESS_CLAIM'
if retry_receipt_path.exists():
    retry_receipt = json.loads(retry_receipt_path.read_bytes())
    assert receipt_state(retry_receipt) == P6_STATE
    retry_source = 'EXISTING_CURRENT_NORMAL_COMMAND_RECEIPT'
target_states[str(MEMBER / (RETRY.replace('.', '/') + '.lean'))] = P6_STATE
selected, old_single_state_selected = {}, {}
for state_path, snapshot in journals.items():
    for line_number, event in enumerate(snapshot['events'], 1):
        if event.get('tool') != 'lean':
            continue
        for target, required_state in target_states.items():
            if target not in event.get('command', []):
                continue
            if state_path == P6_STATE:
                old_single_state_selected[target] = event
            if required_state == state_path:
                selected[target] = dict(state=str(state_path), journal=str(snapshot['path']),
                    journal_line=line_number, event=event)
assert set(selected) == set(target_states)
assert set(old_single_state_selected) == {str(MEMBER / (RETRY.replace('.', '/') + '.lean'))}
for target, item in selected.items():
    command = item['event']['command']
    assert all(flag in command for flag in ['-t0', '-j2', '-M12288', 'maxRecDepth=100000', 'maxHeartbeats=4000000'])
    assert item['event']['cwd'] == str(MEMBER)
    assert command[0] == str(Path(states[Path(item['state'])]['shadow']) / 'bin/lean-runtime')

audit_path = BATCH / 'all-public-types-axioms-command.json'
audit_status = dict(actual_command_receipt_present=audit_path.exists(),
    configured_state=str(P6_STATE), unexecuted_by_review=True,
    future_collector_uses_actual_audit_receipt_state=True)
if audit_path.exists():
    audit_receipt = json.loads(audit_path.read_bytes())
    assert receipt_state(audit_receipt) == P6_STATE
    audit_status.update(receipt=ident(audit_path), recorded_exit=audit_receipt.get('exit_code'))

preservation = []
for path, initial in state_before.items():
    assert path.read_bytes() == initial
for state_path, item in journals.items():
    path, initial = item['path'], item['raw']
    stat = path.stat()
    with path.open('rb') as stream:
        preserved = stream.read(len(initial)) == initial
    assert stat.st_dev == item['dev'] and stat.st_ino == item['ino'] and preserved
    preservation.append(dict(state=str(state_path), state_sha256=sha(state_before[state_path]),
        journal=str(path), initial_prefix_bytes=len(initial), initial_prefix_sha256=sha(initial),
        same_device_inode=True, initial_prefix_byte_exact_at_end=True,
        final_size=stat.st_size, appended_bytes_observed=stat.st_size-len(initial),
        incomplete_tail_bytes_at_initial_snapshot=item['incomplete_tail_bytes']))
assert OLD.read_bytes() == old_bytes and NEW.read_bytes() == new_bytes
assert CORRECTION.read_bytes() == correction_bytes and expected_path.read_bytes() == expected_bytes

report = dict(schema='independent_batch66_mixed_original_runtime_collector_review_v1',
    reviewed_utc=datetime.now(timezone.utc).isoformat(), reviewer='/root/manuscript_inventory/stored_family',
    outcome='PASS_METADATA_ONLY_STATIC_AND_ORIGINAL_JOURNAL_EXTRACTION', findings=[],
    current_driver=ident(NEW), saved_old_driver=ident(OLD), correction_receipt=ident(CORRECTION),
    expected_sources_metadata=ident(expected_path), current_p6_lane=ident(lane_path),
    normal_kernel_audit_commands_and_success_skip_logic_raw_byte_identical=True,
    raw_unchanged_prefix_sha256=sha(old_prefix.encode()), raw_unchanged_suffix_sha256=sha(old_suffix.encode()),
    changes_limited_to_final_runtime_event_collection_and_runtime_metadata_labels=True,
    collector_state_and_journal_access_read_only=True,
    collector_only_metadata_write='batch66/ACTUAL_RUNTIME_COMMANDS.json',
    successful_original_member_receipts=success, selected_authentic_original_source_events=selected,
    independent_metadata_fixture=dict(source_targets_checked=4, three_old_successes_from_member_original_journal=True,
        current_retry_event_from_p6_original_journal=True,
        single_p6_only_collection_missing_original_member_successes=len(target_states)-len(old_single_state_selected),
        no_synthetic_success_receipt_or_event_used=True, retry_provenance=retry_source),
    current_retry_and_audit_scope=audit_status,
    explicit_mixed_state_label='legacy_state_fields_scope=CURRENT_RETRY_AND_AUDIT_ONLY; per-target state and runtime_states prevent a whole-group single-state claim',
    state_and_journal_preservation=preservation,
    append_boundary='The journals are live append-only inputs. This review confirms unchanged original prefixes and same file identities during its read-only interval; legitimate runtime appends are not represented as journal mutation by the review.',
    receipt_files_rehashed=receipt_files,
    driver_imported_or_called=False, successful_commands_repeated=0,
    Lean_Lake_kernel_stock_invocations=0, live_source_object_trace_guard_state_or_journal_writes=0,
    current_processes_touched=False, current_batch66_fullchain_success_claim=False)
review = save(ROOT / 'INDEPENDENT_REVIEW.json', report)
manifest = save(ROOT / 'NEW_FILES_MANIFEST.json', dict(schema='independent_mixed_collector_review_files_v1',
    files=[ident(Path(__file__)), review], self_excluded=True))
print(json.dumps(dict(review=review, new_files=manifest), indent=2))
