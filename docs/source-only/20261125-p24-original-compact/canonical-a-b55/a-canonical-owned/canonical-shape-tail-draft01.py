# Canonical A shape inspection only. No proof regeneration, independent replay,
# original audit CLI, or canonical audit receipt is created by this wrapper.
from run_winner9_private_audit import parse_audit, require

MINIMUM_FREE_BYTES = 32 * 1024 * 1024
METADATA_ALLOWANCE = 2 * 1024 * 1024
CAPTURE_DRAIN_ALLOWANCE = 4 * 1024 * 1024
CHUNK_BYTES = 65536
out = root / ".lake/p24-canonical-A-block-shape/b55-attempt-001"
assert not out.exists() and not out.is_symlink(), "Preserve previous shape evidence"
assert out.resolve().is_relative_to(root.resolve())
capacity_directory = root / ".lake/p24-owned-capacity/b55-A-attempt-001"
capacity_receipt_path = capacity_directory / "capacity-diagnostic.json"
capacity_receipt_sha256 = "47734ae76baf0a59f4f381e491ff4fc2ed62669a2fd81131af24635bb94d20a9"
shape_source_sha256 = "b54a2c1ae01c1ebfbcb83bb63a9e09f7275ef818eb368e683d615deca1196734"
executed_original_shape_sha256 = "c190906df505fbe101f0aca84f46a7ba3252ad75b7ab6bb07ffa2ae3fb950d48"
shape_core_sha256 = "a8db2e02200ea9d21063fbb8e451feebedcb851be3ae53ff7f58c61a313061d3"

# EXACT_CAPACITY_CAPTURE_HELPERS_INSERTION_POINT


def bound_capacity_input(binding, basename):
    path = Path(binding["path"])
    assert path == capacity_directory / basename
    assert path.is_file() and not path.is_symlink()
    assert path.resolve().is_relative_to(capacity_directory.resolve())
    assert path.stat().st_size == binding["bytes"] and digest(path) == binding["sha256"]
    return path


registry_before = {"bytes": registry.stat().st_size, "sha256": digest(registry)}
records = json.loads(registry.read_text())
full_before = snapshot(root, lib, full_nodes, toolchain, external)
assert full_before["external_snapshot"] == native_before
verify_compilation(records, prereq_nodes, full_before)
verify_compilation(records, a_nodes, full_before)
assert digest(registry) == registry_before["sha256"]
original_audit_before = audit_directory_fingerprint()
assert digest(capacity_receipt_path) == capacity_receipt_sha256
measured = json.loads(capacity_receipt_path.read_text())
assert measured["diagnostic_passed"] is True and measured["wrapper_exit_code"] == 0
assert measured["source_pin"] == pin and measured["target"] == A
assert measured["target_project_scope"] == 102 and measured["full_source_scope"] == 324
assert measured["ordered_fingerprint"] == ordered_expected
assert measured["pinned_file_sha256"] == expected and measured["runtime_sha256"] == runtime_expected
assert measured["native_binding"] == native_before
assert measured["postchecks"] and all(value is True for value in measured["postchecks"].values())
assert not measured["errors"] and measured["registry_before"] == measured["registry_after"]
assert measured["original_runner_main_called"] is False
assert measured["independent_replay_performed"] is False and measured["canonical_audit_credit"] is False
capacity_full_path = bound_capacity_input(measured["full324_before"], "full324-before-snapshot.json")
capacity_full = json.loads(capacity_full_path.read_text())
assert {name: capacity_full["project"][name] for name in a_nodes} == \
    {name: full_before["project"][name] for name in a_nodes}
for key in ("toolchain", "lean_binary_sha256", "leanchecker_sha256", "template_sha256", "driver_sha256", "external_snapshot"):
    assert capacity_full[key] == full_before[key]
capacity_capture = measured["capture"]
assert capacity_capture["complete_successful_template_stdout"] is True
assert capacity_capture["lean_exit_code"] == 0 and capacity_capture["read_to_eof"] is True
assert capacity_capture["stopped_for_reserve"] is False and not capacity_capture["errors"]
capacity_gzip = bound_capacity_input({"path": capacity_capture["gzip_path"],
    "bytes": capacity_capture["gzip_bytes"], "sha256": capacity_capture["gzip_sha256"]}, "audit.stdout.log.gz")
assert capacity_capture["gzip_bytes"] == 10708984
assert capacity_capture["gzip_sha256"] == "92489930738bdb59e07ff98dfb795960c324949fd54550c01c7e739382faa780"
assert fingerprint_gzip_payload(capacity_gzip) == {
    "bytes": capacity_capture["stdout_bytes"], "sha256": capacity_capture["stdout_sha256"]}

assert hashlib.sha256(SHAPE_SOURCE.encode()).hexdigest() == shape_source_sha256
shape_core = SHAPE_SOURCE[SHAPE_SOURCE.index("  unless sourceNames.size == 1"):]
assert len(shape_core.encode()) == 6652
assert hashlib.sha256(shape_core.encode()).hexdigest() == shape_core_sha256
free_before = need_free(12 * 1024 * 1024 + METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE)
out.mkdir(parents=True, exist_ok=False)
source_binding = write_derived("InspectBlocks.lean", SHAPE_SOURCE.encode())
before_binding = write_derived("full324-before-snapshot.json", encoded_json(full_before))
audit_binding = write_derived("original-A-audit-directory-before.json", encoded_json(original_audit_before))
environment = dict(os.environ)
environment["LEAN_PATH"] = str(lib) + ":" + environment.get("LEAN_PATH", "")
environment = external.environment(environment)
command = [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
    "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", str((out / "InspectBlocks.lean").relative_to(root))]
initial = {
    "schema": 1, "purpose": "Canonical A exact block-shape inspection, separately from original replay/full-owned audit",
    "source_pin": pin, "target": A, "target_project_scope": 102, "prerequisite_symbolic_scope": 321,
    "full_source_scope": 324, "ordered_fingerprint": ordered_expected,
    "pinned_file_sha256": expected, "runtime_sha256": runtime_expected, "native_binding": native_before,
    "registry_before": registry_before, "full324_before": before_binding,
    "original_A_audit_before": audit_binding, "inspector_source": source_binding,
    "executed_original_inspector_sha256": executed_original_shape_sha256,
    "unchanged_executed_core_bytes": 6652, "unchanged_executed_core_sha256": shape_core_sha256,
    "capacity_receipt": {"path": str(capacity_receipt_path), "bytes": capacity_receipt_path.stat().st_size,
        "sha256": capacity_receipt_sha256},
    "capacity_full_owned_link_is_diagnostic_only": True,
    "command": command, "lean_path": environment.get("LEAN_PATH", ""),
    "minimum_free_reserve_bytes": MINIMUM_FREE_BYTES, "free_bytes_before": free_before,
    "outer_timeout_seconds": 3600, "job_memory_mb": 13107, "cpu_threads": 1,
    "lean_memory_mb": 11264, "lean_threads": 1,
    "original_runner_main_called": False, "independent_replay_performed": False,
    "proof_generator_run": False, "canonical_audit_credit": False, "full324_credit": False,
    "original_audit_files_deleted": False,
}
write_derived("shape-input.json", encoded_json(initial))
print("P24_CANONICAL_A_SHAPE_BEGIN " + json.dumps(initial, sort_keys=True), flush=True)

capture = None
shape_summary = None
shape_join = None
shape_summary_binding = None
shape_join_binding = None
shape_checks_passed = False
full_after = None
errors = []
postchecks = {}
gzip_path = out / "blocks.stdout.log.gz"
try:
    capture = capture_complete_stdout(command, environment, gzip_path)
    assert fingerprint_gzip_payload(gzip_path) == {
        "bytes": capture["stdout_bytes"], "sha256": capture["stdout_sha256"]}
    capture["gzip_roundtrip_verified"] = True
    assert capture["complete_successful_template_stdout"] is True, "Shape child failed or output was incomplete"
    with gzip.open(gzip_path, "rt") as stream:
        inspect_raw = stream.read()
    records_with_prefix = lambda text, prefix: [json.loads(line[len(prefix):])
        for line in text.splitlines() if line.startswith(prefix)]
    target = A
    blocks = records_with_prefix(inspect_raw, "P24_Q80_BLOCK ")
    summaries = records_with_prefix(inspect_raw, "P24_Q80_BLOCK_SUMMARY ")
    require(len(summaries) == 1 and summaries[0].get("module") == target, "Missing block summary")
    require(len(blocks) == 2048 and summaries[0].get("owned_block_count") == 2048 and
            summaries[0].get("shape_checks_passed") is True, "Incorrect block inventory/shape")
    require(summaries[0].get("public_entry_checks_passed") is True and
            summaries[0].get("node_alias_directly_equals_historic_node") is True and
            summaries[0].get("total_fact_count") == 131072,
            "Incorrect public entry/carrier/total fact count")
    require(sorted(summaries[0].get("indices", [])) == list(range(32769, 163841)),
            "Q80 block indices do not cover the exact original first-131072 prefix")
    require(all(block.get("shape_checks_passed") is True and
                block.get("balanced_and_depth") == 6 and block.get("fact_count") == 64
                for block in blocks), "Q80 block depth/fact count differs")
    # Preserve the executed P3 cross-check against complete original-template
    # owned records. Here those records are the already-bound capacity diagnostic;
    # this link does not create a canonical audit/replay receipt.
    parsed = parse_audit(CompleteGzipAuditText(capacity_gzip), A, set(a_nodes))
    assert parsed["declaration_count"] == measured["original_format_sizes"]["declaration_count"]
    assert parsed["axiom_counts"] == measured["original_format_sizes"]["axiom_counts"]
    declarations = parsed["declarations"]
    by_name = {row["name"]:row for row in declarations}
    for block in blocks:
        require(block["name"] in by_name, "Inspected block is absent from original owned audit")
        block["printed_type_utf8_bytes"] = len(by_name[block["name"]]["type"].encode())
        block["axioms"] = by_name[block["name"]]["axioms"]
    shape_summary = summaries[0]
    # The full per-node normal forms and full global index list remain in the
    # lossless stdout gzip. Avoid a second 32+ MB plaintext JSON copy of them.
    shape_join = [{"name": block["name"], "printed_type_utf8_bytes": block["printed_type_utf8_bytes"],
        "axioms": block["axioms"]} for block in blocks]
    summary_raw = encoded_json(shape_summary)
    summary_gzip = gzip.compress(summary_raw, compresslevel=9, mtime=0)
    assert gzip.decompress(summary_gzip) == summary_raw
    shape_summary_binding = write_derived("complete-block-summary.json.gz", summary_gzip)
    join_raw = encoded_json(shape_join)
    join_gzip = gzip.compress(join_raw, compresslevel=9, mtime=0)
    assert gzip.decompress(join_gzip) == join_raw
    shape_join_binding = write_derived("complete-block-owned-link.json.gz", join_gzip)
    shape_checks_passed = True
    del parsed, declarations, by_name, blocks, inspect_raw, summary_raw, join_raw
except Exception as error:
    errors.append({"stage": "shape_capture_parse_or_exact_owned_link", "error": type(error).__name__ + ": " + str(error)})


def postcheck(name, action):
    try:
        action()
        postchecks[name] = True
    except Exception as error:
        postchecks[name] = False
        errors.append({"check": name, "error": type(error).__name__ + ": " + str(error)})


def check_runtime_after():
    assert {name: digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected


def check_all_inputs_after():
    global full_after
    current_nodes = project_nodes(root, W)
    assert list(current_nodes) == full
    mark_project_nodes(current_nodes, set(external.modules))
    full_after = snapshot(root, lib, current_nodes, toolchain, external)
    assert full_after == full_before
    assert {"bytes": registry.stat().st_size, "sha256": digest(registry)} == registry_before
    current_records = json.loads(registry.read_text())
    verify_compilation(current_records, prereq_nodes, full_after)
    verify_compilation(current_records, a_nodes, full_after)


def check_original_audits_after():
    assert audit_directory_fingerprint() == original_audit_before


def check_derived_inputs_after():
    assert digest(out / "InspectBlocks.lean") == shape_source_sha256
    assert digest(capacity_receipt_path) == capacity_receipt_sha256
    assert digest(capacity_gzip) == capacity_capture["gzip_sha256"]
    if capture is not None:
        assert digest(gzip_path) == capture["gzip_sha256"]


postcheck("pinned_sources_and_original_tools", check_source)
postcheck("runtime_and_original_native_snapshot_bytes", check_runtime_after)
postcheck("full324_inputs_registry_native_and_321_plus_A102_bindings", check_all_inputs_after)
postcheck("original_canonical_A_audit_files_unchanged", check_original_audits_after)
postcheck("inspector_capacity_reference_and_complete_stdout_unchanged", check_derived_inputs_after)
postcheck("minimum_32MiB_free_reserve", need_free)
if full_after is not None:
    write_derived("full324-after-snapshot.json", encoded_json(full_after))
success = shape_checks_passed and not errors and all(postchecks.values())
exit_code = 0 if success else 125
if capture is not None and isinstance(capture.get("lean_exit_code"), int) and capture["lean_exit_code"] != 0:
    exit_code = capture["lean_exit_code"] if capture["lean_exit_code"] > 0 else 1
result = dict(initial, canonical_A_shape_checks_passed=success,
    shape_capture=capture, complete_block_summary=shape_summary_binding,
    complete_block_owned_link=shape_join_binding,
    total_block_printed_type_utf8_bytes=None if shape_join is None else sum(row["printed_type_utf8_bytes"] for row in shape_join),
    block_count=2048 if shape_checks_passed else None, fact_count=131072 if shape_checks_passed else None,
    postchecks=postchecks, errors=errors, wrapper_exit_code=exit_code,
    registry_after={"bytes": registry.stat().st_size, "sha256": digest(registry)},
    free_bytes_after=available_bytes(), canonical_audit_credit=False,
    independent_replay_performed=False, original_runner_main_called=False, full324_credit=False)
result_binding = write_derived("shape-diagnostic.json", encoded_json(result))
directory_fd = os.open(out, os.O_RDONLY | os.O_DIRECTORY)
try:
    os.fsync(directory_fd)
finally:
    os.close(directory_fd)
print("P24_CANONICAL_A_SHAPE_DONE " + json.dumps({
    "result": result_binding, "canonical_A_shape_checks_passed": success, "exit_code": exit_code,
    "gzip": None if capture is None else {key: capture[key] for key in ("gzip_path", "gzip_bytes", "gzip_sha256")},
    "block_count": result["block_count"], "fact_count": result["fact_count"],
    "canonical_audit_credit": False, "independent_replay_performed": False,
    "full324_credit": False, "errors": errors}, sort_keys=True), flush=True)
raise SystemExit(exit_code)
