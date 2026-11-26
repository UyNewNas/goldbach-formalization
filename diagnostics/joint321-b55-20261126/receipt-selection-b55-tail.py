# This tail is appended to the unchanged b55 A wrapper's source/runtime/scope setup.
# No A gate, audit runner, final exporter main, or package operation is invoked.
out = Path("/workspace/p24-current-audit-receipt-selection-b55-20261126/attempt-001")
assert not out.exists(), "Preserve every earlier selection attempt"
out.mkdir(parents=True, exist_ok=False)
selection_helper_sha = "0b2798884008c0de0827c8668e828c2bcf236f2e81ec5a2a1eadce9e1769d6be"
selection_block_sha = "6f8d699df12e76a747efe2893ef5a0ff76654357dedacc15bf0ec95f13d52b53"
helper_path = out / "select_original_audit_receipts.py"
helper_raw = base64.b64decode(SELECTION_HELPER_BASE64, validate=True)
assert hashlib.sha256(helper_raw).hexdigest() == selection_helper_sha
helper_path.write_bytes(helper_raw)

def file_info(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest(path)}

def write_json(name, value):
    path = out / name
    with path.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n")
    return file_info(path)

def write_json_gzip(name, value):
    # Preserve the complete serialized JSON; no loose large JSON or registry copy.
    raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode()
    path = out / name
    with path.open("xb") as stream:
        with gzip.GzipFile(filename="", mode="wb", fileobj=stream, compresslevel=9, mtime=0) as compressed:
            compressed.write(raw)
    observed = hashlib.sha256()
    observed_bytes = 0
    with gzip.open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            observed.update(chunk)
            observed_bytes += len(chunk)
    raw_sha = hashlib.sha256(raw).hexdigest()
    assert observed_bytes == len(raw) and observed.hexdigest() == raw_sha
    return {"gzip": file_info(path), "uncompressed_json_bytes": len(raw),
            "uncompressed_json_sha256": raw_sha, "lossless_roundtrip_verified": True}

checks, errors = {}, []
artifacts = {}
before_frozen = None
registry_raw_before = None
records_before = None
pre_rc = None
pre_summary = None
pre_seconds = None
selection = None
selection_started = False

def perform(name, action):
    try:
        action()
        checks[name] = True
    except Exception as error:
        checks[name] = False
        errors.append({"check": name, "type": type(error).__name__, "error": str(error),
                       "traceback": traceback.format_exc()})

def check_runtime_native():
    assert {name: digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected
    assert external.verify() == native_before

def get_current_snapshot():
    current = project_nodes(root, W)
    assert list(current) == full
    assert {name: digest(node["source"]) for name, node in current.items()} == sources_before
    mark_project_nodes(current, set(external.modules))
    return snapshot(root, lib, current, toolchain, external)

def check_complete_inputs():
    check_source()
    check_runtime_native()
    assert registry.read_bytes() == registry_raw_before, "Complete compilation registry changed"
    current = get_current_snapshot()
    assert current == before_frozen, "Full324 source/object/tool/native snapshot changed"
    verify_compilation(json.loads(registry_raw_before), prereq_nodes, current)
    assert digest(helper_path) == selection_helper_sha

def parse_original_summary(path):
    summaries = []
    required = {"roots", "successful_closure", "failed_or_blocked", "pending", "complete", "exit_code", "total"}
    with path.open("rb") as stream:
        for line in stream:
            try:
                value = json.loads(line)
            except (ValueError, UnicodeDecodeError):
                continue
            if isinstance(value, dict) and required <= value.keys():
                summaries.append(value)
    assert len(summaries) == 1, "Expected one complete original zero-budget summary"
    return summaries[0]

print("P24_CURRENT_RECEIPT_SELECTION_BEGIN " + json.dumps({
    "source_pin": pin, "scope": 324, "ordered_fingerprint": ordered_expected,
    "prerequisite_scope": 321, "selection_only": True,
    "output_directory": str(out), "audit_started": False, "final_export_started": False,
    "full324_credit": False}), flush=True)

try:
    registry_raw_before = registry.read_bytes()
    records_before = json.loads(registry_raw_before)
    # The unchanged original zero-budget checker writes canonical registry JSON.
    # Refuse first if that write would alter any existing record or byte.
    persisted = {name: (dict(row, exit_code=125, new_strict_compile=False)
                       if row.get("external_check", {}).get("status") == "PENDING_BATCH_POSTCHECK" else row)
                 for name, row in records_before.items()}
    assert (json.dumps(persisted, indent=2, sort_keys=True) + "\n").encode() == registry_raw_before, \
        "Original zero-budget registry persistence would change existing bytes"
    assert lib.is_dir() and (root / ".lake/p2-private/logs").is_dir()
    for name in prereq_nodes:
        assert records_before.get(name, {}).get("object") == str(lib / (name.replace(".", "/") + ".olean")), \
            "Original zero-budget reuse would rebind an object path: " + name
    baseline_lib = Path("/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001/.lake/build/lib/lean")
    assert baseline_lib.is_dir()
    for source in baseline_lib.rglob("*"):
        if source.is_file():
            assert (lib / source.relative_to(baseline_lib)).is_file(), \
                "Original zero-budget driver would copy a missing baseline file: " + str(source)
    check_runtime_native()
    before_frozen = get_current_snapshot()
    assert before_frozen["external_snapshot"] == native_before
    verify_compilation(records_before, prereq_nodes, before_frozen)
    checks["original321_valid_before_zero_gate"] = True
    artifacts["full324_before"] = write_json_gzip("full324-before.json.gz", before_frozen)
    artifacts["scope"] = write_json("scope.json", {
        "source_pin": pin, "full324_topological_order": full,
        "ordered_fingerprint": ordered_expected,
        "symbolic321_topological_order": [name for name in full if name in prereq_nodes],
        "finite_modules": [A, B, W]})
    artifacts["before_binding"] = write_json("before-binding.json", {
        "source_pin": pin, "registry": {"path": str(registry), "bytes": len(registry_raw_before),
            "sha256": hashlib.sha256(registry_raw_before).hexdigest()},
        "source_sha256": sources_before, "pinned_files": expected,
        "runtime": runtime_expected, "native": native_before,
        "selection_helper": file_info(helper_path), "full324_snapshot": artifacts["full324_before"]})

    command = common + ["--time-budget-seconds", "0", *roots]
    log_path = out / "zero321-original.log"
    started = time.monotonic()
    with log_path.open("xb") as log:
        child = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
    pre_rc = child.returncode
    pre_seconds = time.monotonic() - started
    artifacts["zero321_log"] = file_info(log_path)
    pre_summary = parse_original_summary(log_path)
    artifacts["zero321_result"] = write_json("zero321-result.json", {
        "command": command, "exit_code": pre_rc, "elapsed_seconds": pre_seconds,
        "original_summary": pre_summary, "log": artifacts["zero321_log"]})
    assert pre_summary["roots"] == roots and pre_summary["total"] == 321
    assert pre_summary["time_budget_seconds"] == 0 and pre_summary["exit_code"] == pre_rc
    assert pre_summary["complete"] == (pre_rc == 0)
    assert pre_summary["successful_closure"] + len(pre_summary["failed_or_blocked"]) + len(pre_summary["pending"]) == 321
    assert pre_rc == 0 and pre_summary["successful_closure"] == pre_summary["reused"] == 321
    assert not pre_summary["failed_or_blocked"] and not pre_summary["pending"]
    checks["original_zero321_all_reuse"] = True
    check_complete_inputs()
    checks["all_protected_inputs_unchanged_after_zero_gate"] = True

    spec = importlib.util.spec_from_file_location("p24_exact_original_receipt_selector", helper_path)
    assert spec is not None and spec.loader is not None
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    assert Path(helper.__file__).resolve() == helper_path.resolve()
    selection_started = True
    selection = helper.select_current(root, full)
    assert selection["selection_only"] is True and selection["final_original_export_still_required"] is True
    assert selection["original_exporter_sha256"] == expected["verification/part2/export_winner9_private_evidence.py"]
    assert selection["original_audit_driver_sha256"] == expected["verification/part2/run_winner9_private_audit.py"]
    assert selection["unchanged_selection_block_sha256"] == selection_block_sha
    assert selection["records_snapshot_sha256"] == hashlib.sha256(registry_raw_before).hexdigest()
    accepted = set(selection["accepted_modules"])
    unselected = set(selection["unselected_modules"])
    assert len(selection["unselected_modules"]) == len(unselected)
    assert accepted.isdisjoint(unselected) and accepted | unselected == set(full)
    assert selection["accepted_module_count"] == len(accepted)
    assert not selection["duplicate_owned_declarations"]
    artifacts["selection"] = write_json_gzip("full324-original-selection.json.gz", selection)
    checks["original_selector_complete_partition"] = True
except Exception as error:
    errors.append({"check": "original_prerequisite_or_selection", "type": type(error).__name__,
                   "error": str(error), "traceback": traceback.format_exc()})
finally:
    if registry_raw_before is not None and before_frozen is not None:
        perform("all_protected_inputs_unchanged_final", check_complete_inputs)
        def capture_after():
            artifacts["full324_after"] = write_json_gzip("full324-after.json.gz", get_current_snapshot())
            assert artifacts["full324_after"]["uncompressed_json_sha256"] == artifacts["full324_before"]["uncompressed_json_sha256"]
        perform("full324_after_snapshot_recorded_equal", capture_after)

passed = checks.get("original_selector_complete_partition") is True and not errors
exit_code = pre_rc if pre_rc is not None and pre_rc != 0 else (0 if passed else 125)
if errors:
    artifacts["errors"] = write_json_gzip("errors.json.gz", errors)
accepted_names = set(selection["accepted_modules"]) if selection is not None else set()
unselected_names = set(selection["unselected_modules"]) if selection is not None else set()
receipt = {
    "source_pin": pin, "purpose": "full324 original receipt selection for scheduling only",
    "selection_only": True, "selection_started": selection_started, "selection_passed": passed,
    "scope": 324, "ordered_fingerprint": ordered_expected,
    "prerequisite_scope": 321, "zero321_exit_code": pre_rc, "zero321_seconds": pre_seconds,
    "zero321_original_summary": pre_summary,
    "accepted_count": len(accepted_names) if selection is not None else None,
    "unselected_count": len(unselected_names) if selection is not None else None,
    "eligible_missing_symbolic_count": len(unselected_names & set(prereq_nodes)) if selection is not None else None,
    "existing_finite_receipt_selection": {name: ("accepted" if name in accepted_names else "unselected") for name in (A, B, W)} if selection is not None else None,
    "registry_sha256_before": hashlib.sha256(registry_raw_before).hexdigest() if registry_raw_before is not None else None,
    "registry_sha256_after": digest(registry),
    "native_context_signature": native_context_expected, "selection_helper_sha256": selection_helper_sha,
    "original_selection_block_sha256": selection_block_sha,
    "checks": checks, "error_count": len(errors), "artifacts": artifacts,
    "audit_started": False, "final_export_started": False, "registry_loose_copy_written": False,
    "A_credit": False, "B_credit": False, "W_credit": False,
    "new_owned_audit_credit": False, "full324_credit": False,
    "final_original_export_still_required": True, "wrapper_exit_code": exit_code,
}
receipt_info = write_json("receipt.json", receipt)
if passed:
    for name in full:
        print("P24_CURRENT_RECEIPT_TARGET " + json.dumps({"module": name,
            "status": "accepted" if name in accepted_names else "unselected",
            "symbolic": name in prereq_nodes}), flush=True)
print("P24_CURRENT_RECEIPT_SELECTION_DONE " + json.dumps({
    "receipt": receipt_info, "source_pin": pin, "selection_passed": passed,
    "scope": 324, "accepted_count": receipt["accepted_count"], "unselected_count": receipt["unselected_count"],
    "eligible_missing_symbolic_count": receipt["eligible_missing_symbolic_count"],
    "zero321_exit_code": pre_rc, "zero321_seconds": pre_seconds,
    "registry_sha256_before": receipt["registry_sha256_before"], "registry_sha256_after": receipt["registry_sha256_after"],
    "selection_artifact": artifacts.get("selection"), "checks": checks, "error_count": len(errors),
    "errors_artifact": artifacts.get("errors"), "wrapper_exit_code": exit_code,
    "audit_started": False, "final_export_started": False, "full324_credit": False}), flush=True)
raise SystemExit(exit_code)
