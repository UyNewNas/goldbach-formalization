registry_before = {"bytes": registry.stat().st_size, "sha256": digest(registry)}
assert registry_before["sha256"] == actual_B_failure_registry_sha256
records = json.loads(registry.read_text())
full_before = snapshot(root, lib, full_nodes, toolchain, external)
assert full_before["external_snapshot"] == native_before
verify_compilation(records, prereq_nodes, full_before)
verify_compilation(records, a_nodes, full_before)
assert digest(registry) == registry_before["sha256"]
original_audit_before = audit_directory_fingerprint()
assert failure_log.is_file() and not failure_log.is_symlink()
failure_binding = {"path":str(failure_log), "bytes":failure_log.stat().st_size, "sha256":digest(failure_log)}
failure_text = failure_log.read_text()
assert 'Tactic `rfl` failed' in failure_text and 'cachedHistoricalEndpointCheck' in failure_text
assert hashlib.sha256(DIAGNOSTIC_SOURCE.encode()).hexdigest() == diagnostic_source_sha256
free_before = need_free(METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE + 2 * 1024 * 1024)
out.mkdir(parents=True, exist_ok=False)
source_binding = write_derived("RawDefEq.lean", DIAGNOSTIC_SOURCE.encode())
before_binding = write_derived("full324-before-snapshot.json", encoded_json(full_before))
audit_binding = write_derived("original-A-audit-directory-before.json", encoded_json(original_audit_before))
environment = dict(os.environ)
environment["LEAN_PATH"] = str(lib) + ":" + environment.get("LEAN_PATH", "")
environment = external.environment(environment)
command = [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
    "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", str((out / "RawDefEq.lean").relative_to(root))]
initial = {
    "schema":1, "purpose":"Report one original B raw Meta isDefEq result or exception, without isDefEqGuarded",
    "source_pin":pin, "target":B, "full_source_scope":324, "ordered_fingerprint":ordered_expected,
    "pinned_file_sha256":expected, "runtime_sha256":runtime_expected, "native_binding":native_before,
    "registry_before":registry_before, "full324_before":before_binding,
    "original_A_audit_before":audit_binding, "actual_B_failure_log":failure_binding,
    "diagnostic_source":source_binding, "command":command, "lean_path":environment.get("LEAN_PATH", ""),
    "minimum_free_reserve_bytes":MINIMUM_FREE_BYTES, "free_bytes_before":free_before,
    "outer_timeout_seconds":3600, "job_memory_mb":13107, "cpu_threads":1,
    "lean_memory_mb":11264, "lean_threads":1, "same_original_two_local_zero_options":True,
    "original_runner_main_called":False, "original_B_compiler_called":False,
    "second_guarded_probe_run":False, "kernel_replay_credit":False, "owned_audit_credit":False,
    "original_B_compile_credit":False, "full324_credit":False,
}
write_derived("diagnostic-input.json", encoded_json(initial))
print("P24_B_RAW_DEFEQ_BEGIN " + json.dumps(initial, sort_keys=True), flush=True)
capture = None
observations = []
complete_observation = False
full_after = None
errors = []
postchecks = {}
gzip_path = out / "raw-defeq.stdout.log.gz"
try:
    capture = capture_complete_stdout(command, environment, gzip_path)
    assert fingerprint_gzip_payload(gzip_path) == {"bytes":capture["stdout_bytes"], "sha256":capture["stdout_sha256"]}
    capture["gzip_roundtrip_verified"] = True
    assert capture["read_to_eof"] and not capture["stopped_for_reserve"] and not capture["errors"]
    with gzip.open(gzip_path, "rt") as stream:
        for line in stream:
            if line.startswith("P24_B_RAW_DEFEQ "):
                observations.append(json.loads(line[len("P24_B_RAW_DEFEQ "):]))
    assert len(observations) == 2
    begin, outcome = observations
    assert begin["phase"] == "begin" and begin["guarded_call_used"] is False
    assert begin["maxRecDepth_option"] == 0 and begin["effective_maxRecDepth"] == 0
    assert begin["maxHeartbeats_option"] == 0
    assert outcome["phase"] in ("returned", "exception")
    assert all(row["original_B_compile_credit"] is False for row in observations)
    assert outcome["kernel_replay_credit"] is False and outcome["owned_audit_credit"] is False
    if outcome["phase"] == "returned":
        assert isinstance(outcome["isDefEq"], bool) and capture["lean_exit_code"] == 0
    else:
        assert outcome["kind"] in ("error", "internal") and isinstance(outcome["message"], str)
        assert isinstance(capture["lean_exit_code"], int) and capture["lean_exit_code"] != 0
    complete_observation = True
except Exception as error:
    errors.append({"stage":"raw_precheck_capture_or_parse", "error":type(error).__name__+": "+str(error)})


def postcheck(name, action):
    try:
        action()
        postchecks[name] = True
    except Exception as error:
        postchecks[name] = False
        errors.append({"check":name, "error":type(error).__name__+": "+str(error)})


def check_runtime_after():
    assert {name:digest(name) for name in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected


def check_all_inputs_after():
    global full_after
    current_nodes = project_nodes(root, W)
    assert list(current_nodes) == full
    mark_project_nodes(current_nodes, set(external.modules))
    full_after = snapshot(root, lib, current_nodes, toolchain, external)
    assert full_after == full_before
    assert {"bytes":registry.stat().st_size, "sha256":digest(registry)} == registry_before
    current_records = json.loads(registry.read_text())
    verify_compilation(current_records, prereq_nodes, full_after)
    verify_compilation(current_records, a_nodes, full_after)


def check_original_evidence_after():
    assert audit_directory_fingerprint() == original_audit_before
    assert failure_log.is_file() and not failure_log.is_symlink()
    assert {"path":str(failure_log),"bytes":failure_log.stat().st_size,"sha256":digest(failure_log)} == failure_binding


def check_derived_inputs_after():
    assert digest(out / "RawDefEq.lean") == diagnostic_source_sha256
    if capture is not None:
        assert digest(gzip_path) == capture["gzip_sha256"]


postcheck("pinned_sources_and_original_tools", check_source)
postcheck("runtime_and_original_native_snapshot_bytes", check_runtime_after)
postcheck("full324_inputs_registry_native_and_321_plus_A102_bindings", check_all_inputs_after)
postcheck("original_A_audit_and_B_actual_failure_log_unchanged", check_original_evidence_after)
postcheck("diagnostic_source_and_complete_stdout_unchanged", check_derived_inputs_after)
postcheck("minimum_32MiB_free_reserve", need_free)
if full_after is not None:
    write_derived("full324-after-snapshot.json", encoded_json(full_after))
success = complete_observation and not errors and all(postchecks.values())
exit_code = 0 if success else 125
if capture is not None and isinstance(capture.get("lean_exit_code"), int) and capture["lean_exit_code"] != 0:
    exit_code = capture["lean_exit_code"] if capture["lean_exit_code"] > 0 else 1
result = dict(initial, complete_raw_precheck_observation=complete_observation,
    diagnostic_preservation_checks_passed=success, observations=observations, capture=capture,
    postchecks=postchecks, errors=errors, wrapper_exit_code=exit_code,
    registry_after={"bytes":registry.stat().st_size,"sha256":digest(registry)},
    free_bytes_after=available_bytes())
result_binding = write_derived("raw-defeq-diagnostic.json", encoded_json(result))
directory_fd = os.open(out, os.O_RDONLY | os.O_DIRECTORY)
try:
    os.fsync(directory_fd)
finally:
    os.close(directory_fd)
print("P24_B_RAW_DEFEQ_DONE " + json.dumps({
    "result":result_binding, "complete_raw_precheck_observation":complete_observation,
    "diagnostic_preservation_checks_passed":success, "exit_code":exit_code,
    "observations":observations, "capture":capture, "errors":errors,
    "original_B_compile_credit":False,"kernel_replay_credit":False,"owned_audit_credit":False,
    "full324_credit":False}, sort_keys=True), flush=True)
raise SystemExit(exit_code)
