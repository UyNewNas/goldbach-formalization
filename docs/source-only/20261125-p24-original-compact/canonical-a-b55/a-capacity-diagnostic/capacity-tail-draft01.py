# Capacity diagnosis only. No original audit runner main or replay is invoked.
from run_winner9_private_audit import TEMPLATE, TEMPLATE_TARGET, parse_audit

MINIMUM_FREE_BYTES = 32 * 1024 * 1024
METADATA_ALLOWANCE = 2 * 1024 * 1024
CAPTURE_DRAIN_ALLOWANCE = 4 * 1024 * 1024
CHUNK_BYTES = 65536
out = root / ".lake/p24-owned-capacity/b55-A-attempt-001"
assert not out.exists() and not out.is_symlink(), "Use a new diagnostic output directory"
assert out.resolve().is_relative_to(root.resolve()), "Diagnostic output resolves outside its own worktree"


def available_bytes():
    stat = os.statvfs(root)
    return stat.f_bavail * stat.f_frsize


def need_free(extra=0):
    free = available_bytes()
    if free < MINIMUM_FREE_BYTES + extra:
        raise RuntimeError("32 MiB free reserve guard: available=" + str(free) + ", extra=" + str(extra))
    return free


def encoded_json(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_derived(name, data):
    assert Path(name).name == name
    need_free(len(data) + 65536)
    destination = out / name
    assert not destination.exists(), "Diagnostic artifact already exists: " + name
    with destination.open("xb") as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    return {"path": str(destination), "bytes": len(data), "sha256": digest(destination)}


def audit_directory_fingerprint():
    directory = root / ".lake/p2-private/audit" / A
    if not directory.exists():
        return {"exists": False, "files": {}}
    assert directory.is_dir() and not directory.is_symlink()
    result = {}
    for path in sorted(directory.rglob("*")):
        assert not path.is_symlink(), "Original target audit contains a symlink"
        if path.is_file():
            result[str(path.relative_to(directory))] = {"bytes": path.stat().st_size, "sha256": digest(path)}
    return {"exists": True, "files": result}


def stop_only_this_child(process):
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=10)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait()


def capture_complete_stdout(command, environment, path):
    raw_hash = hashlib.sha256()
    raw_bytes = 0
    capture_errors = []
    stopped_for_reserve = False
    finished_stream = False
    process = None
    started = time.monotonic()
    # A bounded drain allowance remains in addition to the 32 MiB floor, so a
    # stopped diagnostic child can be drained and this gzip can be finalized.
    need_free(METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE)
    with path.open("xb") as physical:
        with gzip.GzipFile(filename="", mode="wb", compresslevel=9, fileobj=physical, mtime=0) as compressed:
            try:
                process = subprocess.Popen(command, cwd=root, env=environment, stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT, bufsize=0)
                selector = selectors.DefaultSelector()
                selector.register(process.stdout, selectors.EVENT_READ)
                last_report = time.monotonic()
                try:
                    while selector.get_map():
                        for key, _ in selector.select(timeout=5):
                            chunk = os.read(key.fileobj.fileno(), CHUNK_BYTES)
                            if not chunk:
                                selector.unregister(key.fileobj)
                                finished_stream = True
                                continue
                            if not stopped_for_reserve:
                                try:
                                    need_free(METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE + 2 * CHUNK_BYTES)
                                except RuntimeError as error:
                                    stopped_for_reserve = True
                                    capture_errors.append(str(error))
                                    stop_only_this_child(process)
                            compressed.write(chunk)
                            raw_hash.update(chunk)
                            raw_bytes += len(chunk)
                        if time.monotonic() - last_report >= 30:
                            print(json.dumps({"phase": "capacity_capture_progress", "raw_stdout_bytes": raw_bytes,
                                              "gzip_bytes_so_far": physical.tell(),
                                              "free_bytes": available_bytes(), "diagnostic_only": True}, sort_keys=True), flush=True)
                            last_report = time.monotonic()
                    returncode = process.wait()
                finally:
                    selector.close()
                    if process.stdout is not None:
                        process.stdout.close()
            except Exception as error:
                capture_errors.append(type(error).__name__ + ": " + str(error))
                if process is not None:
                    stop_only_this_child(process)
                returncode = process.returncode if process is not None else None
            finally:
                if process is not None and process.poll() is None:
                    stop_only_this_child(process)
        physical.flush()
        os.fsync(physical.fileno())
    result = {"command": command, "lean_exit_code": returncode,
              "seconds": round(time.monotonic() - started, 6),
              "stdout_and_stderr_combined": True,
              "stdout_bytes": raw_bytes, "stdout_sha256": raw_hash.hexdigest(),
              "gzip_path": str(path), "gzip_bytes": path.stat().st_size, "gzip_sha256": digest(path),
              "gzip_compresslevel": 9, "gzip_mtime": 0,
              "read_to_eof": finished_stream, "stopped_for_reserve": stopped_for_reserve,
              "errors": capture_errors}
    result["complete_successful_template_stdout"] = (
        returncode == 0 and finished_stream and not stopped_for_reserve and not capture_errors)
    return result


def fingerprint_gzip_payload(path):
    result = hashlib.sha256()
    count = 0
    with gzip.open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
            count += len(chunk)
    return {"bytes": count, "sha256": result.hexdigest()}


class CompleteGzipAuditText:
    """Only supply the read_text API used by the unchanged original parser."""

    def __init__(self, path):
        self.path = path

    def read_text(self):
        # Path.read_text() and this wrapper both use the standard TextIOWrapper
        # defaults, including locale encoding and universal-newline handling.
        with gzip.open(self.path, "rb") as binary:
            with io.TextIOWrapper(binary) as text:
                return text.read()


def fingerprint_original_text(text):
    # Same text and TextIOWrapper defaults as the original Path.write_text(),
    # but the encoded bytes exist only in memory and are never a loose file.
    with io.BytesIO() as memory:
        with io.TextIOWrapper(memory) as writer:
            encoding = writer.encoding
            writer.write(text)
            writer.flush()
            view = memory.getbuffer()
            try:
                return {"bytes": len(view), "sha256": hashlib.sha256(view).hexdigest(),
                        "text_encoding": encoding}
            finally:
                view.release()


registry_before = {"bytes": registry.stat().st_size, "sha256": digest(registry)}
records = json.loads(registry.read_text())
full_before = snapshot(root, lib, full_nodes, toolchain, external)
assert full_before.get("external_snapshot") == native_before
verify_compilation(records, prereq_nodes, full_before)
verify_compilation(records, a_nodes, full_before)
assert digest(registry) == registry_before["sha256"]
original_audit_before = audit_directory_fingerprint()
template_bytes = TEMPLATE.read_bytes()
assert hashlib.sha256(template_bytes).hexdigest() == expected["verification/part2/winner9_private_audit_template.lean"]
template_text = template_bytes.decode()
assert template_text.count(TEMPLATE_TARGET) == 2
audit_text = template_text.replace(TEMPLATE_TARGET, A)
free_before = need_free(METADATA_ALLOWANCE + CAPTURE_DRAIN_ALLOWANCE + 1024 * 1024)
out.mkdir(parents=True, exist_ok=False)
audit_input = write_derived("Audit.lean", audit_text.encode("utf-8"))
original_template = write_derived("original-template.lean", template_bytes)
before_binding = write_derived("full324-before-snapshot.json", encoded_json(full_before))
original_audit_binding = write_derived("original-A-audit-directory-before.json", encoded_json(original_audit_before))
environment = dict(os.environ)
environment["LEAN_PATH"] = str(lib) + ":" + environment.get("LEAN_PATH", "")
environment = external.environment(environment)
command = [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
           "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", str((out / "Audit.lean").relative_to(root))]
assert command[:-1] == [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
                       "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
initial = {"schema": 1, "purpose": "Exact canonical-A full-owned output capacity diagnosis only",
           "source_pin": pin, "target": A, "target_project_scope": 102,
           "full_source_scope": 324, "ordered_fingerprint": ordered_expected,
           "registry_before": registry_before, "full324_before": before_binding,
           "audit_input": audit_input, "original_template": original_template,
           "original_A_audit_before": original_audit_binding,
           "pinned_file_sha256": expected, "runtime_sha256": runtime_expected,
           "native_binding": native_before, "command": command,
           "lean_path": environment.get("LEAN_PATH", ""),
           "original_parser_module": "run_winner9_private_audit", "original_parser_name": "parse_audit",
           "original_parser_input_project": list(a_nodes),
           "minimum_free_reserve_bytes": MINIMUM_FREE_BYTES, "free_bytes_before": free_before,
           "python_version": sys.version, "gzip_module_sha256": digest(gzip.__file__),
           "outer_timeout_seconds": 3600, "job_memory_mb": 13107, "cpu_threads": 1,
           "lean_memory_mb": 11264, "lean_threads": 1,
           "original_runner_main_called": False, "independent_replay_performed": False,
           "canonical_audit_credit": False, "full324_credit": False,
           "original_raw_audit_files_deleted": False,
           "loose_raw_stdout_declarations_or_types_written": False}
write_derived("diagnostic-input.json", encoded_json(initial))
print(json.dumps({"phase": "capacity_template_begin", "source_pin": pin, "target": A,
                  "audit_input_sha256": audit_input["sha256"], "diagnostic_only": True,
                  "canonical_audit_credit": False, "minimum_free_reserve_bytes": MINIMUM_FREE_BYTES}, sort_keys=True), flush=True)

errors = []
postchecks = {}
capture = None
sizes = None
full_after = None
sizes_binding = None
gzip_path = out / "audit.stdout.log.gz"
try:
    capture = capture_complete_stdout(command, environment, gzip_path)
    roundtrip = fingerprint_gzip_payload(gzip_path)
    assert roundtrip == {"bytes": capture["stdout_bytes"], "sha256": capture["stdout_sha256"]}, "Lossless stdout roundtrip failed"
    capture["gzip_roundtrip_verified"] = True
    if not capture["complete_successful_template_stdout"]:
        raise RuntimeError("Complete successful original-template stdout was not obtained")
    parsed = parse_audit(CompleteGzipAuditText(gzip_path), A, set(a_nodes))
    declarations_size = fingerprint_original_text(json.dumps(parsed, indent=2, sort_keys=True) + "\n")
    types_size = fingerprint_original_text("\n\n".join(
        record["name"] + "\n" + record["type"] for record in parsed["declarations"]) + "\n")
    raw_size = {"bytes": capture["stdout_bytes"], "sha256": capture["stdout_sha256"]}
    sizes = {"diagnostic_only": True, "canonical_audit_credit": False,
             "original_parser_passed_full_owned_rules": True,
             "complete_inventory_and_fulltypes_preserved": True,
             "declaration_count": parsed["declaration_count"], "axiom_counts": parsed["axiom_counts"],
             "full_type_utf8_bytes": sum(len(item["type"].encode("utf-8")) for item in parsed["declarations"]),
             "audit.log": raw_size, "declarations.json": declarations_size, "types.txt": types_size,
             "raw_three_files_bytes": raw_size["bytes"] + declarations_size["bytes"] + types_size["bytes"],
             "gzip_roundtrip_verified": True,
             "serializer": "Exact original json.dumps and name/type join; standard TextIOWrapper defaults in memory",
             "source": "Actual canonical A object and unchanged original complete owned template; no independent replay or canonical runner receipt"}
    del parsed
    assert digest(gzip_path) == capture["gzip_sha256"]
    sizes_binding = write_derived("capacity-sizes.json", encoded_json(sizes))
except Exception as error:
    errors.append({"stage": "template_capture_or_full_parse_or_size", "error": type(error).__name__ + ": " + str(error)})


def postcheck(name, action):
    try:
        action()
        postchecks[name] = True
    except Exception as error:
        postchecks[name] = False
        errors.append({"stage": name, "error": type(error).__name__ + ": " + str(error)})


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
    assert full_after == full_before, "Full324 source/object/runtime/native/tool snapshot changed"
    assert {"bytes": registry.stat().st_size, "sha256": digest(registry)} == registry_before
    current_records = json.loads(registry.read_text())
    verify_compilation(current_records, prereq_nodes, full_after)
    verify_compilation(current_records, a_nodes, full_after)


def check_original_audits_after():
    assert audit_directory_fingerprint() == original_audit_before, "An original canonical A audit artifact changed"


def check_generated_inputs_after():
    assert digest(out / "Audit.lean") == audit_input["sha256"]
    assert digest(out / "original-template.lean") == original_template["sha256"]
    if capture is not None:
        assert digest(gzip_path) == capture["gzip_sha256"]


postcheck("pinned_sources_and_original_tools", check_source)
postcheck("runtime_and_original_native_snapshot_bytes", check_runtime_after)
postcheck("full324_inputs_registry_and_322_compilation_bindings", check_all_inputs_after)
postcheck("original_canonical_A_audit_files_unchanged", check_original_audits_after)
postcheck("generated_diagnostic_input_and_stdout_unchanged", check_generated_inputs_after)
postcheck("minimum_32MiB_free_reserve", need_free)
if full_after is not None:
    write_derived("full324-after-snapshot.json", encoded_json(full_after))
success = (capture is not None and capture.get("complete_successful_template_stdout") is True
           and sizes is not None and not errors and all(postchecks.values()))
exit_code = 0 if success else 125
if capture is not None and isinstance(capture.get("lean_exit_code"), int) and capture["lean_exit_code"] != 0:
    exit_code = capture["lean_exit_code"] if capture["lean_exit_code"] > 0 else 1
result = dict(initial, diagnostic_passed=success, capture=capture, capacity_sizes=sizes_binding,
              original_format_sizes=sizes, postchecks=postchecks, errors=errors,
              registry_after={"bytes": registry.stat().st_size, "sha256": digest(registry)},
              free_bytes_after=available_bytes(), wrapper_exit_code=exit_code,
              canonical_audit_credit=False, independent_replay_performed=False,
              original_runner_main_called=False, full324_credit=False)
result_binding = write_derived("capacity-diagnostic.json", encoded_json(result))
directory_fd = os.open(out, os.O_RDONLY | os.O_DIRECTORY)
try:
    os.fsync(directory_fd)
finally:
    os.close(directory_fd)
print("P24_A_CAPACITY_DIAGNOSTIC_DONE " + json.dumps({
    "result": result_binding, "diagnostic_passed": success, "exit_code": exit_code,
    "gzip": None if capture is None else {key: capture[key] for key in ("gzip_path", "gzip_bytes", "gzip_sha256")},
    "raw_three_files_bytes": None if sizes is None else sizes["raw_three_files_bytes"],
    "canonical_audit_credit": False, "independent_replay_performed": False,
    "full324_credit": False, "errors": errors}, sort_keys=True), flush=True)
raise SystemExit(exit_code)
