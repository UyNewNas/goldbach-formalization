#!/usr/bin/env bash
# Prepared read-only B raw Meta precheck diagnostic; no original B/replay/audit credit.
# Submission contract: timeout_seconds=3600, memory_mb=13107, cpu_threads=1.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_B_RAW_DEFEQ'
import gzip
import io
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import subprocess
import sys
import time

root = Path.cwd()
pin = "b55fa93d39e6a4ddf2abd37b9b8481078e329f70"
# The owner submits only after the b55 original strict321 gate succeeds; all eleven repaired source hashes are fixed.
assert re.fullmatch(r"[0-9a-f]{40}", pin), "NEW_COMMIT has not been finalized"
A = "ImbalancedChen.P2OriginalCompactArchivedTotalCandidate"
B = "ImbalancedChen.P2OriginalCompactCachedEndpointCandidate"
W = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
ordered_expected = "c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
snapshot_path = Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
snapshot_expected = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
native_context_expected = "71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90"
expected = {
    "verification/part2/run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "verification/part2/run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "verification/part2/winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    "verification/part2/winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
    "verification/part2/inspect_winner9_owner_native.py": "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
    "ImbalancedChen/P2HistoricLogPointInterpreter.lean": "07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552",
    "ImbalancedChen/P2OriginalCompactCachedRun.lean": "61ea2a921d3b754feb82b507a7b632c8570cc6a0b35d3d3ebca0c02936553ce9",
    "ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean": "03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd",
    "ImbalancedChen/P2OriginalCompactCachedEndpointCandidate.lean": "3f84c653e57cf48266a4160477c94112acbad086028c75652892fb9ab04aecb6",
    "verification/part2/export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "ImbalancedChen/P2OriginalCompactWholeFunctionalEndpoint.lean": "606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185",
    "ImbalancedChen/ActualThirdOriginalP4AOrdinaryFiniteSelector.lean": "bc50bc05f214ff8c9716000558c170fb8a92334ff7bd32465616507107f81547",
    "ImbalancedChen/Certificates/OriginalNodeArraysV1/DataCore.lean": "048eda0f169f5842cf3a969e0c05eb1192222ac920e71153b4cecd5e564990a6",
    "ImbalancedChen/P2OriginalAdaptiveForestSourceIdentity.lean": "e948aa494518fc9fda2aedeee99e4c8b8f9d27be9cd64692036f1ad0e3e06ce6",
    "ImbalancedChen/P2OriginalCompactConcreteLoop.lean": "04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0",
    "ImbalancedChen/P2OriginalCompactConcreteRun.lean": "18f347ca0c231e7bcceca4e7752908bb311052b01495e839ffcef48aacd0ffd2",
    "ImbalancedChen/P2OriginalCompactQ80ArrayTable.lean": "b07fe6df9a3434301d2af52a6c54b02bd8f6bc6b9dbdd7e957244cf78d337b1d",
    "ImbalancedChen/P2OriginalCompactQ80Encloser.lean": "139686b3a2f5453350faf6495ac30424fbe71aa472ae3eba7d3475e1a0fd5058",
    "ImbalancedChen/P2OriginalPriorityForestLedger.lean": "11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c",
    "ImbalancedChen/P2OriginalCompactQ80Reachability.lean": "6f78f1f03b58666d7c968bbcebd6d7c72a680ed8340a685c67404ea2a873c5fb",
    "ImbalancedChen/P2OriginalCompactQ80FixedBindings.lean": "ba24af1a733626cafc3d53d5fc5294c021879b7503c639f4ef97b937cbd00cc9"
}

def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def json_digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def check_source():
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == pin
    assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    actual = {name: digest(root / name) for name in expected}
    assert actual == expected, "Pinned source or original verifier bytes changed"

check_source()
sys.path.insert(0, str(root / "verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes

assert PIN == "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
runtime_expected = {
    LEAN: "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    LEANCHECKER: "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
}
assert {name: digest(name) for name in runtime_expected} == runtime_expected
assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
assert digest(snapshot_path) == snapshot_expected
roots = [
    "ImbalancedChen.P2OriginalCompactQ80CompleteSoundness",
    "ImbalancedChen.P2OriginalCompactCachedRun",
    "ImbalancedChen.P2OriginalCompactQ80FixedBindings",
    "ImbalancedChen.P4AOrdinaryRootFirstIntegral",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve",
]
full_nodes = project_nodes(root, W)
full = list(full_nodes)
assert len(full) == 324 and len(set(full)) == 324
assert hashlib.sha256(("\n".join(full) + "\n").encode()).hexdigest() == ordered_expected
prereq_nodes = {}
for name in roots:
    prereq_nodes.update(project_nodes(root, name))
assert len(prereq_nodes) == 321
assert set(full) - set(prereq_nodes) == {A, B, W}
assert A not in prereq_nodes and B not in prereq_nodes and W not in prereq_nodes
a_nodes = project_nodes(root, A)
assert len(a_nodes) == 102 and A in a_nodes
assert set(a_nodes) - {A} <= set(prereq_nodes)
assert len(project_nodes(root, B)) == 103
sources_before = {name: digest(node["source"]) for name, node in full_nodes.items()}
lib = root / ".lake/p2-private/lib"
registry = root / ".lake/p2-private/records.json"
external = ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=PIN, project_lib=lib)
native_before = external.binding()
assert native_before["snapshot_sha256"] == snapshot_expected
assert native_before["context_signature"] == native_context_expected
assert native_before["verification_helper_sha256"] == expected["verification/part2/winner9_external_snapshot.py"]
assert Path(external.value["runtime"]["leanchecker"]).resolve() == Path(LEANCHECKER).resolve()
assert external.files[external.value["runtime"]["leanchecker"]]["sha256"] == runtime_expected[LEANCHECKER]
mark_project_nodes(full_nodes, set(external.modules))
toolchain = {
    "lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
    "lean_binary_sha256": runtime_expected[LEAN],
    "mathlib_commit": PIN,
}

DIAGNOSTIC_SOURCE = 'import ImbalancedChen.P2OriginalCompactCachedRun\nimport Lean\n\n/-!\nFirst, uncompiled diagnostic for the actual b55 B `rfl` failure.\n\nThis reproduces only applyRfl\'s Meta definitional-equality precheck, with its\napproxDefEq configuration and the original two local zero options. It calls\nisDefEq directly once so that an exception cannot silently become false through\nisDefEqGuarded. It neither assigns nor checks an endpoint proof and supplies no\nreplacement table, state, evaluator, result, resource limit, or numerical input.\n\nThe original target remains closed and unrestricted: this probe is not a claim\nthat its execution time is bounded by the previous 4.312-second failure. The\nunchanged external job limits remain the execution bound. A true result here\nwould still confer no original B compile, kernel replay, or owned-audit credit.\n-/\n\nnamespace P24CachedEndpointRawDefEqDiagnostic\n\nopen Lean Meta Elab Command\n\nprivate def emit (value : Json) : MetaM Unit := do\n  let stream ← IO.getStdout\n  stream.putStrLn ("P24_B_RAW_DEFEQ " ++ value.compress)\n  stream.flush\n\nprivate def rawProbe : MetaM Unit := do\n  let options ← getOptions\n  let begin := Json.mkObj [\n    ("phase", toJson "begin"),\n    ("maxRecDepth_option", toJson (maxRecDepth.get options)),\n    ("maxHeartbeats_option", toJson (maxHeartbeats.get options)),\n    ("effective_maxRecDepth", toJson (← MonadRecDepth.getMaxRecDepth)),\n    ("current_recDepth", toJson (← MonadRecDepth.getRecDepth)),\n    ("guarded_call_used", toJson false),\n    ("original_B_compile_credit", toJson false)]\n  emit begin\n  let lhs := mkConst\n    `ImbalancedChen.P2OriginalCompactCachedRunSourceOnly.cachedHistoricalEndpointCheck\n  let rhs := mkConst ``Bool.true\n  tryCatchRuntimeEx\n    (do\n      let result ← approxDefEq <| isDefEq lhs rhs\n      emit <| Json.mkObj [\n        ("phase", toJson "returned"), ("isDefEq", toJson result),\n        ("original_B_compile_credit", toJson false),\n        ("kernel_replay_credit", toJson false), ("owned_audit_credit", toJson false)])\n    (fun exception => do\n      let kind := match exception with\n        | .error _ _ => "error"\n        | .internal _ _ => "internal"\n      emit <| Json.mkObj [\n        ("phase", toJson "exception"), ("kind", toJson kind),\n        ("isMaxRecDepth", toJson exception.isMaxRecDepth),\n        ("isMaxHeartbeat", toJson exception.isMaxHeartbeat),\n        ("isInterrupt", toJson exception.isInterrupt),\n        ("message", toJson (← exception.toMessageData.toString)),\n        ("original_B_compile_credit", toJson false),\n        ("kernel_replay_credit", toJson false), ("owned_audit_credit", toJson false)]\n      throw exception)\n\n-- Exactly the two original B declaration-local option values; no increase.\nset_option maxRecDepth 0 in\nset_option maxHeartbeats 0 in\nrun_cmd liftTermElabM rawProbe\n\nend P24CachedEndpointRawDefEqDiagnostic\n'

# Only a new diagnostic input and lossless output are written. Original B is not compiled.
MINIMUM_FREE_BYTES = 32 * 1024 * 1024
METADATA_ALLOWANCE = 2 * 1024 * 1024
CAPTURE_DRAIN_ALLOWANCE = 4 * 1024 * 1024
CHUNK_BYTES = 65536
out = root / ".lake/p24-B-raw-defeq/b55-attempt-001"
assert not out.exists() and not out.is_symlink(), "Preserve prior diagnostic evidence"
assert out.resolve().is_relative_to(root.resolve())
diagnostic_source_sha256 = "2eb7dc403ee25098cfe711ab887d3988fe6c87a8872cca758d49ed36dd06cf4e"
actual_B_failure_registry_sha256 = "3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445"
failure_log = root / ".lake/p2-private/logs/ImbalancedChen.P2OriginalCompactCachedEndpointCandidate.attempt1.log"


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
                            print(json.dumps({"phase": "B_raw_defeq_capture_progress", "raw_stdout_bytes": raw_bytes,
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

P24_B_RAW_DEFEQ
