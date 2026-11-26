#!/usr/bin/env bash
# Submission contract: timeout_seconds=3600, memory_mb=13107.
# Preparation only: the owner submits this after the original A gate succeeds.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PY'
import hashlib
import json
import os
from pathlib import Path
import selectors
import subprocess
import sys
import time

root = Path.cwd()
pin = "b55fa93d39e6a4ddf2abd37b9b8481078e329f70"
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
    "ImbalancedChen/ActualThirdOriginalP4AOrdinaryFiniteSelector.lean": "bc50bc05f214ff8c9716000558c170fb8a92334ff7bd32465616507107f81547",
    "ImbalancedChen/Certificates/OriginalNodeArraysV1/DataCore.lean": "048eda0f169f5842cf3a969e0c05eb1192222ac920e71153b4cecd5e564990a6",
    "ImbalancedChen/P2OriginalAdaptiveForestSourceIdentity.lean": "e948aa494518fc9fda2aedeee99e4c8b8f9d27be9cd64692036f1ad0e3e06ce6",
    "ImbalancedChen/P2OriginalCompactConcreteLoop.lean": "04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0",
    "ImbalancedChen/P2OriginalCompactConcreteRun.lean": "18f347ca0c231e7bcceca4e7752908bb311052b01495e839ffcef48aacd0ffd2",
    "ImbalancedChen/P2OriginalCompactQ80ArrayTable.lean": "b07fe6df9a3434301d2af52a6c54b02bd8f6bc6b9dbdd7e957244cf78d337b1d",
    "ImbalancedChen/P2OriginalCompactQ80Encloser.lean": "139686b3a2f5453350faf6495ac30424fbe71aa472ae3eba7d3475e1a0fd5058",
    "ImbalancedChen/P2OriginalPriorityForestLedger.lean": "11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c",
    "ImbalancedChen/P2OriginalCompactQ80Reachability.lean": "6f78f1f03b58666d7c968bbcebd6d7c72a680ed8340a685c67404ea2a873c5fb",
    "ImbalancedChen/P2OriginalCompactQ80FixedBindings.lean": "ba24af1a733626cafc3d53d5fc5294c021879b7503c639f4ef97b937cbd00cc9",
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
    A,
]
full_nodes = project_nodes(root, W)
full = list(full_nodes)
assert len(full) == 324 and len(set(full)) == 324
assert hashlib.sha256(("\n".join(full) + "\n").encode()).hexdigest() == ordered_expected
prereq_nodes = {}
for name in roots:
    prereq_nodes.update(project_nodes(root, name))
assert len(prereq_nodes) == 322
assert set(full) - set(prereq_nodes) == {B, W}
assert A in prereq_nodes and B not in prereq_nodes and W not in prereq_nodes
b_nodes = project_nodes(root, B)
assert len(b_nodes) == 103 and B in b_nodes
assert set(b_nodes) - {B} <= set(prereq_nodes)
assert len(project_nodes(root, A)) == 102
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
common = [sys.executable, "-B", "verification/part2/run_winner9_private_checks.py",
          "--baseline-root", "/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001",
          "--external-snapshot", str(snapshot_path),
          "--memory-mb", "11264", "--workers", "1", "--threads", "1"]
print(json.dumps({
    "phase": "finite_B_b55_draft01_preflight", "source_pin": pin,
    "full_scope": 324, "ordered_fingerprint": ordered_expected,
    "prerequisite_scope": 322, "prerequisite_roots": roots,
    "target_scope": 103, "target": B,
    "source_snapshot_sha256": json_digest(sources_before),
    "pinned_file_sha256": expected, "runtime_sha256": runtime_expected,
    "native_snapshot_sha256": snapshot_expected, "native_context_signature": native_context_expected,
    "registry_sha256_before": digest(registry),
    "memory_mb": 11264, "workers": 1, "threads": 1,
    "time_budget_seconds": 3000, "outer_timeout_seconds": 3600, "job_memory_mb": 13107,
    "prefix_draft_used": False, "B_started": False,
    "kernel_replay_credit": False, "owned_audit_credit": False, "full_p2_complete": False,
}), flush=True)

def run_gate(label, command):
    # Forward original output and newly written module logs without a duplicate log file.
    start_ns = time.time_ns()
    started = time.monotonic()
    seen = {}
    summary = None
    partial_line = b""

    def parse_line(line):
        nonlocal summary
        try:
            value = json.loads(line)
        except (ValueError, UnicodeDecodeError):
            return
        if isinstance(value, dict) and {"roots", "successful_closure", "failed_or_blocked", "pending", "complete", "exit_code", "total"} <= value.keys():
            summary = value

    def report_logs():
        for path in sorted((root / ".lake/p2-private/logs").glob("*.log")):
            try:
                if path.stat().st_mtime_ns < start_ns:
                    continue
                pos = seen.get(str(path), 0)
                with path.open("rb") as stream:
                    stream.seek(pos)
                    chunk = stream.read(65536)
                    if chunk:
                        sys.stdout.buffer.write(("\nLIVE_MODULE_LOG " + str(path) + " offset=" + str(pos) + "\n").encode())
                    while chunk:
                        sys.stdout.buffer.write(chunk)
                        pos += len(chunk)
                        chunk = stream.read(65536)
                sys.stdout.buffer.flush()
                seen[str(path)] = pos
            except OSError as error:
                print(json.dumps({"live_log_read_error": str(path), "error": str(error)}), flush=True)

    print(json.dumps({"phase": label + "_begin", "command": command}), flush=True)
    proc = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
    selector = selectors.DefaultSelector()
    selector.register(proc.stdout, selectors.EVENT_READ)
    last_report = time.monotonic()
    while selector.get_map():
        for key, _ in selector.select(timeout=30):
            chunk = os.read(key.fileobj.fileno(), 65536)
            if not chunk:
                selector.unregister(key.fileobj)
                continue
            sys.stdout.buffer.write(chunk)
            sys.stdout.buffer.flush()
            partial_line += chunk
            while b"\n" in partial_line:
                line, partial_line = partial_line.split(b"\n", 1)
                parse_line(line)
        if time.monotonic() - last_report >= 30:
            report_logs()
            last_report = time.monotonic()
    selector.close()
    proc.stdout.close()
    if partial_line:
        parse_line(partial_line)
    rc = proc.wait()
    report_logs()
    return rc, summary, time.monotonic() - started

def collect_postchecks(summary, rc, phase_roots, total, expected_budget):
    checks, errors = {}, []

    def perform(name, action):
        try:
            action()
            checks[name] = True
        except Exception as error:
            checks[name] = False
            errors.append({"check": name, "error": type(error).__name__ + ": " + str(error)})

    def source_scope():
        current = project_nodes(root, W)
        assert list(current) == full
        assert {name: digest(node["source"]) for name, node in current.items()} == sources_before

    def runtime():
        assert {name: digest(name) for name in runtime_expected} == runtime_expected
        assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN

    def native():
        assert external.verify() == native_before

    def original_summary():
        assert isinstance(summary, dict), "Original driver did not emit its final summary"
        assert summary["roots"] == phase_roots and summary["total"] == total
        assert summary["time_budget_seconds"] == expected_budget
        assert summary["exit_code"] == rc
        assert summary["complete"] == (rc == 0)
        assert summary["successful_closure"] + len(summary["failed_or_blocked"]) + len(summary["pending"]) == total
        if rc == 0:
            assert summary["successful_closure"] == total
            assert not summary["failed_or_blocked"] and not summary["pending"]
            if expected_budget == 0:
                assert summary["reused"] == total

    perform("source_pin_tracked_clean_and_original_verifiers", check_source)
    perform("full_324_order_and_all_source_bytes_unchanged", source_scope)
    perform("lean_and_leanchecker_bytes_unchanged", runtime)
    perform("qualified_native_binding_unchanged", native)
    perform("original_driver_summary_and_exit_consistent", original_summary)
    return checks, errors, perform

pre_rc, pre_summary, pre_seconds = run_gate("P24_FINITE_B_B55_DRAFT01_PREREQUISITES", common + ["--time-budget-seconds", "0", *roots])
pre_checks, pre_errors, pre_perform = collect_postchecks(pre_summary, pre_rc, roots, 322, 0)
prereq_frozen = None
records_before_B = None
if pre_rc == 0 and not pre_errors:
    def bind_prerequisites():
        global prereq_frozen, records_before_B
        records_before_B = json.loads(registry.read_text())
        prereq_frozen = snapshot(root, lib, full_nodes, toolchain, external)
        verify_compilation(records_before_B, prereq_nodes, prereq_frozen)
        assert records_before_B[A]["exit_code"] == 0
        assert records_before_B[A]["source_sha256"] == expected["ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean"]
    pre_perform("original_322_compilation_bindings_including_A", bind_prerequisites)
print(json.dumps({
    "phase": "finite_B_b55_draft01_prerequisites_complete", "source_pin": pin,
    "runner_exit_code": pre_rc, "runner_elapsed_seconds": pre_seconds,
    "original_summary": pre_summary, "postchecks": pre_checks, "postcheck_errors": pre_errors,
    "B_started": False, "A_validated_as_prerequisite": pre_rc == 0 and not pre_errors,
}), flush=True)
if pre_rc != 0 or pre_errors:
    print(json.dumps({"phase": "finite_B_b55_draft01_not_started", "reason": "The original zero-budget 322 prerequisite gate did not pass with all postchecks", "B_started": False, "finite_B_compile_passed": False}), flush=True)
    raise SystemExit(pre_rc if pre_rc != 0 else 125)

b_rc, b_summary, b_seconds = run_gate("P24_FINITE_B_B55_DRAFT01", common + ["--time-budget-seconds", "3000", B])
b_checks, b_errors, b_perform = collect_postchecks(b_summary, b_rc, [B], 103, 3000)
records_after_B = None
after_frozen = None

def bind_after():
    global records_after_B, after_frozen
    records_after_B = json.loads(registry.read_text())
    after_frozen = snapshot(root, lib, full_nodes, toolchain, external)

def untouched_records():
    assert records_after_B is not None
    assert {k: v for k, v in records_after_B.items() if k != B} == {k: v for k, v in records_before_B.items() if k != B}

def untouched_objects():
    assert after_frozen is not None
    assert {k: v for k, v in after_frozen["project"].items() if k != B} == {k: v for k, v in prereq_frozen["project"].items() if k != B}

def prerequisite_bindings():
    assert records_after_B is not None and after_frozen is not None
    verify_compilation(records_after_B, prereq_nodes, after_frozen)

def b_bindings():
    assert records_after_B is not None and after_frozen is not None
    verify_compilation(records_after_B, b_nodes, after_frozen)

b_perform("read_current_registry_and_original_snapshot", bind_after)
b_perform("all_non_B_registry_records_unchanged", untouched_records)
b_perform("all_non_B_project_objects_unchanged", untouched_objects)
b_perform("original_322_prerequisite_bindings_still_valid", prerequisite_bindings)
if b_rc == 0:
    b_perform("original_B_103_compilation_bindings_valid", b_bindings)
passed = b_rc == 0 and not b_errors
exit_code = b_rc if b_rc != 0 else (0 if passed else 125)
b_record = (records_after_B or {}).get(B, {})
print(json.dumps({
    "phase": "finite_B_b55_draft01_complete", "source_pin": pin,
    "full_scope": 324, "ordered_fingerprint": ordered_expected,
    "prerequisite_scope": 322, "target_scope": 103,
    "runner_exit_code": b_rc, "wrapper_exit_code": exit_code, "runner_elapsed_seconds": b_seconds,
    "original_summary": b_summary, "postchecks": b_checks, "postcheck_errors": b_errors,
    "registry_sha256_after": digest(registry),
    "B_record": {key: b_record.get(key) for key in ("source_sha256", "object_sha256", "closure_signature", "exit_code", "command", "log", "seconds", "new_strict_compile")},
    "B_started": True, "finite_B_compile_passed": passed,
    "prefix_draft_used": False, "kernel_replay_credit": False,
    "owned_audit_credit": False, "whole_functional_credit": False, "full_p2_complete": False,
}), flush=True)
raise SystemExit(exit_code)
PY
