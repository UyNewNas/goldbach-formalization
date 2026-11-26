#!/usr/bin/env bash
# Reviewed three-proof source pin b55fa93d39e6a4ddf2abd37b9b8481078e329f70. Owner submits after wrapper review.
# Submission contract: timeout_seconds=3600, memory_mb=13107, cpu_threads=1.
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_THREE_SOURCE_STRICT321'
import hashlib
import json
import os
from pathlib import Path
import re
import selectors
import subprocess
import sys
import time

source_rows = json.loads(r'''[{"path":"ImbalancedChen/P2OriginalCompactCachedRun.lean","old_sha256":"80aab3eb9bda4146fa09ab0245a5bf93114dbf3f788175fb5ed868bfa8a330d4","new_sha256":"61ea2a921d3b754feb82b507a7b632c8570cc6a0b35d3d3ebca0c02936553ce9","new_bytes":24219},{"path":"ImbalancedChen/P2OriginalCompactQ80Reachability.lean","old_sha256":"bdddc14dd6fbd49f7bed6853b87afdc16673d4db8e4a7c8e32e7bce5d11b06d7","new_sha256":"6f78f1f03b58666d7c968bbcebd6d7c72a680ed8340a685c67404ea2a873c5fb","new_bytes":3238},{"path":"ImbalancedChen/P2OriginalCompactQ80FixedBindings.lean","old_sha256":"ce5db10a7ecdfc22eeabecf6df44e0cf302ab8c5768184b2629c58bc3bdb302c","new_sha256":"ba24af1a733626cafc3d53d5fc5294c021879b7503c639f4ef97b937cbd00cc9","new_bytes":13478}]''')

root = Path.cwd()
old_pin = "1087bc663a46352f99b2e9a1da238aaf4b855fdf"
new_pin = "b55fa93d39e6a4ddf2abd37b9b8481078e329f70"
# The owner fills the exact reviewed commit only after freezing the final three-source manifest.
assert re.fullmatch(r"[0-9a-f]{40}", new_pin) and new_pin != old_pin, "NEW_COMMIT has not been finalized"
out = Path("/workspace/p24-integration-proof-repairs-20261126/attempt-001")
assert not out.exists(), "Use a new output directory for a new promotion attempt"
A = "ImbalancedChen.P2OriginalCompactArchivedTotalCandidate"
B = "ImbalancedChen.P2OriginalCompactCachedEndpointCandidate"
W = "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"
roots = [
    "ImbalancedChen.P2OriginalCompactQ80CompleteSoundness",
    "ImbalancedChen.P2OriginalCompactCachedRun",
    "ImbalancedChen.P2OriginalCompactQ80FixedBindings",
    "ImbalancedChen.P4AOrdinaryRootFirstIntegral",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve",
]
ordered_expected = "c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
snapshot_path = Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
snapshot_expected = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
native_context_expected = "71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90"
expected_tools = {
    "verification/part2/run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "verification/part2/run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "verification/part2/winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    "verification/part2/export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "verification/part2/winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
    "verification/part2/inspect_winner9_owner_native.py": "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
}
stable_sources = {
    "ImbalancedChen/P2HistoricLogPointInterpreter.lean": "07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552",
    "ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean": "03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd",
    "ImbalancedChen/P2OriginalCompactCachedEndpointCandidate.lean": "3f84c653e57cf48266a4160477c94112acbad086028c75652892fb9ab04aecb6",
    "ImbalancedChen/P2OriginalCompactWholeFunctionalEndpoint.lean": "606cb2277c031d440cc379aedd4029a8f386f9925d93ccfcb77cf37557d80185",
}

def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def sha_bytes(raw):
    return hashlib.sha256(raw).hexdigest()

def json_digest(value):
    return sha_bytes(json.dumps(value, sort_keys=True, separators=(",", ":")).encode())

def info(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest(path)}

def write(name, value):
    (out / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")

def git(*args):
    return subprocess.check_output(["git", *args], cwd=root)

def check_head_and_clean(pin):
    assert git("rev-parse", "HEAD").decode().strip() == pin
    assert not git("status", "--porcelain", "--untracked-files=no").strip()

def check_tools_and_stable_sources():
    assert {path: digest(root / path) for path in expected_tools} == expected_tools
    assert {path: digest(root / path) for path in stable_sources} == stable_sources

check_head_and_clean(old_pin)
check_tools_and_stable_sources()
assert len(source_rows) == 3 and len({row["path"] for row in source_rows}) == 3
for row in source_rows:
    assert digest(root / row["path"]) == row["old_sha256"]

sys.path.insert(0, str(root / "verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes

assert PIN == "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
runtime_expected = {
    LEAN: "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
    LEANCHECKER: "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
}

def check_runtime():
    assert {path: digest(path) for path in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected

check_runtime()

def get_scopes():
    full_nodes = project_nodes(root, W)
    full = list(full_nodes)
    assert len(full) == len(set(full)) == 324
    assert sha_bytes(("\n".join(full) + "\n").encode()) == ordered_expected
    selected = {}
    for name in roots:
        selected.update(project_nodes(root, name))
    assert len(selected) == 321 and set(full) - set(selected) == {A, B, W}
    assert len(project_nodes(root, A)) == 102
    assert len(project_nodes(root, B)) == 103
    for row in source_rows:
        module = row["path"][:-5].replace("/", ".")
        assert module in selected
        assert Path(selected[module]["source"]).relative_to(root).as_posix() == row["path"]
    return full_nodes, selected

old_nodes, old_selected = get_scopes()
full_order = list(old_nodes)
sources_before = {name: digest(node["source"]) for name, node in old_nodes.items()}
sources_expected = dict(sources_before)
for row in source_rows:
    sources_expected[row["path"][:-5].replace("/", ".")] = row["new_sha256"]
lib = root / ".lake/p2-private/lib"
registry = root / ".lake/p2-private/records.json"
registry_before_raw = registry.read_bytes()
registry_before = json.loads(registry_before_raw)
external = ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=PIN, project_lib=lib)
native_before = external.binding()
assert native_before["snapshot_sha256"] == snapshot_expected
assert native_before["context_signature"] == native_context_expected
assert native_before["verification_helper_sha256"] == expected_tools["verification/part2/winner9_external_snapshot.py"]
assert Path(external.value["runtime"]["leanchecker"]).resolve() == Path(LEANCHECKER).resolve()
assert external.files[external.value["runtime"]["leanchecker"]]["sha256"] == runtime_expected[LEANCHECKER]
mark_project_nodes(old_nodes, set(external.modules))
toolchain = {
    "lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
    "lean_binary_sha256": runtime_expected[LEAN],
    "mathlib_commit": PIN,
}
before_frozen = snapshot(root, lib, old_nodes, toolchain, external)
assert before_frozen["external_snapshot"] == native_before
out.mkdir(parents=True, exist_ok=False)
write("source-bindings.json", source_rows)
write("source-map-before.json", sources_before)
write("source-map-expected-after.json", sources_expected)
write("full324-before-snapshot.json", before_frozen)
(out / "registry-before.json").write_bytes(registry_before_raw)
receipt = {
    "phase": "before_promotion", "old_source_pin": old_pin, "new_source_pin": new_pin,
    "full_scope": 324, "ordered_fingerprint": ordered_expected, "strict_scope": 321,
    "strict_roots": roots, "source_bindings": source_rows,
    "all_324_source_sha256_before": json_digest(sources_before),
    "all_324_source_sha256_expected_after": json_digest(sources_expected),
    "registry_before": info(out / "registry-before.json"),
    "verifier_sha256": expected_tools, "stable_source_sha256": stable_sources,
    "runtime_sha256": runtime_expected, "native_before": native_before,
    "memory_mb": 11264, "workers": 1, "threads": 1, "time_budget_seconds": 3000,
    "outer_timeout_seconds": 3600, "job_memory_mb": 13107,
    "promotion_completed": False, "original_gate_started": False,
    "strict321_compile_passed": False, "old_321_all_reuse_credit_transferred": False,
    "A_new_pin_credit": False, "B_new_pin_credit": False, "W_new_pin_credit": False,
    "independent_replay_credit": False, "owned_audit_credit": False, "full324_credit": False,
}
write("receipt.json", receipt)
common = [sys.executable, "-B", "verification/part2/run_winner9_private_checks.py",
          "--baseline-root", "/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001",
          "--external-snapshot", str(snapshot_path),
          "--memory-mb", "11264", "--workers", "1", "--threads", "1"]

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

checks, errors = {}, []
original_rc, original_summary, original_seconds = None, None, None
new_nodes, new_selected = None, None

def perform(name, action):
    try:
        action()
        checks[name] = True
    except Exception as error:
        checks[name] = False
        errors.append({"check": name, "error": type(error).__name__ + ": " + str(error)})

try:
    print(json.dumps({"phase": "fetch_reviewed_commit", "old_source_pin": old_pin, "new_source_pin": new_pin}), flush=True)
    fetched = subprocess.run(["git", "fetch", "origin", new_pin], cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert fetched.returncode == 0, "git fetch failed; raw stderr is withheld"
    assert git("rev-parse", new_pin + "^{commit}").decode().strip() == new_pin
    assert subprocess.run(["git", "merge-base", "--is-ancestor", old_pin, new_pin], cwd=root).returncode == 0
    changed = [path.decode() for path in git("diff", "--name-only", "--no-renames", "-z", old_pin, new_pin).split(b"\0") if path]
    receipt["git_changed_paths"] = changed
    write("receipt.json", receipt)
    expected_paths = {row["path"] for row in source_rows}
    assert set(path for path in changed if not path.startswith(("docs/", "diagnostics/"))) == expected_paths, "Commit changes more than the three reviewed sources and reviewed docs/diagnostics evidence"
    for row in source_rows:
        raw = git("show", new_pin + ":" + row["path"])
        assert len(raw) == row["new_bytes"] and sha_bytes(raw) == row["new_sha256"]
    check_head_and_clean(old_pin)
    assert digest(registry) == sha_bytes(registry_before_raw)
    merged = subprocess.run(["git", "merge", "--ff-only", new_pin], cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    assert merged.returncode == 0, "git fast-forward failed; inspect the retained receipt and repository status"
    check_head_and_clean(new_pin)
    check_tools_and_stable_sources()
    check_runtime()
    new_nodes, new_selected = get_scopes()
    assert list(new_nodes) == full_order and set(new_selected) == set(old_selected)
    promoted_sources = {name: digest(node["source"]) for name, node in new_nodes.items()}
    assert promoted_sources == sources_expected
    assert digest(registry) == sha_bytes(registry_before_raw), "Source promotion changed compilation records before the original gate"
    for name in (A, B, W):
        obj = Path(before_frozen["project"][name]["object"])
        assert (digest(obj) if obj.is_file() else None) == before_frozen["project"][name]["object_sha256"]
    write("source-map-after-promotion.json", promoted_sources)
    receipt.update({"phase": "original_strict321_gate", "promotion_completed": True,
                    "git_changed_paths": changed, "original_gate_started": True,
                    "registry_sha256_after_promotion": digest(registry)})
    write("receipt.json", receipt)
    print(json.dumps({"phase": "P24_THREE_SOURCE_STRICT321_BEGIN", "source_pin": new_pin,
                      "strict_scope": 321, "full_scope": 324, "ordered_fingerprint": ordered_expected,
                      "source_map_sha256": json_digest(promoted_sources), "registry_sha256_before_gate": digest(registry),
                      "A_B_W_selected": False, "time_budget_seconds": 3000}), flush=True)
    original_rc, original_summary, original_seconds = run_gate(
        "P24_THREE_SOURCE_STRICT321", common + ["--time-budget-seconds", "3000", *roots])
except Exception as error:
    errors.append({"check": "promotion_or_original_gate_execution", "error": type(error).__name__ + ": " + str(error)})

def current_source_scope():
    check_head_and_clean(new_pin)
    check_tools_and_stable_sources()
    nodes, selected = get_scopes()
    assert list(nodes) == full_order and set(selected) == set(old_selected)
    assert {name: digest(node["source"]) for name, node in nodes.items()} == sources_expected

def current_native():
    assert external.verify() == native_before

after_frozen = None
registry_after = None

def capture_current_bindings():
    global after_frozen, registry_after
    raw = registry.read_bytes()
    registry_after = json.loads(raw)
    (out / "registry-after.json").write_bytes(raw)
    current_nodes, _ = get_scopes()
    mark_project_nodes(current_nodes, set(external.modules))
    after_frozen = snapshot(root, lib, current_nodes, toolchain, external)
    write("full324-after-snapshot.json", after_frozen)
    write("source-map-after.json", {name: digest(node["source"]) for name, node in current_nodes.items()})

def untouched_unselected_records_and_objects():
    assert registry_after is not None and after_frozen is not None
    assert {k: v for k, v in registry_after.items() if k not in old_selected} == {
        k: v for k, v in registry_before.items() if k not in old_selected}
    for name in (A, B, W):
        assert after_frozen["project"][name] == before_frozen["project"][name]

def summary_consistent():
    assert original_rc is not None and isinstance(original_summary, dict), "The original gate has no normal final summary"
    assert original_summary["roots"] == roots and original_summary["total"] == 321
    assert original_summary["time_budget_seconds"] == 3000
    assert original_summary["exit_code"] == original_rc
    assert original_summary["complete"] == (original_rc == 0)
    assert original_summary["successful_closure"] + len(original_summary["failed_or_blocked"]) + len(original_summary["pending"]) == 321
    if original_rc == 0:
        assert original_summary["successful_closure"] == 321
        assert not original_summary["failed_or_blocked"] and not original_summary["pending"]

def current_321_compilation_bindings():
    assert registry_after is not None and after_frozen is not None and new_selected is not None
    verify_compilation(registry_after, new_selected, after_frozen)

perform("new_pin_clean_full324_scope_and_all_source_hashes", current_source_scope)
perform("original_runtime_and_snapshot_bytes", check_runtime)
perform("qualified_native_inputs_unchanged", current_native)
perform("record_full324_and_registry_after", capture_current_bindings)
perform("all_unselected_records_and_A_B_W_objects_unchanged", untouched_unselected_records_and_objects)
perform("original_driver_summary_matches_actual_exit", summary_consistent)
if original_rc == 0:
    perform("original_verify_compilation_binds_current_321", current_321_compilation_bindings)
passed = original_rc == 0 and not errors
wrapper_rc = original_rc if original_rc is not None and original_rc != 0 else (0 if passed else 125)
receipt.update({
    "phase": "complete", "original_gate_exit_code": original_rc, "wrapper_exit_code": wrapper_rc,
    "original_gate_seconds": original_seconds, "original_summary": original_summary,
    "strict321_compile_passed": passed, "postchecks": checks, "postcheck_errors": errors,
    "registry_sha256_after": digest(registry), "registry_after": info(out / "registry-after.json") if (out / "registry-after.json").is_file() else None,
    "new_pin_actual_reused_count": original_summary.get("reused") if isinstance(original_summary, dict) else None,
    "old_321_all_reuse_credit_transferred": False,
    "A_new_pin_credit": False, "B_new_pin_credit": False, "W_new_pin_credit": False,
    "independent_replay_credit": False, "owned_audit_credit": False, "full324_credit": False,
})
write("receipt.json", receipt)
print("P24_THREE_SOURCE_STRICT321_DONE " + json.dumps({
    "receipt": info(out / "receipt.json"), "old_source_pin": old_pin, "new_source_pin": new_pin,
    "original_exit_code": original_rc, "wrapper_exit_code": wrapper_rc,
    "original_seconds": original_seconds, "original_summary": original_summary,
    "postchecks": checks, "postcheck_errors": errors, "strict321_compile_passed": passed,
    "registry_sha256_before": sha_bytes(registry_before_raw), "registry_sha256_after": digest(registry),
    "A_new_pin_credit": False, "B_new_pin_credit": False, "W_new_pin_credit": False,
    "independent_replay_credit": False, "owned_audit_credit": False, "full324_credit": False,
}), flush=True)
raise SystemExit(wrapper_rc)

P24_THREE_SOURCE_STRICT321
