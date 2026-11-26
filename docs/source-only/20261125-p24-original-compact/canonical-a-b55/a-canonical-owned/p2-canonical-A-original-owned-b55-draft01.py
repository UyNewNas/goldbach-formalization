import gzip
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
# The original strict321 and current finite A compile records must be valid at b55.
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
common = [sys.executable, "-B", "verification/part2/run_winner9_private_checks.py",
          "--baseline-root", "/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001",
          "--external-snapshot", str(snapshot_path),
          "--memory-mb", "11264", "--workers", "1", "--threads", "1"]
requested_targets = [A]
repaired_source_paths = ["ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean"]

# This diagnostic binds space estimates only. The original audit CLI must still
# perform independent replay and create all three complete plaintext artifacts.
capacity_directory = root / ".lake/p24-owned-capacity/b55-A-attempt-001"
capacity_receipt_path = capacity_directory / "capacity-diagnostic.json"
capacity_receipt_sha256 = "47734ae76baf0a59f4f381e491ff4fc2ed62669a2fd81131af24635bb94d20a9"
assert re.fullmatch(r"[0-9a-f]{64}", capacity_receipt_sha256), \
    "Freeze the completed actual capacity receipt before submission"
minimum_free_reserve = 32 * 1024 * 1024
replay_allocation_allowance = 1 * 1024 * 1024
wrapper_allocation_allowance = 4 * 1024 * 1024
capacity_binding = None
capacity_sizes = None


def bound_capacity_file(binding, expected_name):
    path = Path(binding["path"])
    assert path == capacity_directory / expected_name
    assert path.is_file() and not path.is_symlink()
    assert path.resolve().is_relative_to(capacity_directory.resolve())
    assert file_info(path) == binding
    return path


def bind_capacity_and_check_original_audit_space():
    global capacity_binding, capacity_sizes
    assert capacity_receipt_path.is_file() and not capacity_receipt_path.is_symlink()
    assert digest(capacity_receipt_path) == capacity_receipt_sha256
    measured = json.loads(capacity_receipt_path.read_text())
    assert measured["diagnostic_passed"] is True and measured["wrapper_exit_code"] == 0
    assert measured["source_pin"] == pin and measured["target"] == A
    assert measured["target_project_scope"] == 102 and measured["full_source_scope"] == 324
    assert measured["ordered_fingerprint"] == ordered_expected
    assert measured["pinned_file_sha256"] == expected
    assert measured["runtime_sha256"] == runtime_expected
    assert measured["native_binding"] == native_before
    assert measured["postchecks"] and all(value is True for value in measured["postchecks"].values())
    assert not measured["errors"]
    assert measured["registry_before"] == measured["registry_after"]
    assert measured["original_runner_main_called"] is False
    assert measured["independent_replay_performed"] is False
    assert measured["canonical_audit_credit"] is False and measured["full324_credit"] is False
    assert measured["lean_memory_mb"] == 11264 and measured["lean_threads"] == 1
    assert measured["outer_timeout_seconds"] == 3600 and measured["job_memory_mb"] == 13107
    assert measured["command"][:-1] == [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
        "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
    frozen_path = bound_capacity_file(measured["full324_before"], "full324-before-snapshot.json")
    measured_frozen = json.loads(frozen_path.read_text())
    # B or W may have gained a current object after the diagnostic. Only A's
    # exact 102-source/object closure determines its complete owned type output.
    assert {name: measured_frozen["project"][name] for name in a_nodes} == \
        {name: pre_frozen["project"][name] for name in a_nodes}
    for key in ("toolchain", "lean_binary_sha256", "leanchecker_sha256", "template_sha256",
                "driver_sha256", "external_snapshot"):
        assert measured_frozen[key] == pre_frozen[key]
    sizes_path = bound_capacity_file(measured["capacity_sizes"], "capacity-sizes.json")
    capacity_sizes = json.loads(sizes_path.read_text())
    assert capacity_sizes == measured["original_format_sizes"]
    assert capacity_sizes["original_parser_passed_full_owned_rules"] is True
    assert capacity_sizes["complete_inventory_and_fulltypes_preserved"] is True
    assert capacity_sizes["gzip_roundtrip_verified"] is True
    assert capacity_sizes["canonical_audit_credit"] is False
    capture = measured["capture"]
    assert capture["complete_successful_template_stdout"] is True
    assert capture["lean_exit_code"] == 0 and capture["read_to_eof"] is True
    assert capture["stopped_for_reserve"] is False and not capture["errors"]
    compressed = {"path": capture["gzip_path"], "bytes": capture["gzip_bytes"],
                  "sha256": capture["gzip_sha256"]}
    gzip_path = bound_capacity_file(compressed, "audit.stdout.log.gz")
    restored_hash, restored_bytes = hashlib.sha256(), 0
    with gzip.open(gzip_path, "rb") as stream:
        while chunk := stream.read(65536):
            restored_hash.update(chunk)
            restored_bytes += len(chunk)
    assert {"bytes": restored_bytes, "sha256": restored_hash.hexdigest()} == capacity_sizes["audit.log"]
    assert restored_bytes == capture["stdout_bytes"] and restored_hash.hexdigest() == capture["stdout_sha256"]
    raw_names = ("audit.log", "declarations.json", "types.txt")
    for name in raw_names:
        assert isinstance(capacity_sizes[name]["bytes"], int) and capacity_sizes[name]["bytes"] > 0
        assert re.fullmatch(r"[0-9a-f]{64}", capacity_sizes[name]["sha256"])
    assert capacity_sizes["raw_three_files_bytes"] == sum(capacity_sizes[name]["bytes"] for name in raw_names)
    assert capacity_sizes["raw_three_files_bytes"] == 485251971
    disk = os.statvfs(root)
    block = disk.f_frsize
    allocated = lambda count: ((count + block - 1) // block) * block
    original_raw_allocation = sum(allocated(capacity_sizes[name]["bytes"]) for name in raw_names)
    # The before-registry copy already exists; reserve the exact same lossless
    # after-registry payload plus its small index, never another plaintext copy.
    future_registry_bytes = len(gzip.compress(registry.read_bytes(), compresslevel=9, mtime=0))
    future_registry_allocation = allocated(future_registry_bytes) + 65536
    required = (original_raw_allocation + future_registry_allocation + replay_allocation_allowance
                + wrapper_allocation_allowance + minimum_free_reserve)
    capacity_binding = {
        "receipt": file_info(capacity_receipt_path), "sizes": file_info(sizes_path),
        "full324_reference": file_info(frozen_path), "complete_stdout_gzip": file_info(gzip_path),
        "exact_A_102_input_binding_unchanged": True,
        "raw_three_files_bytes": capacity_sizes["raw_three_files_bytes"],
        "raw_three_files_block_allocation": original_raw_allocation,
        "future_registry_allocation": future_registry_allocation,
        "replay_allocation_allowance": replay_allocation_allowance,
        "wrapper_allocation_allowance": wrapper_allocation_allowance,
        "minimum_free_reserve": minimum_free_reserve,
        "required_available_bytes_before_original_CLI": required,
        "actual_available_bytes": disk.f_bavail * block,
        "diagnostic_credit_transferred": False,
        "shape_checker_run_in_separate_bound_wrapper": True,
    }
    write_evidence("capacity-binding-and-space-guard.json", capacity_binding)
    assert capacity_binding["actual_available_bytes"] >= required, \
        "Insufficient space for the original complete three files and preserved reserve"


def verify_original_plaintext_sizes():
    row = captured_modules[A]
    receipt = json.loads(Path(row["captured_latest"]["path"]).read_text())
    assert receipt["accepted"] is True
    measured = {}
    for name in ("audit.log", "declarations.json", "types.txt"):
        candidates = [root / path for path in receipt["artifacts"] if Path(path).name == name]
        assert len(candidates) == 1
        info = file_info(candidates[0])
        assert info["sha256"] == receipt["artifacts"][str(candidates[0].relative_to(root))]
        assert {key: info[key] for key in ("bytes", "sha256")} == \
            {key: capacity_sizes[name][key] for key in ("bytes", "sha256")}
        measured[name] = info
    assert receipt["audit"]["declaration_count"] == capacity_sizes["declaration_count"]
    assert receipt["audit"]["axiom_counts"] == capacity_sizes["axiom_counts"]
    write_evidence("original-plaintext-artifacts-match-capacity.json", {
        "original_plaintext_files": measured,
        "all_original_files_retained": True,
        "capacity_diagnostic_credit_transferred": False,
    })

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

# No selector/exporter package is run. Only canonical A is passed to the unchanged
# original replay/full-owned CLI. The capacity diagnostic supplies no audit credit.
summary_name = "p24-owned-b55-canonical-A-001.json"
audit_root = root / ".lake/p2-private/audit"
summary_path = audit_root / summary_name
out = Path("/workspace/p24-canonical-A-original-owned-20261126/attempt-001")
assert not out.exists(), "Preserve earlier wrapper evidence; choose a new attempt directory"
assert not summary_path.exists(), "Preserve the original summary; choose a new summary name"
assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= minimum_free_reserve + 8 * 1024 * 1024
assert len(requested_targets) == len(set(requested_targets)) == 1
targets = [name for name in full if name in set(requested_targets)]
assert targets == [A] and len(targets) == 1
assert set(targets) <= set(prereq_nodes)
assert set(targets).isdisjoint({B, W})
assert {name.replace(".", "/") + ".lean" for name in targets} == set(repaired_source_paths)
for name in targets:
    assert Path(full_nodes[name]["source"]).relative_to(root).as_posix() == name.replace(".", "/") + ".lean"

out.mkdir(parents=True, exist_ok=False)
(out / "latest-before").mkdir()
(out / "latest-after").mkdir()

def write_evidence(name, value):
    (out / name).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")

def file_info(path):
    path = Path(path)
    return {"path": str(path), "bytes": path.stat().st_size, "sha256": digest(path)}

def write_registry_snapshot(name, raw):
    # Only wrapper-owned complete registry copies are compressed; the canonical
    # registry and every original runner artifact remain at their original paths.
    assert name in {"registry-before-audit.json", "registry-after-audit.json"}
    path = out / (name + ".gz")
    index_path = out / (name + ".gz.index.json")
    assert not path.exists() and not index_path.exists(), "Preserve earlier compressed evidence"
    compressed = gzip.compress(raw, compresslevel=9, mtime=0)
    raw_sha256 = hashlib.sha256(raw).hexdigest()
    index = {
        "canonical_registry": str(registry),
        "uncompressed_bytes": len(raw), "uncompressed_sha256": raw_sha256,
        "gzip": {"path": str(path), "bytes": len(compressed),
                 "sha256": hashlib.sha256(compressed).hexdigest()},
        "lossless_decompressed_bytes_equal": True,
        "lossless_decompressed_sha256": raw_sha256,
        "loose_registry_copy_written": False,
    }
    index_raw = (json.dumps(index, ensure_ascii=False, indent=2) + "\n").encode()
    disk = os.statvfs(out)
    block = disk.f_frsize
    reserve = 32 * 1024 * 1024
    allocation = (((len(compressed) + block - 1) // block
                   + (len(index_raw) + block - 1) // block + 1) * block)
    assert disk.f_bavail * block >= allocation + reserve, \
        "Compressed registry and index would breach the original 32 MiB reserve"
    with path.open("xb") as stream:
        stream.write(compressed)
    restored = gzip.decompress(path.read_bytes())
    assert restored == raw, "Compressed registry did not preserve the complete original bytes"
    assert len(restored) == len(raw) and hashlib.sha256(restored).hexdigest() == raw_sha256
    assert file_info(path) == index["gzip"]
    with index_path.open("xb") as stream:
        stream.write(index_raw)
    disk_after = os.statvfs(out)
    assert disk_after.f_bavail * disk_after.f_frsize >= reserve
    return index

write_evidence("requested-targets.json", {"requested_explicit_modules": requested_targets,
    "original_full324_topological_order": targets, "ordered_fingerprint": ordered_expected})
print(json.dumps({
    "phase": "canonical_owned_A_preflight", "source_pin": pin,
    "full_scope": 324, "prerequisite_scope": 322, "requested": 1,
    "ordered_fingerprint": ordered_expected, "targets": targets,
    "all_324_source_sha256": json_digest(sources_before), "pinned_file_sha256": expected,
    "runtime_sha256": runtime_expected, "native_before": native_before,
    "memory_mb": 11264, "workers": 1, "threads": 1,
    "prerequisite_time_budget_seconds": 0, "outer_timeout_seconds": 3600, "job_memory_mb": 13107,
    "original_runner_flags_preserved": True, "selector_run": False, "exporter_package_run": False,
    "canonical_owned_A_passed": False, "A_owned_audit_credit": False, "B_credit": False,
    "W_credit": False, "full324_credit": False,
}), flush=True)

pre_rc, pre_summary, pre_seconds = run_gate(
    "P24_CANONICAL_OWNED_A_PREREQUISITES", common + ["--time-budget-seconds", "0", *roots])
pre_checks, pre_errors, pre_perform = collect_postchecks(pre_summary, pre_rc, roots, 322, 0)
pre_frozen = None
records_before = None
registry_expected = None

def bind_current_prerequisites():
    global pre_frozen, records_before, registry_expected
    raw = registry.read_bytes()
    registry_expected = hashlib.sha256(raw).hexdigest()
    records_before = json.loads(raw)
    write_registry_snapshot("registry-before-audit.json", raw)
    pre_frozen = snapshot(root, lib, full_nodes, toolchain, external)
    verify_compilation(records_before, prereq_nodes, pre_frozen)
    assert pre_frozen["external_snapshot"] == native_before
    write_evidence("full324-before-audit.json", pre_frozen)

if pre_rc == 0 and not pre_errors:
    pre_perform("original_verify_compilation_binds_current_322", bind_current_prerequisites)
    if not pre_errors:
        pre_perform("actual_capacity_binding_and_original_plaintext_space_guard", bind_capacity_and_check_original_audit_space)
write_evidence("prerequisite-result.json", {
    "source_pin": pin, "runner_exit_code": pre_rc, "runner_elapsed_seconds": pre_seconds,
    "original_summary": pre_summary, "postchecks": pre_checks, "postcheck_errors": pre_errors})
print(json.dumps({
    "phase": "canonical_owned_A_prerequisites_complete", "source_pin": pin,
    "runner_exit_code": pre_rc, "runner_elapsed_seconds": pre_seconds,
    "original_summary": pre_summary, "postchecks": pre_checks, "postcheck_errors": pre_errors,
    "audit_started": False,
}), flush=True)
if pre_rc != 0 or pre_errors:
    rc = pre_rc if pre_rc != 0 else 125
    write_evidence("receipt.json", {"source_pin": pin, "wrapper_exit_code": rc,
        "audit_started": False, "canonical_owned_A_passed": False,
        "reason": "Original zero-budget 322 gate, current compilation binding, or measured space guard failed",
        "prerequisite_result": file_info(out / "prerequisite-result.json"),
        "A_owned_audit_credit": False, "B_credit": False, "W_credit": False, "full324_credit": False})
    raise SystemExit(rc)

latest_before = {}
attempts_before = {}
for name in targets:
    directory = audit_root / name
    attempts_before[name] = {path.name for path in directory.glob("attempt-*") if path.is_dir()}
    latest = directory / "latest.json"
    latest_before[name] = file_info(latest) if latest.is_file() else None
    if latest.is_file():
        raw = latest.read_bytes()
        (out / "latest-before" / (name + ".json")).write_bytes(raw)
write_evidence("latest-before-index.json", latest_before)
assert digest(registry) == registry_expected
assert not summary_path.exists()

env = external.environment(dict(os.environ))
command = [sys.executable, "-B", "verification/part2/run_winner9_private_audit.py",
           *targets, "--external-snapshot", str(snapshot_path),
           "--memory-mb", "11264", "--summary-name", summary_name]
write_evidence("original-audit-command.json", {"command": command, "cwd": str(root),
    "source_pin": pin, "targets_in_original_topological_order": targets,
    "original_runner_sha256": expected["verification/part2/run_winner9_private_audit.py"],
    "original_template_sha256": expected["verification/part2/winner9_private_audit_template.lean"],
    "registry_sha256_before": registry_expected})
print(json.dumps({"phase": "canonical_owned_A_begin", "source_pin": pin,
    "targets": targets, "command": command, "summary": str(summary_path),
    "registry_sha256_before": registry_expected, "audit_started": True}), flush=True)

# Preserve the runner's stdout exactly; the unchanged runner keeps all complete
# replay, audit/type logs, Audit.lean and per-attempt receipts in its own directory.
audit_rc = None
audit_seconds = None
execution_errors = []
started = time.monotonic()
try:
    with (out / "original-runner.stdout").open("wb") as transcript:
        proc = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, bufsize=0)
        try:
            while True:
                chunk = os.read(proc.stdout.fileno(), 65536)
                if not chunk:
                    break
                transcript.write(chunk)
                transcript.flush()
                sys.stdout.buffer.write(chunk)
                sys.stdout.buffer.flush()
        finally:
            proc.stdout.close()
            audit_rc = proc.wait()
except Exception as error:
    execution_errors.append({"check": "original_audit_execution", "error": type(error).__name__ + ": " + str(error)})
audit_seconds = time.monotonic() - started

checks, errors = {}, list(execution_errors)
after_frozen = None
records_after = None
original_summary = None
captured_modules = {}

def perform(name, action):
    try:
        action()
        checks[name] = True
    except Exception as error:
        checks[name] = False
        errors.append({"check": name, "error": type(error).__name__ + ": " + str(error)})

def check_runtime_after():
    assert {path: digest(path) for path in runtime_expected} == runtime_expected
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
    assert digest(snapshot_path) == snapshot_expected

def check_native_after():
    assert external.verify() == native_before

def capture_current_snapshot():
    global after_frozen, records_after
    raw = registry.read_bytes()
    records_after = json.loads(raw)
    write_registry_snapshot("registry-after-audit.json", raw)
    current = project_nodes(root, W)
    assert list(current) == full
    assert {name: digest(node["source"]) for name, node in current.items()} == sources_before
    mark_project_nodes(current, set(external.modules))
    after_frozen = snapshot(root, lib, current, toolchain, external)
    write_evidence("full324-after-audit.json", after_frozen)
    assert hashlib.sha256(raw).hexdigest() == registry_expected, "An audit-only batch changed compilation records"
    assert after_frozen == pre_frozen, "Full324 source/object/tool/native snapshot changed during audit"

def bind_prerequisites_after():
    assert records_after is not None and after_frozen is not None
    verify_compilation(records_after, prereq_nodes, after_frozen)

def capture_original_summary():
    global original_summary
    raw = summary_path.read_bytes()
    (out / "original-summary.json").write_bytes(raw)
    original_summary = json.loads(raw)
    assert set(original_summary["modules"]) == set(targets)
    assert original_summary["requested"] == len(targets) == 1
    accepted = sum(row["accepted"] is True for row in original_summary["modules"].values())
    all_accepted = all(row["accepted"] is True for row in original_summary["modules"].values())
    assert original_summary["accepted"] == accepted
    assert original_summary["all_accepted"] == all_accepted
    assert audit_rc == int(not all_accepted), "Original audit summary and actual return code disagree"

perform("source_pin_tracked_clean_original_tools_and_repaired_sources", check_source)
perform("original_runtime_and_snapshot_bytes_unchanged", check_runtime_after)
perform("qualified_native_binding_unchanged", check_native_after)
perform("all324_source_objects_and_compile_registry_unchanged", capture_current_snapshot)
perform("original_verify_compilation_still_binds_current_322", bind_prerequisites_after)
perform("capture_original_summary_and_verify_actual_exit", capture_original_summary)

def capture_module(name):
    directory = audit_root / name
    latest = directory / "latest.json"
    raw = latest.read_bytes()
    captured_latest = out / "latest-after" / (name + ".json")
    captured_latest.write_bytes(raw)
    receipt = json.loads(raw)
    assert receipt["module"] == name
    paths = {latest}
    new_attempts = []
    for attempt in sorted(directory.glob("attempt-*")):
        if attempt.is_dir() and attempt.name not in attempts_before[name]:
            new_attempts.append(attempt.name)
            paths.update(path for path in attempt.rglob("*") if path.is_file())
    for relative, wanted_sha in receipt.get("artifacts", {}).items():
        path = root / relative
        assert path.resolve().is_relative_to(audit_root.resolve())
        paths.add(path)
        assert path.is_file() and digest(path) == wanted_sha
    for section, keys in (("replay", ("log",)), ("audit", ("log", "source"))):
        for key in keys:
            relative = receipt.get(section, {}).get(key)
            if relative:
                path = root / relative
                assert path.resolve().is_relative_to(audit_root.resolve())
                if path.is_file():
                    paths.add(path)
    artifacts = []
    for path in sorted(paths):
        assert path.resolve().is_relative_to(audit_root.resolve())
        artifacts.append(file_info(path))
    row = {"module": name, "latest_before": latest_before[name],
        "latest_after": file_info(latest), "captured_latest": file_info(captured_latest),
        "new_attempts": new_attempts, "original_files": artifacts,
        "accepted": receipt.get("accepted", False)}
    captured_modules[name] = row
    if original_summary is not None:
        assert row["accepted"] is original_summary["modules"][name]["accepted"]
        row["original_reuse_result"] = original_summary["modules"][name].get("reused")
    if receipt.get("accepted") is True:
        assert receipt["source_sha256"] == sources_before[name]
        assert after_frozen is not None and records_after is not None
        assert receipt["object_sha256"] == after_frozen["project"][name]["object_sha256"]
        assert receipt["compile_closure_signature"] == records_after[name]["closure_signature"]
        assert receipt["replay"]["exit_code"] == receipt["audit"]["exit_code"] == 0
        assert receipt["replay"]["inputs_unchanged"] is True
        assert receipt["audit"]["inputs_unchanged"] is True
        assert receipt["audit"]["memory_mb"] == 11264
        assert receipt["artifacts"], "Accepted original receipt has no complete artifact manifest"
        assert receipt["audit"]["declaration_count"] == original_summary["modules"][name]["declarations"]
        row["owned_count"] = receipt["audit"]["declaration_count"]
        row["axiom_counts"] = receipt["audit"]["axiom_counts"]

# Capture every requested target even when another target failed its original audit.
for name in targets:
    perform("capture_all_original_artifacts_" + name, lambda name=name: capture_module(name))
write_evidence("original-artifact-index.json", captured_modules)
if audit_rc == 0 and not errors:
    perform("original_full_plaintext_artifacts_exactly_match_actual_capacity", verify_original_plaintext_sizes)

def check_capacity_reference_and_free_reserve():
    assert digest(capacity_receipt_path) == capacity_receipt_sha256
    disk = os.statvfs(root)
    assert disk.f_bavail * disk.f_frsize >= minimum_free_reserve

perform("capacity_reference_unchanged_and_32MiB_reserve_preserved", check_capacity_reference_and_free_reserve)
passed = audit_rc == 0 and not errors
wrapper_rc = audit_rc if audit_rc is not None and audit_rc != 0 else (0 if passed else 125)
receipt = {
    "source_pin": pin, "full_scope": 324, "prerequisite_scope": 322,
    "ordered_fingerprint": ordered_expected, "targets": targets,
    "audit_started": True, "original_runner_exit_code": audit_rc,
    "wrapper_exit_code": wrapper_rc, "original_runner_seconds": audit_seconds,
    "original_summary": original_summary, "postchecks": checks, "postcheck_errors": errors,
    "canonical_owned_A_passed": passed,
    "capacity_binding": capacity_binding,
    "independent_replay_and_original_full_owned_CLI_preserved": True,
    "capacity_diagnostic_credit_transferred": False,
    "separate_shape_checker_credit_transferred": False,
    "shape_checker_run": False,
    "all_original_plaintext_artifacts_retained": True,
    "original_summary_file": file_info(summary_path) if summary_path.is_file() else None,
    "original_artifact_index": file_info(out / "original-artifact-index.json"),
    "original_runner_stdout": file_info(out / "original-runner.stdout") if (out / "original-runner.stdout").is_file() else None,
    "registry_sha256_before": registry_expected, "registry_sha256_after": digest(registry),
    "memory_mb": 11264, "workers": 1, "threads": 1,
    "outer_timeout_seconds": 3600, "job_memory_mb": 13107,
    "selector_run": False, "exporter_package_run": False,
    "isolated_candidate_credit_transferred": False,
    "A_owned_audit_credit": passed, "B_credit": False, "W_credit": False, "full324_credit": False,
}
write_evidence("receipt.json", receipt)
print("P24_CANONICAL_OWNED_A_DONE " + json.dumps({
    "receipt": file_info(out / "receipt.json"), "source_pin": pin,
    "original_runner_exit_code": audit_rc, "wrapper_exit_code": wrapper_rc,
    "original_runner_seconds": audit_seconds, "original_summary": original_summary,
    "postchecks": checks, "postcheck_errors": errors,
    "canonical_owned_A_passed": passed, "artifact_index": file_info(out / "original-artifact-index.json"),
    "registry_sha256_before": registry_expected, "registry_sha256_after": digest(registry),
    "A_owned_audit_credit": passed, "B_credit": False, "W_credit": False, "full324_credit": False,
}), flush=True)
raise SystemExit(wrapper_rc)
