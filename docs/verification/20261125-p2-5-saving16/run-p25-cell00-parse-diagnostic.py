#!/usr/bin/env python3
"""One bounded diagnostic of the unchanged original cell-00 parse/decode.

Run from the existing P3 environment. Only the task's fixed worktree may
advance from 845f633 to the caller's already-fetched publication commit,
after checking unchanged finite/parser/floor source bytes. No inputs or
dependencies are installed or built, and normal compile records are not
updated. All new outputs belong to one diagnostic directory. Even a
successful optional replay is NOT full-owned acceptance.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


ROOT = Path("/workspace/p25-q96-20261125")
SOURCE_COMMIT = "845f6336d06729857f1f4f87102202943c79a650"
SOURCE_PATH = "ImbalancedChen/P2OriginalSaving16FiniteArchive.lean"
RUNNER_PATH = "docs/verification/20261125-p2-5-saving16/run-p25-cell00-parse-diagnostic.py"
SOURCE_SHA256 = "72824a189dd65b29f0f340918ff867a1e905959e8e60e683a797226923d7e01d"
PREFIX_SHA256 = "2f83fc7ad18612c33b16d2949f19e99128f9cde3d87e663c084da3168bf35fb6"
PREFIX_BYTES = 7017
GUARD_MARKER = (
    b"/-- Closed original-file parse-success guard, UNEVALUATED. No parse\n"
    b"success premise or external PASS record is introduced. -/\n"
    b"theorem original_parse_success_tag :"
)
DIAGNOSTIC_MODULE = "P25Cell00ParseDiagnostic"
DIAGNOSTIC_SUFFIX = (
    b"/-- Diagnostic only: the unchanged parser and decoder on original cell 00. -/\n"
    b"theorem cell00_parse_success_diagnostic :\n"
    b"    parsedCellSuccess (0 : Fin 14) = true := by\n"
    b"  decide +kernel\n\n"
    b"end\n"
    b"end ImbalancedChen.P2OriginalSaving16OriginalArchive\n"
)
ATTEMPT = ".lake/diagnostic/p25-cell00-parse-845f633-attempt001"
MANIFEST_PATH = "docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json"
MANIFEST_SHA256 = "79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0"
MATHLIB = Path("/mathlib")
MATHLIB_PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
LEAN = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
CHECKER = LEAN.with_name("leanchecker")
LEAN_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
CHECKER_SHA256 = "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
PROJECT_LIB = ROOT / ".lake/p2-private/lib"
BASELINE_LIB = Path("/workspace/p25-q96-baseline-8657/.lake/build/lib/lean")
MATHLIB_PATHS = ["/mathlib/.lake/build/lib/lean"] + [
    f"/mathlib/.lake/packages/{package}/.lake/build/lib/lean"
    for package in ["plausible", "LeanSearchClient", "importGraph", "proofwidgets", "aesop", "Qq", "batteries"]
]
STRICT_FLAGS = [
    "-t0", "-j1", "-M11264", "-DwarningAsError=true",
    "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000",
]
COMPILE_TIMEOUT_SECONDS = 180
REPLAY_TIMEOUT_SECONDS = 180
DEPENDENCIES = {
    "ImbalancedChen.P2OriginalSaving19SourceJson": {
        "source_sha256": "d58e22ba7e2d92b6c9f2d139993361ae9b827d25d6869fcf38f3837ba7bc3d02",
        "object_sha256": "50b1caec038208d3becd6cbef3a318b1d2966add295c060ad28d8999e1aa64e7",
        "closure_signature": "a10f02a0c330018bbe871da38adf5fb2f88b4c7d0a7994bf334ae8e4701e1f20",
        "owned_declarations": 122,
    },
    "ImbalancedChen.P2OriginalSaving16Q96FloorCore": {
        "source_sha256": "9a456807e6c3a167fd12c1c6e5db492d6c54fd700a1de122ea492774f697c778",
        "object_sha256": "720df453f67d6650c195b737357d87aafb511b10a87dbf8654ae2fc6d9e712b9",
        "closure_signature": "b6b656dea45d9be757d6aed80b3fbb6275b0935824e538056f14066a2d775597",
        "owned_declarations": 1,
    },
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest_bytes(value):
    return hashlib.sha256(value).hexdigest()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def output(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def saved(path, value):
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    temporary.replace(path)


def extract_diagnostic(source):
    require(digest_bytes(source) == SOURCE_SHA256, "Pinned finite source SHA differs")
    require(source.count(GUARD_MARKER) == 1, "Expected exactly one original guard marker")
    prefix = source[:source.index(GUARD_MARKER)]
    require(len(prefix) == PREFIX_BYTES and digest_bytes(prefix) == PREFIX_SHA256,
            "Original parser/decoder prefix differs")
    require(b"theorem original_parse_success_tag" not in prefix, "Original full guard entered prefix")
    require(b"def physicalVolumeQ" not in prefix, "Geometry entered diagnostic prefix")
    return prefix + DIAGNOSTIC_SUFFIX


def input_snapshot(rows):
    data_path = ROOT / "../goldbach-research"
    data_dir = data_path.resolve()
    result = {
        "cwd": str(ROOT), "directory": str(data_dir),
        "directory_realpath": str(data_dir.resolve()),
        "directory_identity": None, "files": [], "errors": [],
    }
    if data_path.is_symlink():
        result["errors"].append("Input directory is a symlink")
    try:
        directory = data_dir.stat()
        result["directory_identity"] = {
            "device": directory.st_dev, "inode": directory.st_ino,
            "mtime_ns": directory.st_mtime_ns, "ctime_ns": directory.st_ctime_ns,
        }
    except OSError as error:
        result["errors"].append(str(error))
    for row in rows:
        path = ROOT / row["install_path"]
        item = {"install_path": row["install_path"], "realpath": str(path.resolve())}
        try:
            if path.is_symlink():
                result["errors"].append("Input file is a symlink: " + str(path))
            stat = path.stat()
            actual = digest(path)
            item.update({
                "bytes": stat.st_size, "sha256": actual,
                "device": stat.st_dev, "inode": stat.st_ino,
                "mtime_ns": stat.st_mtime_ns, "ctime_ns": stat.st_ctime_ns,
            })
            if stat.st_size != row["bytes"] or actual != row["sha256"]:
                result["errors"].append("Original input differs: " + str(path))
        except OSError as error:
            item["error"] = str(error)
            result["errors"].append(str(error))
        result["files"].append(item)
    if len(result["files"]) != 14 or sum(item.get("bytes", 0) for item in result["files"]) != 93508187:
        result["errors"].append("Expected fourteen original inputs totaling 93508187 bytes")
    result["all_inputs_match_manifest"] = not result["errors"]
    return result


def dependency_snapshot():
    records_path = ROOT / ".lake/p2-private/records.json"
    records = json.loads(records_path.read_text())
    result = {}
    for module, expected in DEPENDENCIES.items():
        source = ROOT / (module.replace(".", "/") + ".lean")
        obj = PROJECT_LIB / (module.replace(".", "/") + ".olean")
        receipt_path = ROOT / ".lake/p2-private/audit" / module / "latest.json"
        receipt = json.loads(receipt_path.read_text())
        record = records.get(module, {})
        require(digest(source) == expected["source_sha256"], "Dependency source differs: " + module)
        require(digest(obj) == expected["object_sha256"], "Dependency object differs: " + module)
        require(record.get("exit_code") == 0 and record.get("source_sha256") == expected["source_sha256"]
                and record.get("object_sha256") == expected["object_sha256"]
                and record.get("closure_signature") == expected["closure_signature"]
                and record.get("deps") == {}, "Dependency compile record is not the accepted exact object: " + module)
        require(receipt.get("accepted") is True and receipt.get("module") == module
                and receipt.get("source_sha256") == expected["source_sha256"]
                and receipt.get("object_sha256") == expected["object_sha256"]
                and receipt.get("compile_closure_signature") == expected["closure_signature"],
                "Dependency accepted receipt differs: " + module)
        for phase in ["replay", "audit"]:
            require(receipt.get(phase, {}).get("exit_code") == 0
                    and receipt.get(phase, {}).get("inputs_unchanged") is True,
                    "Dependency " + phase + " did not pass: " + module)
        require(receipt["audit"].get("declaration_count") == expected["owned_declarations"],
                "Dependency full-owned declaration count differs: " + module)
        result[module] = {
            "source": str(source), "source_sha256": digest(source),
            "object": str(obj), "object_sha256": digest(obj),
            "compile_record": record, "receipt_path": str(receipt_path),
            "receipt_sha256": digest(receipt_path), "receipt": receipt,
        }
    return result


def run_bounded(command, log_path, environment, timeout_seconds):
    started = time.monotonic()
    started_utc = utc_now()
    timed_out = False
    print("P25_CELL00_START " + json.dumps(command), flush=True)
    with log_path.open("w") as log:
        proc = subprocess.Popen(command, cwd=ROOT, env=environment,
                                stdout=log, stderr=subprocess.STDOUT)
        while True:
            remaining = timeout_seconds - (time.monotonic() - started)
            if remaining <= 0:
                timed_out = True
                proc.kill()
                proc.wait()
                break
            try:
                proc.wait(timeout=min(30, remaining))
                break
            except subprocess.TimeoutExpired:
                print("P25_CELL00_RUNNING_SECONDS " + str(round(time.monotonic() - started, 3)), flush=True)
    result = {
        "command": command, "cwd": str(ROOT), "started_utc": started_utc,
        "seconds": round(time.monotonic() - started, 3),
        "exit_code": proc.returncode, "timed_out": timed_out,
        "wall_timeout_seconds": timeout_seconds,
        "log": str(log_path), "log_sha256": digest(log_path),
        "runner_children_peak_rss_kib_so_far": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
    }
    print(log_path.read_text(errors="replace")[-24000:], flush=True)
    return result


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("publication_commit", help="Full SHA of the already-fetched runner publication commit")
    args.add_argument("--replay", action="store_true",
                      help="After successful bound compilation, run one independent leanchecker replay; still no full-owned acceptance")
    options = args.parse_args()
    if not ROOT.is_dir():
        print("P25_CELL00_ERROR Existing task worktree is missing; no location exists for its receipt", file=sys.stderr)
        return 1
    out = ROOT / ATTEMPT
    if out.exists():
        print("P25_CELL00_ERROR Diagnostic attempt exists; preserve and inspect " + str(out), file=sys.stderr)
        return 1
    out.mkdir(parents=True)
    receipt_path = out / "DIAGNOSTIC_RESULT.json"
    state = {
        "schema": "p25-original-cell00-parse-diagnostic-v1",
        "status": "PREPARING", "accepted": False, "diagnostic_only": True,
        "full_owned_audit_performed": False, "full_fourteen_parse_proved": False,
        "original_arithmetic_guards_started": False, "started_utc": utc_now(),
        "runner_path": str(Path(__file__).resolve()), "runner_sha256": digest(__file__),
        "publication_commit": options.publication_commit,
        "source_commit": SOURCE_COMMIT, "original_source": SOURCE_PATH,
        "original_source_sha256": SOURCE_SHA256, "prefix_sha256": PREFIX_SHA256,
        "prefix_bytes": PREFIX_BYTES, "guard_marker": GUARD_MARKER.decode(),
        "diagnostic_module": DIAGNOSTIC_MODULE,
        "diagnostic_statement": "ImbalancedChen.P2OriginalSaving16OriginalArchive.parsedCellSuccess (0 : Fin 14) = true",
        "strict_flags": STRICT_FLAGS, "replay_requested": options.replay,
        "boundary": "Only a diagnostic of the unchanged pure parser plus decoder on original cell 00. All fourteen original texts are read and bound. Success gives no whole-family, Q96, arithmetic, full-owned, or final-P2.5 acceptance.",
        "read_window_condition": "No runner subprocess writes original inputs. The source reader emits the original String literals. Before/after hashes and physical identities assume the same task-owned no-out-of-band-write read window as the existing finite runner.",
        "replay_boundary": "Optional leanchecker checks the fresh diagnostic object containing the bound literals; it does not read JSON again. Full-owned audit is not performed by this diagnostic.",
    }
    saved(receipt_path, state)
    try:
        publication = options.publication_commit
        require(len(publication) == 40 and all(c in "0123456789abcdef" for c in publication),
                "Expected one full lowercase publication commit SHA")
        initial_head = output(["git", "rev-parse", "HEAD"], ROOT)
        state["worktree_head_before"] = initial_head
        saved(receipt_path, state)
        require(initial_head in [SOURCE_COMMIT, publication], "Unexpected HEAD in the task's fixed worktree")
        require(not output(["git", "status", "--porcelain", "--untracked-files=no"], ROOT),
                "Tracked worktree changes must be reviewed before diagnostic advancement")
        source = subprocess.check_output(["git", "show", SOURCE_COMMIT + ":" + SOURCE_PATH], cwd=ROOT)
        diagnostic = extract_diagnostic(source)
        state["diagnostic_source_sha256"] = digest_bytes(diagnostic)
        require(digest(ROOT / SOURCE_PATH) == SOURCE_SHA256, "Current finite source differs from pinned 845f633")
        require(output(["git", "rev-parse", "HEAD"], MATHLIB) == MATHLIB_PIN, "Mathlib pin differs")
        require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256, "Compiler/checker binary differs")
        version = output([str(LEAN), "--version"])
        require("4.33.0-rc1" in version and LEAN_COMMIT in version, "Lean version differs")
        require(all(Path(path).is_dir() for path in MATHLIB_PATHS), "Missing approved Mathlib package path")
        require(not BASELINE_LIB.exists(), "Unexpected objects in the intentionally empty isolated baseline")
        manifest_path = ROOT / MANIFEST_PATH
        require(digest(manifest_path) == MANIFEST_SHA256, "Original input manifest differs")
        rows = json.loads(manifest_path.read_text())["saving16_inputs"]
        before = input_snapshot(rows)
        state["input_snapshot_before"] = before
        saved(receipt_path, state)
        require(before["all_inputs_match_manifest"], "Original input snapshot failed; see saved file evidence")
        dependencies_before = dependency_snapshot()
        state["dependencies_before"] = dependencies_before
        saved(receipt_path, state)
        # No network operation is performed. The publishing bootstrap must have
        # already fetched this commit into the shared object store.
        subprocess.check_call(["git", "cat-file", "-e", publication + "^{commit}"], cwd=ROOT)
        subprocess.check_call(["git", "merge-base", "--is-ancestor", SOURCE_COMMIT, publication], cwd=ROOT)
        published_runner = subprocess.check_output(["git", "show", publication + ":" + RUNNER_PATH], cwd=ROOT)
        require(digest_bytes(published_runner) == state["runner_sha256"], "Executing runner differs from publication")
        for module, expected in DEPENDENCIES.items():
            relative = module.replace(".", "/") + ".lean"
            published = subprocess.check_output(["git", "show", publication + ":" + relative], cwd=ROOT)
            require(digest_bytes(published) == expected["source_sha256"], "Publication changes an accepted dependency: " + module)
        published_finite = subprocess.check_output(["git", "show", publication + ":" + SOURCE_PATH], cwd=ROOT)
        require(digest_bytes(published_finite) == SOURCE_SHA256, "Publication changes the original finite source")
        published_manifest = subprocess.check_output(["git", "show", publication + ":" + MANIFEST_PATH], cwd=ROOT)
        require(digest_bytes(published_manifest) == MANIFEST_SHA256, "Publication changes the input manifest")
        state["status"] = "ADVANCING_ONLY_TASK_WORKTREE"
        state["worktree_advance_command"] = ["git", "checkout", "--detach", publication]
        saved(receipt_path, state)
        if initial_head != publication:
            subprocess.check_call(state["worktree_advance_command"], cwd=ROOT)
        state["worktree_head_after"] = output(["git", "rev-parse", "HEAD"], ROOT)
        require(state["worktree_head_after"] == publication, "Worktree advance did not select publication")
        require(digest(ROOT / SOURCE_PATH) == SOURCE_SHA256, "Finite source changed during worktree advance")
        advanced_inputs = input_snapshot(rows)
        state["input_snapshot_after_advance"] = advanced_inputs
        saved(receipt_path, state)
        require(advanced_inputs == before and dependency_snapshot() == dependencies_before,
                "Original inputs or accepted dependencies changed during advancement")
        source_dir = out / "src"
        lib = out / "lib"
        source_dir.mkdir()
        lib.mkdir()
        # A distinct top-level module avoids shadowing the ImbalancedChen package
        # root; Lean does not use later paths as per-file fallbacks in one package.
        probe_source = source_dir / (DIAGNOSTIC_MODULE + ".lean")
        probe_object = lib / (DIAGNOSTIC_MODULE + ".olean")
        probe_source.write_bytes(diagnostic)
        environment = dict(os.environ)
        environment["LEAN_PATH"] = ":".join([str(lib), str(PROJECT_LIB), str(BASELINE_LIB), *MATHLIB_PATHS])
        state.update({
            "lean_version": version, "lean_sha256": digest(LEAN), "leanchecker_sha256": digest(CHECKER),
            "mathlib_pin": MATHLIB_PIN, "approved_LEAN_PATH": environment["LEAN_PATH"],
            "manifest_sha256": MANIFEST_SHA256, "input_snapshot_before": before,
            "dependencies_before": dependencies_before, "diagnostic_source": str(probe_source),
            "diagnostic_object": str(probe_object), "status": "DIAGNOSTIC_STRICT_COMPILE_RUNNING",
        })
        saved(receipt_path, state)
        command = [str(LEAN), *STRICT_FLAGS, "--root=" + str(source_dir),
                   "-o", str(probe_object), str(probe_source)]
        state["compile"] = run_bounded(command, out / "STRICT_COMPILE.log", environment, COMPILE_TIMEOUT_SECONDS)
        saved(receipt_path, state)
        after = input_snapshot(rows)
        state["input_snapshot_after_compile"] = after
        saved(receipt_path, state)
        dependencies_after = dependency_snapshot()
        state.update({"input_snapshot_after_compile": after, "dependencies_after_compile": dependencies_after,
                      "inputs_unchanged_through_compile": after == before,
                      "dependencies_unchanged_through_compile": dependencies_after == dependencies_before})
        require(after == before and dependencies_after == dependencies_before, "Inputs or accepted dependencies changed during diagnostic")
        require(digest(probe_source) == digest_bytes(diagnostic)
                and digest(ROOT / SOURCE_PATH) == SOURCE_SHA256, "Diagnostic or production source changed during compile")
        require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256, "Compiler/checker changed during compile")
        if state["compile"]["exit_code"] != 0 or state["compile"]["timed_out"]:
            state["status"] = "DIAGNOSTIC_COMPILE_TIMEOUT" if state["compile"]["timed_out"] else "DIAGNOSTIC_COMPILE_FAILED"
            return 1
        require(probe_object.is_file() and probe_object.stat().st_size > 0, "Successful compile did not create a fresh diagnostic object")
        object_sha = digest(probe_object)
        state.update({"fresh_data_to_diagnostic_object_bound": True,
                      "diagnostic_object_sha256": object_sha,
                      "diagnostic_object_bytes": probe_object.stat().st_size,
                      "status": "DIAGNOSTIC_COMPILE_PASSED_NOT_FULL_OWNED_ACCEPTED"})
        saved(receipt_path, state)
        if options.replay:
            state["status"] = "DIAGNOSTIC_KERNEL_REPLAY_RUNNING"
            saved(receipt_path, state)
            state["replay"] = run_bounded([str(CHECKER), "--verbose", DIAGNOSTIC_MODULE],
                                          out / "KERNEL_REPLAY.log", environment, REPLAY_TIMEOUT_SECONDS)
            saved(receipt_path, state)
            final = input_snapshot(rows)
            state["input_snapshot_after_replay"] = final
            saved(receipt_path, state)
            dependencies_final = dependency_snapshot()
            state.update({"input_snapshot_after_replay": final, "dependencies_after_replay": dependencies_final,
                          "inputs_unchanged_through_replay": final == before,
                          "dependencies_unchanged_through_replay": dependencies_final == dependencies_before})
            require(final == before and dependencies_final == dependencies_before, "Inputs/dependencies changed during replay")
            require(digest(probe_object) == object_sha and digest(probe_source) == digest_bytes(diagnostic)
                    and digest(ROOT / SOURCE_PATH) == SOURCE_SHA256, "Diagnostic object/source or production source changed during replay")
            require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256, "Compiler/checker changed during replay")
            if state["replay"]["exit_code"] != 0 or state["replay"]["timed_out"]:
                state["status"] = "DIAGNOSTIC_REPLAY_TIMEOUT" if state["replay"]["timed_out"] else "DIAGNOSTIC_REPLAY_FAILED"
                return 1
            state["status"] = "DIAGNOSTIC_COMPILE_AND_REPLAY_PASSED_NOT_FULL_OWNED_ACCEPTED"
        return 0
    except Exception as error:
        state["status"] = "DIAGNOSTIC_PRECONDITION_OR_BINDING_FAILED"
        state["error"] = str(error)
        print("P25_CELL00_ERROR " + str(error), file=sys.stderr, flush=True)
        return 1
    finally:
        state["ended_utc"] = utc_now()
        saved(receipt_path, state)
        print("P25_CELL00_RESULT " + json.dumps({key: state[key] for key in [
            "status", "accepted", "diagnostic_only", "full_owned_audit_performed",
            "full_fourteen_parse_proved", "original_arithmetic_guards_started",
        ]}), flush=True)
        print("P25_CELL00_RECEIPT " + str(receipt_path) + " " + digest(receipt_path), flush=True)


if __name__ == "__main__":
    sys.exit(main())
