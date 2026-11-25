#!/usr/bin/env python3
"""One input-bound local String/Char diagnostic, with complete owned audit.

Only the existing /workspace/p25-q96-20261125 worktree may advance from the
explicit previous commit to the already-fetched publication commit. Source
bytes are checked before advancement. No dependency is built or installed;
no project cache or production receipt is written. The candidate is copied
verbatim into a fresh isolated source/library pair. Acceptance, if earned,
means only its local String.ofList equality, never canonical originalText 0,
JSON parse, Q96 or P2.5. No network operation is performed by this runner.
"""

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time

ROOT = Path("/workspace/p25-q96-20261125")
RUNNER_PATH = "docs/verification/20261125-p2-5-saving16/string-char-binding/run_diagnostic.py"
CANDIDATE_PATH = "docs/verification/20261125-p2-5-saving16/string-char-binding/ImbalancedChen/P2Saving16StringCharBinding00.lean"
CANDIDATE_MANIFEST = "docs/verification/20261125-p2-5-saving16/string-char-binding/MANIFEST.json"
MODULE = "ImbalancedChen.P2Saving16StringCharBinding00"
GOAL_NAME = MODULE + ".originalStringeq00"
CANDIDATE_SHA256 = "9eee86b71a1f14dcdf3740b9faea53d5e484af727167d639ba5eff68183a023f"
ATTEMPT = ".lake/diagnostic/p25-string-char-binding-attempt001"
INPUT_MANIFEST = "docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json"
INPUT_PATH = "../goldbach-research/eighth-prefix-family-20261009-cell-00.witness.json"
INPUT_SHA256 = "360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6"
INPUT_BYTES = 53305
AUDIT_TEMPLATE = "verification/part2/winner9_private_audit_template.lean"
AUDIT_TARGET = "ImbalancedChen.P2Winner9FiniteMomentKernel"
AUDIT_DRIVER = "verification/part2/run_winner9_private_audit.py"
PYTHON_AUDIT_SOURCES = [
    "verification/part2/inspect_winner9_owner_native.py",
    "verification/part2/run_winner9_private_checks.py",
    AUDIT_DRIVER,
]
PINNED_FILES = {
    CANDIDATE_PATH: CANDIDATE_SHA256,
    CANDIDATE_MANIFEST: "a5cfa44970ec3ddd7e87e4a7f2f5e6400cf7dddfc539a63889a341acc2156043",
    INPUT_MANIFEST: "79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0",
    AUDIT_TEMPLATE: "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    AUDIT_DRIVER: "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "verification/part2/run_winner9_private_checks.py": "f7816db16309f99b6f3babbe128425c06818b3da1dec556dffffe5e8132a6314",
    "verification/part2/inspect_winner9_owner_native.py": "28fbce08aa1adcc379ee592eda3760d2465b27e784cc735497d35b3658c9e464",
    "docs/verification/20261125-p2-5-saving16/run-p25-cell00-parse-diagnostic.py": "f899171553941822f31eed55d2e47777768ab7c091b64ed98a7f365119ebd186",
}
LEAN = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
CHECKER = LEAN.with_name("leanchecker")
SYSROOT = LEAN.parent.parent
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
LEAN_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
CHECKER_SHA256 = "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
STRICT_FLAGS = [
    "-t0", "-j1", "-M11264", "-DwarningAsError=true",
    "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000",
]
NORMAL_TIMEOUT_SECONDS = 180
REPLAY_TIMEOUT_SECONDS = 180
AUDIT_TIMEOUT_SECONDS = 180
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


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
    if len(result["files"]) != 1 or sum(item.get("bytes", 0) for item in result["files"]) != 53305:
        result["errors"].append("Expected only the original cell00 input totaling 53305 bytes")
    result["all_inputs_match_manifest"] = not result["errors"]
    return result


def run_bounded(command, log_path, environment, timeout_seconds):
    started = time.monotonic()
    started_utc = utc_now()
    timed_out = False
    print("P25_STRING_CHAR_START " + json.dumps(command), flush=True)
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
                print("P25_STRING_CHAR_RUNNING_SECONDS " + str(round(time.monotonic() - started, 3)), flush=True)
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


def file_snapshot(path):
    path = Path(path)
    require(path.is_file(), "Missing frozen file: " + str(path))
    first = path.stat()
    content_hash = digest(path)
    second = path.stat()
    fields = ("st_dev", "st_ino", "st_size", "st_mtime_ns", "st_ctime_ns")
    require(tuple(getattr(first, k) for k in fields) == tuple(getattr(second, k) for k in fields),
            "File changed while hashing: " + str(path))
    return {"path": str(path), "realpath": str(path.resolve()), "is_symlink": path.is_symlink(),
            "bytes": second.st_size,
            "device": second.st_dev, "inode": second.st_ino,
            "mtime_ns": second.st_mtime_ns, "ctime_ns": second.st_ctime_ns,
            "sha256": content_hash}


def frozen_snapshot(paths, input_rows):
    return {"files": {str(p): file_snapshot(p) for p in paths},
            "input": input_snapshot(input_rows)}


def object_snapshot(lib):
    return {str(p.relative_to(lib)): file_snapshot(p)
            for p in sorted(lib.rglob("*")) if p.is_file()}


def load_original_audit_parser(tools_dir):
    # The original parser and its two top-level project imports are copied
    # verbatim. Importing their definitions does not invoke either main().
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(tools_dir))
    names = ["inspect_winner9_owner_native", "run_winner9_private_checks", "run_winner9_private_audit"]
    for name in names:
        require(name not in sys.modules, "Audit helper was preloaded from another context: " + name)
    source = tools_dir / "run_winner9_private_audit.py"
    spec = importlib.util.spec_from_file_location("run_winner9_private_audit", source)
    require(spec is not None and spec.loader is not None, "Cannot load original audit parser")
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    for name in names:
        loaded = sys.modules[name]
        require(Path(loaded.__file__).resolve() == (tools_dir / (name + ".py")).resolve(),
                "Audit helper import resolved outside the isolated copies: " + name)
    require(module.AXIOMS == ALLOWED_AXIOMS and module.TEMPLATE_TARGET == AUDIT_TARGET,
            "Original audit policy changed")
    return module.parse_audit


def run_phase(state, receipt, name, command, log, env, timeout, paths, rows,
              frozen, lib, expected_objects=None):
    before = frozen_snapshot(paths, rows)
    require(before == frozen, "Source/input/toolchain/template changed before " + name)
    before_objects = object_snapshot(lib)
    if expected_objects is not None:
        require(before_objects == expected_objects, "Object set changed before " + name)
    else:
        require(not before_objects, "Fresh normal diagnostic library is not empty")
    state[name + "_snapshot_before"] = before
    state[name + "_objects_before"] = before_objects
    state["status"] = name.upper() + "_RUNNING"
    saved(receipt, state)
    result = run_bounded(command, log, env, timeout)
    state[name] = result
    saved(receipt, state)
    after = frozen_snapshot(paths, rows)
    after_objects = object_snapshot(lib)
    result["inputs_sources_compiler_template_unchanged"] = after == frozen
    result["objects_unchanged"] = None if expected_objects is None else after_objects == expected_objects
    state[name] = result
    state[name + "_snapshot_after"] = after
    state[name + "_objects_after"] = after_objects
    saved(receipt, state)
    require(after == frozen, "Source/input/toolchain/template changed during " + name)
    if expected_objects is not None:
        require(after_objects == expected_objects, "Object set changed during " + name)
    if result["timed_out"] or result["exit_code"] != 0:
        state["status"] = name.upper() + ("_TIMEOUT" if result["timed_out"] else "_FAILED")
        return False
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("publication_commit", help="Full lowercase already-fetched publication SHA")
    parser.add_argument("previous_commit", help="Full lowercase previous SHA authorized for this worktree")
    args = parser.parse_args()
    if not ROOT.is_dir() or ROOT.is_symlink():
        print("P25_STRING_CHAR_ERROR Fixed existing worktree is absent or symlinked", file=sys.stderr)
        return 1
    out = ROOT / ATTEMPT
    if out.exists():
        print("P25_STRING_CHAR_ERROR Preserve the existing attempt: " + str(out), file=sys.stderr)
        return 1
    require(out.parent.resolve().is_relative_to(ROOT.resolve()), "Diagnostic parent leaves fixed worktree")
    out.mkdir(parents=True)
    receipt = out / "RESULT.json"
    runner_file = Path(__file__).resolve()
    state = {
        "schema": "p25-single-local-string-char-binding-diagnostic-v1",
        "status": "PREPARING", "accepted": False, "diagnostic_only": True,
        "accepted_scope": "Only the fresh local String.ofList chars00 = oldString00 equality and its complete module inventory.",
        "canonical_originalText_0_connected": False, "parse_proved": False,
        "typed_decode_proved": False, "Q96_proved": False, "P2_5_proved": False,
        "production_credit": False, "compilation_cache_credit": False,
        "full_owned_audit_started": False, "full_owned_audit_accepted": False,
        "publication_commit": args.publication_commit, "previous_commit": args.previous_commit,
        "runner_path": str(runner_file), "runner_sha256": digest(runner_file),
        "candidate_path": CANDIDATE_PATH, "candidate_sha256": CANDIDATE_SHA256,
        "module": MODULE, "target": GOAL_NAME,
        "strict_flags": STRICT_FLAGS, "source_effective_maxRecDepth": 1000000,
        "audit_effective_maxRecDepth": 50000,
        "source_options_boundary": "Candidate source-local maxRecDepth 1000000 overrides CLI 50000 in that module only; the unchanged audit template has no such override.",
        "phase_wall_limits_seconds": {"normal": NORMAL_TIMEOUT_SECONDS, "replay": REPLAY_TIMEOUT_SECONDS, "audit": AUDIT_TIMEOUT_SECONDS},
        "heap_boundary": "Normal and audit use original -M11264. leanchecker keeps its original --verbose command with a 180-second wall bound; the service enforces the job memory boundary.",
        "read_window_condition": "Both source elaborators read the same original cell00 path. No runner child writes it. Original hash and physical identity are checked before/after, assuming no out-of-band host write during this task-owned read window.",
        "replay_boundary": "The independent checker reads the fresh bound object, not the original JSON. Audit checks all serialized/environment-owned names including private/generated declarations.",
        "standard_library_boundary": "Only the fixed Lean toolchain is used; no Mathlib or other ImbalancedChen library path is added. Direct standard-library objects and compiler/checker binaries are frozen; a new full standard-library source census is not claimed.",
        "started_utc": utc_now(),
    }
    saved(receipt, state)
    try:
        for value in [args.publication_commit, args.previous_commit]:
            require(re.fullmatch(r"[0-9a-f]{40}", value) is not None, "Expected full lowercase commit SHAs")
        require(Path(output(["git", "rev-parse", "--show-toplevel"], ROOT)).resolve() == ROOT.resolve(),
                "Fixed directory is not the intended worktree root")
        initial_head = output(["git", "rev-parse", "HEAD"], ROOT)
        state["worktree_head_before"] = initial_head
        require(initial_head in [args.previous_commit, args.publication_commit], "Unexpected current worktree HEAD")
        require(not output(["git", "status", "--porcelain", "--untracked-files=no"], ROOT),
                "Tracked worktree is not clean")
        for value in [args.previous_commit, args.publication_commit]:
            subprocess.check_call(["git", "cat-file", "-e", value + "^{commit}"], cwd=ROOT)
        subprocess.check_call(["git", "merge-base", "--is-ancestor", args.previous_commit,
                               args.publication_commit], cwd=ROOT)
        published_runner = subprocess.check_output(["git", "show", args.publication_commit + ":" + RUNNER_PATH], cwd=ROOT)
        require(digest_bytes(published_runner) == state["runner_sha256"], "Executing runner differs from publication")
        published = {}
        for relative, expected in PINNED_FILES.items():
            raw = subprocess.check_output(["git", "show", args.publication_commit + ":" + relative], cwd=ROOT)
            require(digest_bytes(raw) == expected, "Published source/policy differs: " + relative)
            published[relative] = raw
        source = published[CANDIDATE_PATH]
        require(re.findall(rb"(?m)^import (\S+)$", source) == [b"Lean"], "Candidate must import only Lean")
        require(published[AUDIT_TEMPLATE].count(AUDIT_TARGET.encode()) == 2, "Audit template target count differs")
        input_manifest = json.loads(published[INPUT_MANIFEST])
        rows = [row for row in input_manifest["saving16_inputs"] if row["install_path"] == INPUT_PATH]
        require(len(rows) == 1 and rows[0]["bytes"] == INPUT_BYTES and rows[0]["sha256"] == INPUT_SHA256,
                "Original manifest cell00 binding differs")
        before_advance = input_snapshot(rows)
        state["input_snapshot_before_advance"] = before_advance
        require(before_advance["all_inputs_match_manifest"], "Original cell00 snapshot failed")
        require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256,
                "Compiler/checker binary differs")
        version = output([str(LEAN), "--version"])
        require("4.33.0-rc1" in version and LEAN_COMMIT in version, "Lean version differs")
        state["source_first_verified"] = {RUNNER_PATH: state["runner_sha256"], **PINNED_FILES}
        state["worktree_advance_command"] = ["git", "checkout", "--detach", args.publication_commit]
        state["status"] = "ADVANCING_ONLY_FIXED_TASK_WORKTREE"
        saved(receipt, state)
        if initial_head != args.publication_commit:
            subprocess.check_call(state["worktree_advance_command"], cwd=ROOT)
        require(output(["git", "rev-parse", "HEAD"], ROOT) == args.publication_commit, "Worktree advancement failed")
        require(not output(["git", "status", "--porcelain", "--untracked-files=no"], ROOT),
                "Tracked worktree changed during advancement")
        require(digest(ROOT / RUNNER_PATH) == state["runner_sha256"], "Published runner changed during advancement")
        for relative, expected in PINNED_FILES.items():
            require(digest(ROOT / relative) == expected, "Published file changed during advancement: " + relative)
        after_advance = input_snapshot(rows)
        state["input_snapshot_after_advance"] = after_advance
        require(after_advance == before_advance, "Original cell00 changed during advancement")
        state["worktree_head_after"] = args.publication_commit

        src, lib, audit_dir, tools_dir = (out / n for n in ["src", "lib", "audit", "audit-tools"])
        for directory in [src, lib, audit_dir, tools_dir]:
            directory.mkdir()
        module_relative = Path(MODULE.replace(".", "/"))
        copied_source = src / module_relative.with_suffix(".lean")
        probe_object = lib / module_relative.with_suffix(".olean")
        copied_source.parent.mkdir(parents=True)
        probe_object.parent.mkdir(parents=True)
        copied_source.write_bytes(source)
        require(digest(copied_source) == CANDIDATE_SHA256 and not probe_object.exists(),
                "Candidate copy differs or object is not fresh")
        runner_copy = out / "EXECUTED_RUNNER.py"
        runner_copy.write_bytes(published_runner)
        copied_tools = []
        for relative in [*PYTHON_AUDIT_SOURCES, AUDIT_TEMPLATE]:
            target = tools_dir / Path(relative).name
            target.write_bytes(published[relative])
            require(digest(target) == PINNED_FILES[relative], "Audit source copy differs")
            copied_tools.append(target)
        template = published[AUDIT_TEMPLATE]
        audit_source = audit_dir / "Audit.lean"
        audit_source.write_bytes(template.replace(AUDIT_TARGET.encode(), MODULE.encode()))
        require(audit_source.read_bytes() == template.replace(AUDIT_TARGET.encode(), MODULE.encode()),
                "Audit source differs from the original target-only substitution")
        standard_objects = [SYSROOT / "lib/lean/Lean.olean", SYSROOT / "lib/lean/Lean/Util/CollectAxioms.olean"]
        require(all(p.is_file() for p in standard_objects), "Fixed standard Lean objects are missing")
        paths = list(dict.fromkeys([runner_file, ROOT / RUNNER_PATH, *[ROOT / p for p in PINNED_FILES],
                                   copied_source, runner_copy, audit_source, *copied_tools,
                                   LEAN, CHECKER, *standard_objects]))
        frozen = frozen_snapshot(paths, rows)
        expected_frozen_hashes = {str(ROOT / relative): expected for relative, expected in PINNED_FILES.items()}
        expected_frozen_hashes.update({str(runner_file): state["runner_sha256"],
            str(ROOT / RUNNER_PATH): state["runner_sha256"], str(runner_copy): state["runner_sha256"],
            str(copied_source): CANDIDATE_SHA256,
            str(audit_source): digest_bytes(template.replace(AUDIT_TARGET.encode(), MODULE.encode())),
            str(LEAN): LEAN_SHA256, str(CHECKER): CHECKER_SHA256})
        expected_frozen_hashes.update({str(tools_dir / Path(relative).name): PINNED_FILES[relative]
                                      for relative in [*PYTHON_AUDIT_SOURCES, AUDIT_TEMPLATE]})
        for path, expected in expected_frozen_hashes.items():
            require(frozen["files"][path]["sha256"] == expected,
                    "Frozen source/compiler/policy differs from its checked pin: " + path)
        require(frozen["input"] == before_advance, "Original input changed before compilation")
        parse_audit = load_original_audit_parser(tools_dir)
        require(frozen_snapshot(paths, rows) == frozen, "Audit helper import changed frozen inputs")
        environment = dict(os.environ)
        environment.pop("LEAN_SRC_PATH", None)
        environment["LEAN_SYSROOT"] = str(SYSROOT)
        environment["LEAN_PATH"] = str(lib)
        state.update({"frozen_context": frozen, "lean_version": version,
                      "approved_LEAN_PATH": environment["LEAN_PATH"], "LEAN_SYSROOT": str(SYSROOT),
                      "isolated_source_root": str(src), "isolated_library": str(lib),
                      "audit_source": str(audit_source), "audit_source_sha256": digest(audit_source),
                      "audit_template_target_only_replacement_count": 2,
                      "audit_parser_source": str(tools_dir / Path(AUDIT_DRIVER).name)})
        saved(receipt, state)

        normal = [str(LEAN), *STRICT_FLAGS, "--root=" + str(src),
                  "-o", str(probe_object), str(copied_source)]
        if not run_phase(state, receipt, "normal", normal, out / "NORMAL.log", environment,
                         NORMAL_TIMEOUT_SECONDS, paths, rows, frozen, lib):
            return 1
        require(probe_object.is_file() and probe_object.stat().st_size > 0, "No fresh diagnostic object")
        objects = object_snapshot(lib)
        state.update({"fresh_input_to_object_binding": True, "bound_objects": objects,
                      "primary_object_sha256": digest(probe_object)})
        saved(receipt, state)
        replay = [str(CHECKER), "--verbose", MODULE]
        if not run_phase(state, receipt, "replay", replay, out / "REPLAY.log", environment,
                         REPLAY_TIMEOUT_SECONDS, paths, rows, frozen, lib, objects):
            return 1
        state["full_owned_audit_started"] = True
        audit_command = [str(LEAN), *STRICT_FLAGS, "--root=" + str(audit_dir), str(audit_source)]
        if not run_phase(state, receipt, "audit", audit_command, out / "AUDIT.log", environment,
                         AUDIT_TIMEOUT_SECONDS, paths, rows, frozen, lib, objects):
            return 1
        parsed = parse_audit(out / "AUDIT.log", MODULE, {MODULE})
        require(GOAL_NAME in {record["name"] for record in parsed["declarations"]},
                "The sole binding goal is absent from the complete owned inventory")
        saved(out / "OWNED_DECLARATIONS.json", parsed)
        (out / "TYPES.txt").write_text("\n\n".join(
            record["name"] + "\n" + record["type"] for record in parsed["declarations"]) + "\n")
        require(frozen_snapshot(paths, rows) == frozen and object_snapshot(lib) == objects,
                "Frozen context changed while processing full owned evidence")
        state["audit"].update({"declaration_count": parsed["declaration_count"],
                               "axiom_counts": parsed["axiom_counts"],
                               "serialized_environment_complete": True,
                               "private_generated_included": True,
                               "unsafe_partial_axiom_flags_all_false": True})
        state["artifacts"] = {str(p.relative_to(out)): digest(p) for p in
                              [out / "NORMAL.log", out / "REPLAY.log", out / "AUDIT.log",
                               out / "OWNED_DECLARATIONS.json", out / "TYPES.txt", audit_source,
                               copied_source, runner_copy, *copied_tools]}
        require(output(["git", "rev-parse", "HEAD"], ROOT) == args.publication_commit
                and not output(["git", "status", "--porcelain", "--untracked-files=no"], ROOT),
                "Published worktree changed before final acceptance")
        state["full_owned_audit_accepted"] = True
        state["accepted"] = True
        state["status"] = "LOCAL_STRING_CHAR_BINDING_NORMAL_REPLAY_FULL_OWNED_ACCEPTED"
        return 0
    except Exception as error:
        state["status"] = "PRECONDITION_OR_EVIDENCE_BINDING_FAILED"
        state["error"] = str(error)
        print("P25_STRING_CHAR_ERROR " + str(error), file=sys.stderr, flush=True)
        return 1
    finally:
        state["ended_utc"] = utc_now()
        saved(receipt, state)
        print("P25_STRING_CHAR_RESULT " + json.dumps({key: state[key] for key in [
            "status", "accepted", "full_owned_audit_started", "full_owned_audit_accepted",
            "canonical_originalText_0_connected", "parse_proved", "Q96_proved", "P2_5_proved",
        ]}), flush=True)
        print("P25_STRING_CHAR_RECEIPT " + str(receipt) + " " + digest(receipt), flush=True)


if __name__ == "__main__":
    sys.exit(main())
