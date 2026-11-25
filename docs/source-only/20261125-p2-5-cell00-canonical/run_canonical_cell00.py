#!/usr/bin/env python3
"""Two isolated cell00 stages; reuse accepted objects without cache adoption.

This draft is deliberately blocked by NOT_READY Input/Decoder evidence pins.
After evidence is filled and published, only the fixed existing P3 worktree
may advance from PREVIOUS_COMMIT. No network, production installation, cache
cleanup, dependency compile, or private-record mutation occurs. Each stage
uses its own single ImbalancedChen library, exact copies of accepted objects,
and the original strict normal/replay/complete-owned gates.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path("/workspace/p25-q96-20261125")
PREVIOUS_COMMIT = "448e03d6ce02fd7d3b8d008defcd5ffffc4fc426"
PACKAGE = "docs/source-only/20261125-p2-5-cell00-canonical"
RUNNER_PATH = PACKAGE + "/run_canonical_cell00.py"
RUNNER_MANIFEST = PACKAGE + "/RUNNER_MANIFEST.json"
SOURCE_MANIFEST = PACKAGE + "/MANIFEST.json"
SOURCE_MANIFEST_SHA256 = "ff0e820084853fbcc8f81a02c04d2d11d49c9a7a65ac93bd2b96773adb0744d9"
ATTEMPT = ".lake/diagnostic/p25-cell00-canonical-attempt001"
INPUT_MANIFEST = "docs/verification/20261125-p2-5-saving16/Q96_EXISTING_INPUTS_AND_SOURCES.json"
INPUT_MANIFEST_SHA256 = "79404a0f8ed17c2d49fd377363a5169936628ff88e8e7fdd6d5165c8c6a917e0"
BASE_RUNNER = "docs/verification/20261125-p2-5-saving16/string-char-binding/attempt003/run_diagnostic.py"
BASE_RUNNER_SHA256 = "04873a54e94bc5d923bab8446f898584f2a50e3179f8124d8a5fc1248b0fe709"
INPUT_RUNNER = "docs/source-only/20261125-p2-5-decoder/run_unguarded_sources.py"
INPUT_RUNNER_SHA256 = "30350d5baac2abfd9491d01f1d7fc02230ef44fc7e641830af378b8ad1bb4a59"
LEAN = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
CHECKER = LEAN.with_name("leanchecker")
LEAN_SHA256 = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
CHECKER_SHA256 = "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
MATHLIB = Path("/mathlib")
MATHLIB_PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
STRICT_FLAGS = ["-t0", "-j1", "-M11264", "-DwarningAsError=true",
                "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
TIMEOUT_SECONDS = 180
RAW = "ImbalancedChen.P2Saving16StringCharBinding00"
INPUT = "ImbalancedChen.P2OriginalSaving16OriginalInput"
DECODER = "ImbalancedChen.P2OriginalSaving16Decoder"
CANONICAL = "ImbalancedChen.P2Saving16CanonicalCell00Binding"
CONSUMER = "ImbalancedChen.P2Saving16CanonicalCell00ParseDiagnostic"
CANONICAL_SHA256 = "a5864c739608bda635f88cf7cf3e39481d63b67c4d279f11b45b2cb99e8290dc"
CONSUMER_SHA256 = "362c214fc600ad73cf996862f63664ac99b344ca73b5a574f23a3ce9490d4470"
RECORDS = ROOT / ".lake/p2-private/records.json"
OUTER_INPUT_RECEIPT = ROOT / ".lake/p25-unguarded-sources/attempt001/RUN_RESULT.json"
RAW_ROOT = ROOT / ".lake/diagnostic/p25-string-char-binding-attempt003"
RAW_RECEIPT = RAW_ROOT / "RESULT.json"
RAW_RECEIPT_SHA256 = "430c5da64acf25d186a15501209a5f83bdb0a964be4120297c20a5a5fe7cab0e"
RAW_OBJECT_SHA256 = "a16d72d38a3313c8654f48c1aae85755a8e810e4e53bcaa600ff78ccce07422a"
RAW_OBJECT_BYTES = 1902224


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def sha(value):
    return hashlib.sha256(value).hexdigest()


def saved(path, value):
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")
    tmp.replace(path)


def output(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()


def import_exact(name, path, expected):
    require(digest(path) == expected, "Helper source differs: " + str(path))
    require(name not in sys.modules, "Helper name already loaded: " + name)
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "Cannot load pinned helper")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def publication_bytes(commit, path):
    return subprocess.check_output(["git", "show", commit + ":" + path], cwd=ROOT)


def copy_exact(source, destination, expected):
    require(source.is_file() and not source.is_symlink(), "Missing/symlinked accepted file: " + str(source))
    require(digest(source) == expected, "Accepted copy source differs: " + str(source))
    require(not destination.exists() and not destination.is_symlink(), "Copy destination already exists")
    destination.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as src, destination.open("xb") as dst:
        shutil.copyfileobj(src, dst, length=1024 * 1024)
    require(digest(source) == expected and digest(destination) == expected,
            "Exact dependency/source copy changed")


def ready_manifest(manifest):
    require(manifest.get("readiness") == "READY_FOR_BOUNDED_RUN",
            "NOT_READY: actual Input/Decoder acceptance evidence has not been pinned")
    require(manifest.get("previous_commit") == PREVIOUS_COMMIT, "Wrong fixed predecessor")
    for name in [INPUT, DECODER]:
        pin = manifest["private_dependencies"][name]
        require(pin.get("status") == "ACTUAL_ACCEPTED",
                "NOT_READY: " + name)
        for field in ["object_sha256", "receipt_sha256", "closure_signature"]:
            require(re.fullmatch(r"[0-9a-f]{64}", pin.get(field, "")) is not None,
                    "NOT_READY evidence pin: " + name + " " + field)
        require(type(pin.get("owned_declarations")) is int and pin["owned_declarations"] > 0,
                "NOT_READY owned inventory: " + name)
    require(re.fullmatch(r"[0-9a-f]{64}", manifest.get("unguarded_outer_receipt_sha256", "")) is not None,
            "NOT_READY: the actual input-bound outer receipt is absent")


def source_graphs(source_manifest, published):
    graphs = {}
    for key, target, count, expected_sha in [
        ("canonical_project_closure", CANONICAL, 3, CANONICAL_SHA256),
        ("consumer_project_closure", CONSUMER, 9, CONSUMER_SHA256),
    ]:
        graph = source_manifest[key]
        nodes = graph["modules"]
        require(graph["root"] == target and graph["project_module_count"] == count
                and len(nodes) == count and not graph["missing"] and not graph["cycles"]
                and graph["FiniteArchive_imported"] is False, "Wrong fixed project closure")
        require(nodes[target]["sha256"] == expected_sha, "Candidate source pin differs")
        for name, row in nodes.items():
            data = published[row["source_path"]]
            require(sha(data) == row["sha256"], "Closure source differs: " + name)
            imports = [v.decode() for v in re.findall(rb"(?m)^import ([^\s]+)\s*$", data)]
            require(imports == row["imports"], "Closure imports differ: " + name)
            require("ImbalancedChen.P2OriginalSaving16FiniteArchive" not in imports,
                    "Guarded finite owner was imported")
        reached, visiting = set(), set()
        def visit(name):
            require(name not in visiting, "Project cycle")
            if name in reached:
                return
            visiting.add(name)
            for imported in nodes[name]["imports"]:
                if imported.startswith("ImbalancedChen."):
                    require(imported in nodes, "Missing project import")
                    visit(imported)
            visiting.remove(name)
            reached.add(name)
        visit(target)
        require(reached == set(nodes), "Closure contains unreachable project nodes")
        graphs[target] = nodes
    return graphs


def validate_dependencies(manifest, nodes, B, U, parse_audit, rows):
    """Read accepted records and evidence; never modify or adopt any record."""
    paths = [RECORDS, RAW_RECEIPT, OUTER_INPUT_RECEIPT]
    records = json.loads(RECORDS.read_text())
    checks = sys.modules["run_winner9_private_checks"]
    pins = manifest["private_dependencies"]
    expected_names = set(nodes) - {RAW, CANONICAL, CONSUMER}
    require(set(pins) == expected_names, "Private prerequisite set differs from the fixed closure")
    objects, evidence = {}, {}
    expected_toolchain = {"lean_version": output([str(LEAN), "--version"]),
                          "lean_binary_sha256": LEAN_SHA256, "mathlib_commit": MATHLIB_PIN}
    for name, pin in pins.items():
        source = ROOT / nodes[name]["source_path"]
        obj = ROOT / ".lake/p2-private/lib" / Path(name.replace(".", "/") + ".olean")
        receipt_path = ROOT / ".lake/p2-private/audit" / name / "latest.json"
        require(pin.get("status") == "ACTUAL_ACCEPTED", "Dependency is not accepted: " + name)
        require(pin["source_sha256"] == nodes[name]["sha256"] == digest(source),
                "Dependency source differs: " + name)
        require(digest(obj) == pin["object_sha256"] and digest(receipt_path) == pin["receipt_sha256"],
                "Dependency object/accepted receipt differs: " + name)
        record = records[name]
        receipt = json.loads(receipt_path.read_text())
        deps = [dep for dep in nodes[name]["imports"] if dep.startswith("ImbalancedChen.")]
        require(record.get("cache_schema") == 2 and record.get("module") == name
                and record.get("exit_code") == 0 and record.get("toolchain") == expected_toolchain
                and record.get("source_sha256") == pin["source_sha256"]
                and record.get("object_sha256") == pin["object_sha256"]
                and record.get("closure_signature") == pin["closure_signature"]
                and checks.closure_signature(record) == pin["closure_signature"],
                "Source/dependency-bound compile record differs: " + name)
        require(record.get("deps") == {dep: pins[dep]["object_sha256"] for dep in deps}
                and record.get("dependency_signatures") == {
                    dep: pins[dep]["closure_signature"] for dep in deps},
                "Dependency closure differs: " + name)
        require(record.get("command", [])[:1 + len(STRICT_FLAGS)] == [str(LEAN), *STRICT_FLAGS],
                "Original strict compile flags differ: " + name)
        require(receipt.get("accepted") is True and receipt.get("module") == name
                and receipt.get("source_sha256") == pin["source_sha256"]
                and receipt.get("object_sha256") == pin["object_sha256"]
                and receipt.get("compile_closure_signature") == pin["closure_signature"],
                "Accepted dependency receipt does not bind this object: " + name)
        for phase in ["replay", "audit"]:
            require(receipt.get(phase, {}).get("exit_code") == 0
                    and receipt[phase].get("inputs_unchanged") is True,
                    "Dependency replay/owned acceptance missing: " + name)
        require(receipt["audit"]["declaration_count"] == pin["owned_declarations"],
                "Dependency owned inventory count differs: " + name)
        require(receipt["input_snapshot"]["project"][name]["object_sha256"] == pin["object_sha256"],
                "Dependency audit object binding differs")
        for relative, expected in receipt["artifacts"].items():
            path = ROOT / relative
            require(digest(path) == expected, "Accepted dependency artifact differs: " + relative)
            paths.append(path)
        paths.extend([source, obj, receipt_path])
        objects[name] = {"path": str(obj), "sha256": pin["object_sha256"],
                         "receipt": str(receipt_path), "receipt_sha256": pin["receipt_sha256"]}
        evidence[name] = {"compile_record": record, "accepted_receipt": receipt,
                          "receipt_sha256": pin["receipt_sha256"]}
    raw = json.loads(RAW_RECEIPT.read_text())
    raw_obj = RAW_ROOT / "lib/ImbalancedChen/P2Saving16StringCharBinding00.olean"
    require(digest(RAW_RECEIPT) == RAW_RECEIPT_SHA256 and raw.get("accepted") is True
            and raw.get("full_owned_audit_accepted") is True
            and raw.get("fresh_input_to_object_binding") is True
            and raw.get("candidate_sha256") == nodes[RAW]["sha256"]
            and raw.get("primary_object_sha256") == RAW_OBJECT_SHA256
            and digest(raw_obj) == RAW_OBJECT_SHA256 and raw_obj.stat().st_size == RAW_OBJECT_BYTES,
            "The accepted raw binding is not the exact original object/receipt")
    for phase in ["normal", "replay", "audit"]:
        require(raw[phase]["exit_code"] == 0 and raw[phase]["timed_out"] is False
                and raw[phase]["inputs_sources_compiler_template_unchanged"] is True,
                "Raw binding phase did not pass")
    require(raw["audit"]["declaration_count"] == 7, "Raw full-owned count differs")
    for relative, expected in raw["artifacts"].items():
        path = RAW_ROOT / relative
        require(digest(path) == expected, "Raw accepted artifact differs: " + relative)
        paths.append(path)
    parsed_raw = parse_audit(RAW_ROOT / "AUDIT.log", RAW, {RAW})
    require(parsed_raw["declaration_count"] == 7, "Raw serialized/environment audit differs")
    paths.append(raw_obj)
    objects[RAW] = {"path": str(raw_obj), "sha256": RAW_OBJECT_SHA256,
                    "receipt": str(RAW_RECEIPT), "receipt_sha256": RAW_RECEIPT_SHA256}
    evidence[RAW] = {"accepted_receipt": raw, "receipt_sha256": RAW_RECEIPT_SHA256}
    current_inputs = U.input_snapshot(rows)
    require(current_inputs["all_inputs_match_manifest"], "Original fourteen-input snapshot failed")
    old_raw_input = raw["normal_snapshot_before"]["input"]
    cell00 = [item for item in current_inputs["files"] if item["install_path"] == B.INPUT_PATH]
    require(old_raw_input["files"] == cell00
            and old_raw_input["directory_identity"] == current_inputs["directory_identity"],
            "Current cell00 is not the physical input bound to the accepted raw object")
    outer = json.loads(OUTER_INPUT_RECEIPT.read_text())
    require(digest(OUTER_INPUT_RECEIPT) == manifest["unguarded_outer_receipt_sha256"]
            and outer.get("accepted") is True
            and outer.get("publication_commit") == PREVIOUS_COMMIT
            and outer.get("original_input_fresh_data_to_object_bound") is True
            and outer.get("inputs_unchanged") is True
            and outer.get("sources_gates_toolchain_unchanged") is True
            and outer.get("records_objects_unchanged_during_audit") is True,
            "OriginalInput lacks actual fresh fourteen-input-bound acceptance")
    require(outer.get("fresh_compilation", {}).get(INPUT) is True
            and INPUT in outer.get("normal", {}).get("exact_START_modules", []),
            "OriginalInput was not actually compiled by the original fresh-input run")
    require(outer.get("final_input_snapshot") == current_inputs
            and outer.get("input_snapshot_after_compile") == current_inputs
            and outer.get("input_snapshot_after_audit") == current_inputs,
            "Current fourteen inputs differ from the accepted reader object's snapshot")
    for name in [INPUT, DECODER]:
        require(outer["compiled_objects"][name]["sha256"] == pins[name]["object_sha256"]
                and outer["owned_receipts"][name]["sha256"] == pins[name]["receipt_sha256"],
                "Input/Decoder outer receipt differs from accepted dependency pins")
    evidence["original_input_outer_receipt"] = {"path": str(OUTER_INPUT_RECEIPT),
        "sha256": manifest["unguarded_outer_receipt_sha256"], "receipt": outer}
    return objects, evidence, list(dict.fromkeys(paths)), current_inputs


def frozen_snapshot(B, U, paths, rows, publication):
    require(output(["git", "rev-parse", "HEAD"]) == publication, "Published worktree HEAD changed")
    require(not output(["git", "status", "--porcelain", "--untracked-files=no"]),
            "Published tracked worktree changed")
    require(output(["git", "rev-parse", "HEAD"], MATHLIB) == MATHLIB_PIN, "Mathlib pin changed")
    require(Path("/workspace/compile-deps/mathlib").resolve() == MATHLIB.resolve(),
            "Mathlib alias changed")
    return {"files": {str(path): B.file_snapshot(path) for path in paths},
            "inputs": U.input_snapshot(rows), "publication": publication,
            "mathlib_pin": MATHLIB_PIN, "mathlib_path": str(MATHLIB.resolve())}


def run_stage(label, target, graph, objects, shared_paths, rows, publication,
              published, out, B, U, parse_audit, template, shared_reference):
    """One target receives its own durable receipt and separate union library."""
    stage = out / label
    stage.mkdir()
    receipt_path = stage / "RESULT.json"
    state = {"schema": "p25-canonical-cell00-stage-v1", "module": target, "accepted": False,
             "status": "PREPARING", "source_sha256": graph[target]["sha256"],
             "project_closure": sorted(graph), "dependency_objects": objects,
             "strict_flags": STRICT_FLAGS, "phase_wall_limits_seconds": 180,
             "fresh_readFile_this_stage": False,
             "input_binding": "Transitive reuse of exact accepted raw and canonical reader objects.",
             "private_records_written": False, "dependency_modules_compiled": [],
             "FiniteArchive_imported": False, "Q96_proved": False, "P2_5_proved": False,
             "started_utc": B.utc_now()}
    saved(receipt_path, state)
    try:
        src, lib, audit_dir = (stage / name for name in ["src", "lib", "audit"])
        for directory in [src, lib, audit_dir]:
            directory.mkdir()
        copied = src / Path(target.replace(".", "/") + ".lean")
        copied.parent.mkdir(parents=True)
        copied.write_bytes(published[graph[target]["source_path"]])
        require(digest(copied) == graph[target]["sha256"], "New source copy differs")
        deps = set(graph) - {target}
        require(set(objects) == deps, "Stage dependency object set differs")
        for name, info in objects.items():
            copy_exact(Path(info["path"]), lib / Path(name.replace(".", "/") + ".olean"), info["sha256"])
        target_object = lib / Path(target.replace(".", "/") + ".olean")
        require(not target_object.exists(), "Target object must be newly generated")
        audit_source = audit_dir / "Audit.lean"
        require(template.count(B.AUDIT_TARGET.encode()) == 2, "Original audit substitution count differs")
        audit_source.write_bytes(template.replace(B.AUDIT_TARGET.encode(), target.encode()))
        paths = list(dict.fromkeys([*shared_paths, copied, audit_source]))
        frozen = frozen_snapshot(B, U, paths, rows, publication)
        require(frozen["inputs"]["all_inputs_match_manifest"], "Stage input snapshot failed")
        require(frozen["inputs"] == shared_reference["inputs"]
                and {path: frozen["files"].get(path) for path in shared_reference["files"]}
                    == shared_reference["files"],
                "Accepted shared context changed while preparing the stage")
        expected = B.object_snapshot(lib)
        require(set(expected) == {name.replace(".", "/") + ".olean" for name in deps},
                "Union library has unexpected dependency objects")
        environment = dict(os.environ)
        environment.pop("LEAN_SRC_PATH", None)
        environment["LEAN_SYSROOT"] = str(LEAN.parent.parent)
        environment["LEAN_PATH"] = ":".join([str(lib), *U.MATHLIB_PATHS])
        state.update(frozen_context=frozen, approved_LEAN_PATH=environment["LEAN_PATH"],
                     isolated_library=str(lib), isolated_source_root=str(src),
                     copied_dependency_objects=expected)
        saved(receipt_path, state)
        commands = [
            ("normal", [str(LEAN), *STRICT_FLAGS, "--root=" + str(src),
                        "-o", str(target_object), str(copied)]),
            ("replay", [str(CHECKER), "--verbose", target]),
            ("audit", [str(LEAN), *STRICT_FLAGS, "--root=" + str(audit_dir), str(audit_source)]),
        ]
        for phase, command in commands:
            before = frozen_snapshot(B, U, paths, rows, publication)
            require(before == frozen and B.object_snapshot(lib) == expected,
                    "Stage sources/inputs/dependencies changed before " + phase)
            state[phase + "_snapshot_before"] = before
            state[phase + "_objects_before"] = expected
            state["status"] = phase.upper() + "_RUNNING"
            saved(receipt_path, state)
            result = B.run_bounded(command, stage / (phase.upper() + ".log"),
                                   environment, TIMEOUT_SECONDS)
            state[phase] = result
            saved(receipt_path, state)
            after = frozen_snapshot(B, U, paths, rows, publication)
            after_objects = B.object_snapshot(lib)
            state[phase + "_snapshot_after"] = after
            state[phase + "_objects_after"] = after_objects
            result["inputs_sources_dependencies_unchanged"] = after == frozen
            if phase == "normal":
                new_name = target.replace(".", "/") + ".olean"
                require(all(after_objects.get(name) == info for name, info in expected.items()),
                        "Normal compilation changed accepted copied dependency objects")
                require(set(after_objects) <= set(expected) | {new_name},
                        "Normal compilation emitted unexpected library files")
            else:
                require(after_objects == expected, "Replay/audit changed any bound object")
            saved(receipt_path, state)
            require(after == frozen, "Stage context changed during " + phase)
            if result["timed_out"] or result["exit_code"] != 0:
                state["status"] = phase.upper() + ("_TIMEOUT" if result["timed_out"] else "_FAILED")
                return None
            if phase == "normal":
                require(set(after_objects) == set(expected) | {new_name}
                        and target_object.is_file() and target_object.stat().st_size > 0,
                        "No fresh target object after successful normal compilation")
                expected = after_objects
                state["fresh_target_object_sha256"] = digest(target_object)
                state["fresh_target_normal_compile"] = True
        parsed = parse_audit(stage / "AUDIT.log", target, set(graph))
        goals = ({CANONICAL + ".canonicalText0_eq_oldString00",
                  CANONICAL + ".ofList_chars00_eq_canonicalText0"} if target == CANONICAL
                 else {CONSUMER + ".cell00_parse_success_diagnostic"})
        require(goals <= {row["name"] for row in parsed["declarations"]},
                "A required theorem is absent from complete owned inventory")
        saved(stage / "OWNED_DECLARATIONS.json", parsed)
        (stage / "TYPES.txt").write_text("\n\n".join(
            row["name"] + "\n" + row["type"] for row in parsed["declarations"]) + "\n")
        require(frozen_snapshot(B, U, paths, rows, publication) == frozen
                and B.object_snapshot(lib) == expected, "Stage final evidence context changed")
        state["audit"].update(declaration_count=parsed["declaration_count"],
                              axiom_counts=parsed["axiom_counts"],
                              serialized_environment_complete=True,
                              private_generated_included=True,
                              unsafe_partial_axiom_flags_all_false=True)
        state["artifacts"] = {str(p.relative_to(stage)): digest(p) for p in [
            copied, target_object, audit_source, stage / "NORMAL.log", stage / "REPLAY.log",
            stage / "AUDIT.log", stage / "OWNED_DECLARATIONS.json", stage / "TYPES.txt"]}
        state["accepted"] = True
        state["status"] = "NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED"
        state["bound_objects"] = expected
    except Exception as error:
        state["accepted"] = False
        state["status"] = "PRECONDITION_OR_EVIDENCE_FAILED"
        state["error"] = type(error).__name__ + ": " + str(error)
    finally:
        state["final_input_snapshot"] = U.input_snapshot(rows)
        if "frozen_context" in state and state["final_input_snapshot"] != state["frozen_context"]["inputs"]:
            state["accepted"] = False
            state["status"] = "FINAL_INPUT_IDENTITY_MISMATCH"
        state["ended_utc"] = B.utc_now()
        saved(receipt_path, state)
        print("P25_CELL00_STAGE_RESULT " + json.dumps({"stage": label, "status": state["status"],
              "accepted": state["accepted"], "receipt": str(receipt_path),
              "receipt_sha256": digest(receipt_path)}), flush=True)
    if not state["accepted"]:
        return None
    return {"path": str(target_object), "sha256": digest(target_object),
            "receipt": str(receipt_path), "receipt_sha256": digest(receipt_path),
            "stage_directory": str(stage), "accepted": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("publication_commit", help="Full already-fetched commit; no network operation")
    args = parser.parse_args()
    require(ROOT.is_dir() and not ROOT.is_symlink(), "Fixed own worktree absent or symlinked")
    out = ROOT / ATTEMPT
    require(not out.exists(), "Preserve the existing attempt; do not overwrite evidence")
    require(out.parent.resolve().is_relative_to(ROOT.resolve()), "Output parent leaves fixed root")
    out.mkdir(parents=True)
    receipt_path = out / "RESULT.json"
    state = {"schema": "p25-canonical-cell00-two-stage-v1", "accepted": False, "status": "PREPARING",
             "publication_commit": args.publication_commit, "previous_commit": PREVIOUS_COMMIT,
             "canonical_binding_accepted": False, "single_cell_parse_decode_accepted": False,
             "raw_binding_recompiled": False, "private_records_written": False,
             "other_13_cells_proved": False, "four_finite_guards_proved": False,
             "Q96_proved": False, "P2_5_proved": False, "production_credit": False,
             "runner_sha256": digest(Path(__file__).resolve())}
    saved(receipt_path, state)
    B = U = rows = None
    try:
        require(re.fullmatch(r"[0-9a-f]{40}", args.publication_commit) is not None,
                "Expected full lowercase publication commit")
        require(Path(output(["git", "rev-parse", "--show-toplevel"])).resolve() == ROOT.resolve(),
                "Wrong existing worktree")
        require(output(["git", "rev-parse", "HEAD"]) == PREVIOUS_COMMIT,
                "Own worktree must still be at the fixed predecessor")
        require(not output(["git", "status", "--porcelain", "--untracked-files=no"]),
                "Own worktree tracked source is not clean")
        subprocess.check_call(["git", "merge-base", "--is-ancestor", PREVIOUS_COMMIT,
                               args.publication_commit], cwd=ROOT)
        runner_bytes = publication_bytes(args.publication_commit, RUNNER_PATH)
        manifest_bytes = publication_bytes(args.publication_commit, RUNNER_MANIFEST)
        require(sha(runner_bytes) == state["runner_sha256"], "Executing runner differs from publication")
        manifest = json.loads(manifest_bytes)
        require(manifest["runner_sha256"] == state["runner_sha256"], "Runner manifest does not bind this code")
        state["runner_manifest_sha256"] = sha(manifest_bytes)
        ready_manifest(manifest)
        source_manifest_bytes = publication_bytes(args.publication_commit, SOURCE_MANIFEST)
        require(sha(source_manifest_bytes) == SOURCE_MANIFEST_SHA256, "Candidate manifest differs")
        source_manifest = json.loads(source_manifest_bytes)
        pinned = {SOURCE_MANIFEST: SOURCE_MANIFEST_SHA256, INPUT_MANIFEST: INPUT_MANIFEST_SHA256,
                  BASE_RUNNER: BASE_RUNNER_SHA256, INPUT_RUNNER: INPUT_RUNNER_SHA256}
        protected = source_manifest["original_target_identity"]
        pinned[protected["original_source"]] = protected["original_source_sha256"]
        for graph_key in ["canonical_project_closure", "consumer_project_closure"]:
            for row in source_manifest[graph_key]["modules"].values():
                pinned[row["source_path"]] = row["sha256"]
        pinned.update(manifest["gate_sources"])
        published = {path: publication_bytes(args.publication_commit, path) for path in pinned}
        for path, expected in pinned.items():
            require(sha(published[path]) == expected, "Published source/gate differs: " + path)
        graphs = source_graphs(source_manifest, published)
        require(digest(LEAN) == LEAN_SHA256 and digest(CHECKER) == CHECKER_SHA256, "Tool binaries differ")
        require(output(["git", "rev-parse", "HEAD"], MATHLIB) == MATHLIB_PIN, "Mathlib pin differs")
        require(LEAN_COMMIT in output([str(LEAN), "--version"]), "Lean source commit differs")
        shared = out / "shared"
        shared.mkdir()
        for relative, name in [(BASE_RUNNER, "raw_runner.py"), (INPUT_RUNNER, "input_runner.py")]:
            (shared / name).write_bytes(published[relative])
        (shared / "EXECUTED_RUNNER.py").write_bytes(runner_bytes)
        (shared / "RUNNER_MANIFEST.json").write_bytes(manifest_bytes)
        B = import_exact("p25_raw003_reuse", shared / "raw_runner.py", BASE_RUNNER_SHA256)
        U = import_exact("p25_unguarded_reuse", shared / "input_runner.py", INPUT_RUNNER_SHA256)
        require(B.ROOT == U.ROOT == ROOT and B.STRICT_FLAGS == U.STRICT_FLAGS == STRICT_FLAGS,
                "Reusable runner context/strict flags differ")
        tools_dir = shared / "audit-tools"
        tools_dir.mkdir()
        for relative in [*B.PYTHON_AUDIT_SOURCES, B.AUDIT_TEMPLATE]:
            require(manifest["gate_sources"][relative] == B.PINNED_FILES[relative],
                    "Original audit source pin differs")
            (tools_dir / Path(relative).name).write_bytes(published[relative])
        parse_audit = B.load_original_audit_parser(tools_dir)
        rows = json.loads(published[INPUT_MANIFEST])["saving16_inputs"]
        require(len(rows) == 14 and sum(row["bytes"] for row in rows) == 93508187,
                "Expected fourteen original input rows")
        objects, evidence, dependency_paths, before = validate_dependencies(
            manifest, graphs[CONSUMER], B, U, parse_audit, rows)
        state["accepted_dependency_evidence"] = evidence
        state["input_snapshot_before_advance"] = before
        state["accepted_dependency_objects_before_advance"] = {
            name: B.file_snapshot(info["path"]) for name, info in objects.items()}
        saved(receipt_path, state)
        actual_copy_bytes = sum(Path(objects[name]["path"]).stat().st_size
                                for name in graphs[CANONICAL] if name != CANONICAL)
        actual_copy_bytes += sum(Path(info["path"]).stat().st_size for info in objects.values())
        free = shutil.disk_usage(out).free
        state["disk_preflight"] = {"free_bytes": free, "known_dependency_copy_bytes": actual_copy_bytes,
                                   "new_target_sizes_not_predicted": True}
        require(free > actual_copy_bytes, "Insufficient disk for exact known dependency copies")
        old_dependencies = {str(path): B.file_snapshot(path) for path in dependency_paths
                            if path not in {ROOT / row["source_path"] for row in graphs[CONSUMER].values()}}
        state["status"] = "ADVANCING_ONLY_FIXED_TASK_WORKTREE"
        saved(receipt_path, state)
        subprocess.check_call(["git", "checkout", "--detach", args.publication_commit], cwd=ROOT)
        require(digest(ROOT / RUNNER_PATH) == state["runner_sha256"]
                and digest(ROOT / RUNNER_MANIFEST) == sha(manifest_bytes), "Runner changed during advancement")
        for path, expected in pinned.items():
            require(digest(ROOT / path) == expected, "Published source changed during advancement: " + path)
        require(U.input_snapshot(rows) == before, "Original inputs changed during source advancement")
        require({path: B.file_snapshot(path) for path in old_dependencies} == old_dependencies,
                "Accepted dependency objects/receipts/records changed during advancement")
        shared_paths = list(dict.fromkeys([
            ROOT / RUNNER_PATH, ROOT / RUNNER_MANIFEST, *[ROOT / p for p in pinned],
            Path(__file__).resolve(), *[p for p in shared.rglob("*") if p.is_file()],
            LEAN, CHECKER, LEAN.parent.parent / "lib/lean/Lean.olean",
            LEAN.parent.parent / "lib/lean/Lean/Util/CollectAxioms.olean", *dependency_paths]))
        for path in U.MATHLIB_PATHS:
            require(Path(path).is_dir(), "Approved Mathlib dependency library missing")
        shared_reference = frozen_snapshot(B, U, shared_paths, rows, args.publication_commit)
        require(shared_reference["inputs"] == before, "Original inputs changed before stage preparation")
        state["shared_frozen_context"] = shared_reference
        saved(receipt_path, state)
        a_objects = {name: objects[name] for name in graphs[CANONICAL] if name != CANONICAL}
        first = run_stage("canonical", CANONICAL, graphs[CANONICAL], a_objects, shared_paths,
                          rows, args.publication_commit, published, out, B, U, parse_audit,
                          published[B.AUDIT_TEMPLATE], shared_reference)
        if first is None:
            state["status"] = "CANONICAL_NOT_ACCEPTED_CHARPARSE_NOT_STARTED"
            return 1
        state["canonical_binding_accepted"] = True
        state["canonical_accepted_object"] = first
        state["status"] = "CANONICAL_ACCEPTED_CHARPARSE_PENDING"
        saved(receipt_path, state)
        # Stage A is finalized above. Stage B reads/copies it without changing
        # any A artifact or receipt, including when B fails or times out.
        a_paths = [p for p in Path(first["stage_directory"]).rglob("*") if p.is_file()]
        require(frozen_snapshot(B, U, shared_paths, rows, args.publication_commit) == shared_reference,
                "Accepted shared context changed after the canonical stage")
        second_reference = frozen_snapshot(B, U, [*shared_paths, *a_paths], rows, args.publication_commit)
        second_objects = {**objects, CANONICAL: first}
        second = run_stage("charparse", CONSUMER, graphs[CONSUMER], second_objects,
                           [*shared_paths, *a_paths], rows, args.publication_commit, published,
                           out, B, U, parse_audit, published[B.AUDIT_TEMPLATE], second_reference)
        require(digest(Path(first["receipt"])) == first["receipt_sha256"]
                and digest(Path(first["path"])) == first["sha256"],
                "Stage B changed the already accepted canonical evidence")
        if second is None:
            state["status"] = "CANONICAL_ACCEPTED_CHARPARSE_NOT_ACCEPTED"
            return 1
        state["single_cell_parse_decode_accepted"] = True
        state["charparse_accepted_object"] = second
        require(frozen_snapshot(B, U, shared_paths, rows, args.publication_commit) == shared_reference,
                "Accepted shared context changed before final acceptance")
        state["accepted"] = True
        state["status"] = "CANONICAL_AND_CELL00_PARSE_DECODE_ACCEPTED"
    except Exception as error:
        state["accepted"] = False
        state["status"] = "PRECONDITION_OR_EVIDENCE_FAILED"
        state["error"] = type(error).__name__ + ": " + str(error)
        return 1
    finally:
        if U is not None and rows is not None:
            state["final_input_snapshot"] = U.input_snapshot(rows)
            if "input_snapshot_before_advance" in state:
                state["current_input_context_unchanged"] = (
                    state["final_input_snapshot"] == state["input_snapshot_before_advance"])
                if not state["current_input_context_unchanged"]:
                    state["accepted"] = False
                    state["status"] = "FINAL_INPUT_IDENTITY_MISMATCH"
        saved(receipt_path, state)
        print("P25_CELL00_RESULT " + json.dumps({key: state[key] for key in [
            "status", "accepted", "canonical_binding_accepted", "single_cell_parse_decode_accepted",
            "Q96_proved", "P2_5_proved"]}), flush=True)
        print("P25_CELL00_RECEIPT " + str(receipt_path) + " " + digest(receipt_path), flush=True)
    return 0 if state["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())

