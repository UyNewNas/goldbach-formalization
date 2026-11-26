#!/usr/bin/env python3
"""Dormant two-owner Cell01 canonical character binding continuation.

Reuse the accepted OriginalInput object and its original fourteen-input binding.
Compile only the existing quotation loader and Cell01 binding sources unchanged,
using the original strict normal, independent replay and full owned audit gates.
The actual accepted v8 fresh-context receipt, original reused Decoded provenance,
exact normal-rematerialization accounting and reviewed artifacts are mandatory
before any mutation. No source generation, accepted gate rerun, storage cleanup,
new audit framework, JSON parser or typed decoder is introduced.
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
CELL00_PUBLICATION = "2106ae104bb98cd3d647a202df069b380e2de5bc"
CELL00_RESULT_SHA256 = None
CELL00_ARTIFACTS_REVIEWED = False
PREVIOUS_COMMIT = CELL00_PUBLICATION
ORIGINAL_INPUT_PUBLICATION = "448e03d6ce02fd7d3b8d008defcd5ffffc4fc426"
PACKAGE = "docs/source-only/20261125-p2-5-canonical-char-loader"
RUNNER_FOLDER = "docs/verification/20261126-p2-5-resumed/cell01-canonical"
RUNNER_PATH = RUNNER_FOLDER + "/run_canonical_cell01_v3.py"
RUNNER_MANIFEST = RUNNER_FOLDER + "/RUNNER_MANIFEST_V3.json"
SOURCE_MANIFEST = PACKAGE + "/MANIFEST.json"
SOURCE_MANIFEST_SHA256 = "fed4f00b0a662ad02241ff294d78746d69d48d334dbf8775d4068f120ba64f44"
ADAPTED_FROM = "docs/source-only/20261125-p2-5-cell00-canonical/run_canonical_cell00.py"
ADAPTED_FROM_SHA256 = "7fb5a087044cf2689d6e171b2012b4ff11e46d6e7c37ae6bd8dd12045524e848"
ATTEMPT = ".lake/diagnostic/p25-cell01-canonical-attempt001"
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
MIN_INITIAL_FREE_BYTES = 1024 * 1024 * 1024
GATE_WORKING_HEADROOM_BYTES = 256 * 1024 * 1024
INPUT = "ImbalancedChen.P2OriginalSaving16OriginalInput"
LOADER = "ImbalancedChen.P2Saving16CanonicalCharLoader"
BINDING = "ImbalancedChen.P2Saving16CanonicalCell01Binding"
FRESH_MODULES = [LOADER, BINDING]
REQUIRED_PUBLIC_NAMES = {LOADER: [], BINDING: [BINDING + ".chars01", BINDING + ".ofList_chars01_eq_originalText1"]}
LOADER_SHA256 = "a61bf5fe0b370019f7b3115684dae4ba98ca947604adbd03d01d543528b134a1"
BINDING_SHA256 = "a18d3ae821babe0d06642aaece7abd73b368bf6196095810f669a5756d40f802"
INPUT_SHA256 = "792a5adf50263cfc1a0f67fb3d088c7612910388e4d1fa65db45c3c50065aca5"
INPUT_OBJECT_SHA256 = "72488821ccb01dec90188d2f09b0e3a73c0087b54c6c4bae4410a109b6f82f91"
INPUT_OBJECT_BYTES = 93650960
INPUT_RECEIPT_SHA256 = "8cca39ad7ae91d0be9d7b8f5d7a92251ca80e2f0b80a4f17f4816e77b41c34fb"
INPUT_CLOSURE_SIGNATURE = "81c89a9fc79a2aa1b6ddfac5a3fe7b12de66784c9cebacff6533625a5bdd2a71"
OUTER_INPUT_RECEIPT = ROOT / ".lake/p25-unguarded-sources/attempt001/RUN_RESULT.json"
OUTER_INPUT_RECEIPT_SHA256 = "cb11eb092d12e3e1f08eb9dccad4ecbe53311f456babe6c0ccabe72b93c3fa65"
CELL00_RESULT = ROOT / ".lake/diagnostic/p25-cell00-four-consumers-attempt008/RESULT.json"
CELL00_DRIVER = "docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v8.py"
CELL00_RUNNER_SHA256 = "ffcc4aff64705a29d9fa94faf44350753d4ba6faf2abbd0c748d634baf363beb"
CELL00_VALIDATOR_DRIVER = "docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v6.py"
CELL00_VALIDATOR_SHA256 = "064fa8414660f7036b51bf6bf336f1aef168913dca5722cd4050b9d005174f7a"
CELL00_SELECTION = "docs/verification/20261126-p2-5-resumed/cell00-fresh-context/FRESH_CONTEXT_SELECTION.json"
CELL00_SELECTION_SHA256 = "1be717f81e2886e5291bdff7f129dbff8d75453656d6afa88c54cfd8168f01ca"
RECOVERY_SELECTION = "docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json"
RECOVERY_SELECTION_SHA256 = "cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf"
CELL00_MODULES = ["ImbalancedChen.P2Saving16Cell00OriginalParse",
                  "ImbalancedChen.P2Saving16Cell00OriginalFloors", "ImbalancedChen.P2Saving16Cell00OriginalArithmetic",
                  "ImbalancedChen.P2Saving16Cell00OriginalSourceFacts"]
DECODED = "ImbalancedChen.P2Saving16Cell00Decoded"
DECODED_PUBLICATION = "be20f0b050bb787ecb98f9afdd9b6a386706f45a"
DECODED_OBJECT_SHA256 = "f700e8e866da0192152040a0853e27eab857ee007c0076df61613e3a849e534f"
PREVIOUS_CONSUMER = ROOT / ".lake/diagnostic/p25-cell00-five-consumers-attempt005/RESULT.json"
PREVIOUS_CONSUMER_SHA256 = "bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88"
DISK_FAILURE = ROOT / ".lake/diagnostic/p25-cell00-five-consumers-attempt004/RESULT.json"
DISK_FAILURE_SHA256 = "2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a"
CANONICAL00 = "ImbalancedChen.P2Saving16CanonicalCell00Binding"
CANONICAL00_ROOT = ROOT / ".lake/diagnostic/p25-cell00-canonical-attempt001"
CANONICAL00_RECEIPT_SHA256 = "02da5203b80e6d5a735596ef2f6c1f2f26682304627a8e95f890c0ce2ca1d23b"
CANONICAL00_OUTER_SHA256 = "edec731af08194ad0b3f57b291491fd1bae67fa9876a84bb1e3bf8b58be5db72"
CANONICAL00_PUBLICATION = "52098e403ac4b28c72ec5958fd738ae93d785ac5"
CANONICAL00_OBJECT_SHA256 = "fa7ad4fd4333a9e4fc13fb64448b91db539d65ecf51c6d572e98322e2ccd1837"
QUALIFIED_EXTERNAL = None


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


def require_workflow_ready():
    require(isinstance(CELL00_RESULT_SHA256, str) and re.fullmatch(r"[0-9a-f]{64}", CELL00_RESULT_SHA256) and
            isinstance(CELL00_PUBLICATION, str) and re.fullmatch(r"[0-9a-f]{40}", CELL00_PUBLICATION) and
            PREVIOUS_COMMIT == CELL00_PUBLICATION and CELL00_ARTIFACTS_REVIEWED is True,
            "DORMANT: actual accepted Cell00 consumer receipt, exact publication and artifact review are required before mutation.")


def ready_manifest(manifest):
    require(manifest.get("readiness") == "READY_FOR_BOUNDED_RUN" and manifest.get("previous_commit") == PREVIOUS_COMMIT,
            "DORMANT: Cell01 manifest is not bound to the actual accepted Cell00 prerequisite.")
    require(manifest["fresh_modules"] == FRESH_MODULES and set(manifest["private_dependencies"]) == {INPUT},
            "Only the two existing new modules and one accepted OriginalInput dependency are permitted.")
    pin = manifest["private_dependencies"][INPUT]
    require(pin.get("status") == "ACTUAL_ACCEPTED" and pin["source_sha256"] == INPUT_SHA256 and
            pin["object_sha256"] == INPUT_OBJECT_SHA256 and pin["object_bytes"] == INPUT_OBJECT_BYTES and
            pin["receipt_sha256"] == INPUT_RECEIPT_SHA256 and pin["closure_signature"] == INPUT_CLOSURE_SIGNATURE and
            pin["owned_declarations"] == 3 and manifest["unguarded_outer_receipt_sha256"] == OUTER_INPUT_RECEIPT_SHA256,
            "OriginalInput accepted source/object/owned/closure evidence differs.")
    require(manifest["cell00_prerequisite"] == {"publication_commit": CELL00_PUBLICATION,
                "result_sha256": CELL00_RESULT_SHA256, "runner_sha256": CELL00_RUNNER_SHA256,
                "artifacts_reviewed": CELL00_ARTIFACTS_REVIEWED},
            "Cell00 prerequisite pins differ from the driver.")
    require(manifest["fresh_context_selection"] == {"path": CELL00_SELECTION, "sha256": CELL00_SELECTION_SHA256}
            and manifest["recovery_selection"] == {"path": RECOVERY_SELECTION, "sha256": RECOVERY_SELECTION_SHA256},
            "Fresh-context and exact original-object selection pins differ.")


def source_graphs(source_manifest, published):
    require(source_manifest["schema"] == "p25-canonical-char-loader-cell01-source-only-v1" and
            set(source_manifest["modules"]) == set(FRESH_MODULES), "Require exactly the two existing Cell01 source modules.")
    cell = source_manifest["cell01"]
    require(cell["canonical_index"] == cell["canonical_source_id"] == 1 and
            cell["new_character_definition"] == REQUIRED_PUBLIC_NAMES[BINDING][0] and
            cell["target"] == REQUIRED_PUBLIC_NAMES[BINDING][1] and
            cell["statement"] == "String.ofList chars01 = originalText (1 : Fin 14)",
            "Cell01 index or existing target statement differs.")
    dependency = source_manifest["existing_canonical_dependency"]
    require(dependency["module"] == INPUT and dependency["sha256"] == INPUT_SHA256 and
            dependency["production_path"] == "ImbalancedChen/P2OriginalSaving16OriginalInput.lean",
            "OriginalInput source identity differs.")
    nodes = {INPUT: {"source_path": dependency["production_path"], "sha256": dependency["sha256"],
                     "imports": dependency["imports"]}}
    for module in FRESH_MODULES:
        row = source_manifest["modules"][module]
        require(row["sha256"] == (LOADER_SHA256 if module == LOADER else BINDING_SHA256),
                "Existing Cell01 source pin differs: " + module)
        nodes[module] = {"source_path": row["path"], "sha256": row["sha256"], "imports": row["imports"]}
    require(source_manifest["static_import_closure"]["topological_order"] == [INPUT, LOADER, BINDING] and
            source_manifest["static_import_closure"]["project_module_count"] == 3,
            "Cell01 project closure scope differs.")
    for module, row in nodes.items():
        data = published[row["source_path"]]
        require(sha(data) == row["sha256"], "Closure source differs: " + module)
        imports = [name.decode() for name in re.findall(rb"(?m)^import ([^\s]+)\s*$", data)]
        require(imports == row["imports"], "Closure imports differ: " + module)
    require(nodes[INPUT]["imports"] == ["Lean", "Mathlib.Data.Fin.VecNotation"] and
            nodes[LOADER]["imports"] == ["Lean", INPUT] and nodes[BINDING]["imports"] == [LOADER],
            "Unexpected Cell01 source/import closure.")
    return {LOADER: {name: nodes[name] for name in [INPUT, LOADER]}, BINDING: nodes}


def original_compile_record(outer):
    """Read the unchanged record embedded in the exact original outer receipt."""
    record = outer["compile_records"][INPUT]
    require(record == outer["records_after_audit"][INPUT],
            "The original compile record changed across its historical owned audit.")
    return record


def validate_original_input_window(outer, current, rows):
    """Retain historical physical identities; bind new observations by exact bytes."""
    historical = outer["final_input_snapshot"]
    require(all(outer[key] == historical for key in ["input_snapshot_before_advance",
                "input_snapshot_after_compile", "input_snapshot_after_audit"]),
            "The historical input read/compile/audit window changed.")
    expected = [{"install_path": row["install_path"], "realpath": row["cloud"]["path"],
                 "bytes": row["bytes"], "sha256": row["sha256"]} for row in rows]
    require(len(expected) == len({r["install_path"] for r in expected}) ==
            len({r["realpath"] for r in expected}) == 14 and
            sum(r["bytes"] for r in expected) == 93508187 and
            all(os.path.normpath(str(ROOT / r["install_path"])) == r["realpath"] for r in expected),
            "Original input manifest paths or scope changed.")
    directory = str(ROOT.parent / "goldbach-research")
    for label, snapshot in [("historical", historical), ("current", current)]:
        require(snapshot["all_inputs_match_manifest"] is True and snapshot["errors"] == []
                and snapshot["cwd"] == str(ROOT)
                and snapshot["directory"] == snapshot["directory_realpath"] == directory
                and [{key: row[key] for key in expected[0]} for row in snapshot["files"]] == expected,
                label + " input paths, bytes or SHA differ from the original fourteen inputs.")
        require(all(type(identity.get(key)) is int for identity in
                    [snapshot["directory_identity"], *snapshot["files"]]
                    for key in ["device", "inode", "mtime_ns", "ctime_ns"]),
                label + " input physical identity inventory is incomplete.")
    return {"historical_read_window_unchanged": True,
            "current_bytes_match_original_fourteen": True,
            "historical_physical_identity_still_equal": current == historical,
            "historical_metadata_rewritten": False}


def validate_dependencies(manifest, nodes, B, U, parse_audit, rows):
    """Read accepted records and evidence; never modify or adopt any record."""
    paths = [OUTER_INPUT_RECEIPT]
    require(digest(OUTER_INPUT_RECEIPT) == OUTER_INPUT_RECEIPT_SHA256,
            "Exact original outer receipt bytes differ before reading its compile record.")
    outer = json.loads(OUTER_INPUT_RECEIPT.read_text())
    records = {INPUT: original_compile_record(outer)}
    checks = sys.modules["run_winner9_private_checks"]
    pins = manifest["private_dependencies"]
    expected_names = set(nodes) - set(FRESH_MODULES)
    require(expected_names == {INPUT}, "Only accepted OriginalInput may be staged.")
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
        require(obj.stat().st_size == INPUT_OBJECT_BYTES and
                not any(Path(str(obj) + suffix).exists() for suffix in [".private", ".server"]),
                "OriginalInput object byte count or accepted companion inventory differs.")
        parsed = parse_audit(ROOT / receipt["audit"]["log"], INPUT, {INPUT})
        require(parsed["declaration_count"] == 3 and
                parsed == json.loads((ROOT / Path(receipt["audit"]["log"]).with_name("declarations.json")).read_text()),
                "OriginalInput complete owned evidence differs from its exact accepted audit.")
        paths.extend([source, obj, receipt_path])
        objects[name] = {"path": str(obj), "sha256": pin["object_sha256"],
                         "receipt": str(receipt_path), "receipt_sha256": pin["receipt_sha256"]}
        evidence[name] = {"compile_record": record, "accepted_receipt": receipt,
                          "receipt_sha256": pin["receipt_sha256"]}
    current_inputs = U.input_snapshot(rows)
    require(current_inputs["all_inputs_match_manifest"], "Original fourteen-input snapshot failed")
    require(digest(OUTER_INPUT_RECEIPT) == manifest["unguarded_outer_receipt_sha256"]
            and outer.get("accepted") is True
            and outer.get("publication_commit") == ORIGINAL_INPUT_PUBLICATION
            and outer.get("original_input_fresh_data_to_object_bound") is True
            and outer.get("inputs_unchanged") is True
            and outer.get("sources_gates_toolchain_unchanged") is True
            and outer.get("records_objects_unchanged_during_audit") is True,
            "OriginalInput lacks actual fresh fourteen-input-bound acceptance")
    require(outer.get("fresh_compilation", {}).get(INPUT) is True
            and INPUT in outer.get("normal", {}).get("exact_START_modules", []),
            "OriginalInput was not actually compiled by the original fresh-input run")
    evidence["original_input_read_window"] = validate_original_input_window(outer, current_inputs, rows)
    for name in [INPUT]:
        require(outer["compiled_objects"][name]["sha256"] == pins[name]["object_sha256"]
                and outer["owned_receipts"][name]["sha256"] == pins[name]["receipt_sha256"],
                "OriginalInput outer receipt differs from its accepted dependency pin")
    require(outer["compile_records"][INPUT] == records[INPUT] and
            outer["owned_receipts"][INPUT]["receipt"] == evidence[INPUT]["accepted_receipt"],
            "OriginalInput historical compile or owner dictionary was relabeled.")
    evidence["original_input_outer_receipt"] = {"path": str(OUTER_INPUT_RECEIPT),
        "sha256": manifest["unguarded_outer_receipt_sha256"], "receipt": outer}
    return objects, evidence, list(dict.fromkeys(paths)), current_inputs


def validate_normal_accounting(cell00, remat, selected, recovery):
    """Separate actual exact-byte recovery normals from the four consumer gates."""
    objects = recovery["objects"]
    require(selected["schema"] == "p25-cell00-fresh-context-selection-v1"
            and recovery["schema"] == "p25-cache-rematerialization-selection-v1"
            and selected["target_root"] == recovery["target_root"] == str(ROOT)
            and selected["output_root"] == str(CELL00_RESULT.parent)
            and selected["consumer_modules"] == CELL00_MODULES
            and len(objects) == 41 and len(selected["only_normal_modules"]) == 10
            and selected["only_normal_modules"] == recovery["allowed_normal_rebuild_modules"]
            and set(selected["normal_order"]) == set(selected["only_normal_modules"])
            and len(selected["normal_order"]) == 10,
            "Original object/source graph or normal allowance changed.")
    require(remat["schema"] == "p25-exact-normal-rematerialization-fresh-context-v8"
            and remat["status"] == "EXACT_OBJECTS_READY_FOR_NEW_CONSUMER_CONTEXT"
            and remat["exact_objects_ready"] is True and remat["accepted"] is False
            and remat["new_formal_credit"] is False and remat["P2_5_proved"] is False
            and remat["publication_commit"] == CELL00_PUBLICATION
            and remat["runner_sha256"] == CELL00_RUNNER_SHA256
            and remat["selection_sha256"] == CELL00_SELECTION_SHA256
            and remat["old_receipts_changed"] is False and remat["old_snapshots_synthesized"] is False
            and remat["old_v7_preflight_passed"] is False,
            "Actual exact-normal rematerialization evidence or provenance differs.")
    stages = remat["normal_stages"]
    normals = [row["module"] for row in stages]
    available = remat["available_objects_reused_without_normal"]
    require(available == sorted(set(available)) and set(available).isdisjoint(normals)
            and set(available) | set(normals) == set(objects),
            "An available object was rebuilt or the complete object partition changed.")
    require(len(normals) == len(set(normals)) and set(normals) <= set(selected["only_normal_modules"])
            and normals == [name for name in selected["normal_order"] if name not in available]
            and cell00["dependency_modules_compiled"] == cell00["existing_owners_normally_recompiled"] == normals
            and cell00["normal_rematerialization_stages"] == stages
            and cell00["consumer_phase_dependency_modules_compiled"] ==
                cell00["accepted_dependency_gates_rerun"] == remat["replay_stages"] == remat["owned_audit_stages"] == [],
            "Exact normal recovery work is unapproved, hidden, reordered or counted as a consumer gate.")
    require(set(cell00["dependency_objects"]) == set(objects) and all(
                cell00["dependency_objects"][name]["sha256"] == row["sha256"] and
                cell00["dependency_objects"][name]["source_sha256"] == row["source_sha256"]
                for name, row in objects.items()), "An accepted dependency source/object pin differs.")
    exceptions = {row["path"]: row for row in selected["historical_envelope_exceptions"]}
    gaps = remat["historical_archive_gaps"]
    require(len(exceptions) == 5 and len({r["path"] for r in gaps}) == len(gaps)
            and all(exceptions.get(row["path"]) == row for row in gaps)
            and cell00["historical_archive_gaps"] == gaps,
            "A historical envelope gap is not an exact original tuple.")
    phase = CELL00_RESULT.parent / "rematerialization"
    witness_keys = ["path", "realpath", "bytes", "sha256"]
    witnesses = [{"path": row["realpath"], "realpath": row["realpath"],
                  "bytes": row["bytes"], "sha256": row["sha256"]} for row in recovery["witnesses"]]
    for stage in stages:
        row = objects[stage["module"]]
        relative = stage["module"].replace(".", "/")
        source, obj = phase / "src" / (relative + ".lean"), phase / "lib" / (relative + ".olean")
        require(stage["purpose"] == "exact-historical-byte-rematerialization"
                and stage["status"] == "PASSED" and stage["exit_code"] == 0 and stage["timed_out"] is False
                and stage["cwd"] == str(ROOT) and stage["LEAN_PATH"] == ":".join(
                    [str(phase / "lib"), *selected["external_provider_roots"][1:]])
                and stage["command"] == [str(LEAN), *recovery["runtime"]["strict_flags"],
                    "--root=" + str(phase / "src"), "-o", str(obj), str(source)],
                "An exact normal stage changed its strict command, context or result.")
        require(stage["expected_object_sha256"] == stage["object"]["sha256"] == row["sha256"]
                and stage["object"]["path"] == str(obj) and stage["object"]["bytes"] > 0
                and stage["exact_historical_object_match"] is True and stage["object_companions"] == [],
                "A normal object did not reproduce the original accepted bytes.")
        require(stage["input_snapshot_before"] == stage["input_snapshot_after"]
                and [{key: item[key] for key in witness_keys} for item in stage["input_snapshot_before"]] == witnesses
                and all(type(item.get(key)) is int for item in stage["input_snapshot_before"]
                        for key in ["device", "inode", "mtime_ns"]),
                "Original input physical/hash window changed during normal recovery.")


def validate_workflow_receipts(cell00, canonical, historical_outer, previous_consumer=None):
    """Check the observed workflow prerequisite without importing any Cell00 object."""
    require(cell00["schema"] == "p25-cell00-four-consumers-fresh-context-strict-v8" and
            cell00["accepted"] is True and cell00["status"] == "ORIGINAL_CELL00_FOUR_CONSUMERS_ACCEPTED" and
            cell00["publication_commit"] == CELL00_PUBLICATION and cell00["runner"]["sha256"] == CELL00_RUNNER_SHA256 and
            cell00["module_order"] == CELL00_MODULES and set(cell00["modules"]) == set(CELL00_MODULES) and
            cell00["original_cell00_decode_proved"] is True and
            cell00["complete_external_after_matches_before"] is True and
            cell00["consumer_phase_dependency_modules_compiled"] == cell00["accepted_dependency_gates_rerun"] == [] and
            cell00["old_v7_preflight_passed"] is False and cell00["old_recovery_complete"] is False and
            cell00["old_snapshots_synthesized"] is False and cell00["historical_missing_external_hashes_invented"] is False and
            cell00["decoded_gates_rerun"] == [] and cell00["failed_parse_aggregate_relabelled"] is False and
            cell00["private_parse_helpers_audited"] is True and len(cell00["dependency_objects"]) == 41 and
            cell00["Q96_proved"] is False and cell00["P2_5_proved"] is False,
            "Actual complete Cell00 consumer acceptance is required before Cell01 execution.")
    for module in CELL00_MODULES:
        owner = cell00["modules"][module]
        require(owner["accepted"] is True and owner["status"] == "NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED" and
                owner["source_origin"]["commit"] == CELL00_PUBLICATION and
                set(owner["stages"]) == {"normal", "replay", "audit"} and
                all(row["status"] == "PASSED" and row["exit_code"] == 0 and row["timed_out"] is False
                    for row in owner["stages"].values()), "An actual Cell00 owner has not passed every gate.")
    require(previous_consumer is not None and previous_consumer["accepted"] is False and
            previous_consumer["status"] == "MODULE_STAGE_FAILED" and
            previous_consumer["publication_commit"] == DECODED_PUBLICATION and
            cell00["previous_parse_failure"] == {
                "path": str(PREVIOUS_CONSUMER), "bytes": 5049315, "sha256": PREVIOUS_CONSUMER_SHA256,
                "publication_commit": DECODED_PUBLICATION, "aggregate_accepted": False,
                "aggregate_status": "MODULE_STAGE_FAILED", "failed_module": CELL00_MODULES[0],
                "failed_stage": "normal", "failed_owner_reused": False} and
            cell00["previous_parse_failed_owner"] == previous_consumer["modules"][CELL00_MODULES[0]] and
            cell00["reused_decoded_owner_receipt_source"] == {
                "path": str(PREVIOUS_CONSUMER), "bytes": 5049315, "sha256": PREVIOUS_CONSUMER_SHA256} and
            cell00["reused_decoded_owner_receipt"] == previous_consumer["modules"][DECODED],
            "Cell00 must preserve the original failed005 aggregate and its exact accepted Decoded owner.")
    decoded = cell00["reused_decoded_owner_receipt"]
    require(decoded["accepted"] is True and decoded["status"] == "NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED" and
            decoded["source_origin"]["commit"] == DECODED_PUBLICATION and decoded["owned_count"] == 4 and
            decoded["object"]["sha256"] == cell00["dependency_objects"][DECODED]["sha256"] == DECODED_OBJECT_SHA256 and
            set(decoded["stages"]) == {"normal", "replay", "audit"} and
            all(row["status"] == "PASSED" and row["exit_code"] == 0 and row["timed_out"] is False
                for row in decoded["stages"].values()),
            "Cell00 reused Decoded acceptance or original publication differs.")
    require(cell00["dependency_objects"][INPUT]["sha256"] == INPUT_OBJECT_SHA256 and
            cell00["dependency_receipts"][INPUT]["sha256"] == INPUT_RECEIPT_SHA256 and
            cell00["dependency_objects"][CANONICAL00]["sha256"] == CANONICAL00_OBJECT_SHA256 and
            cell00["dependency_receipts"][CANONICAL00]["sha256"] == CANONICAL00_RECEIPT_SHA256,
            "Cell00 prerequisite changed the accepted input or canonical00 provenance.")
    require(canonical["schema"] == "p25-canonical-cell00-stage-v1" and canonical["module"] == CANONICAL00 and
            canonical["accepted"] is True and canonical["status"] == "NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED" and
            canonical["fresh_target_object_sha256"] == CANONICAL00_OBJECT_SHA256 and
            all(canonical[label]["exit_code"] == 0 and canonical[label]["timed_out"] is False
                for label in ["normal", "replay", "audit"]),
            "The original accepted canonical00 stage changed.")
    require(historical_outer["accepted"] is False and
            historical_outer["status"] == "CANONICAL_ACCEPTED_CHARPARSE_NOT_ACCEPTED" and
            historical_outer["publication_commit"] == CANONICAL00_PUBLICATION and
            historical_outer["canonical_binding_accepted"] is True and
            historical_outer["single_cell_parse_decode_accepted"] is False and
            historical_outer["canonical_accepted_object"]["receipt_sha256"] == CANONICAL00_RECEIPT_SHA256 and
            historical_outer["canonical_accepted_object"]["sha256"] == CANONICAL00_OBJECT_SHA256,
            "The old canonical aggregate must retain its actual failed parse/decode status.")


def checked_artifact(row):
    path = Path(row["path"])
    require(path.is_absolute() and path.stat().st_size == row["bytes"] and digest(path) == row["sha256"],
            "Accepted artifact identity differs: " + str(path))
    return path


def validate_fresh_context_records(contexts, external, selected, runtime, frozen, remat_frozen):
    """Pure structural check of the three new observations and original runtime pins."""
    phases = ["before-normal-rematerialization", "after-normal-rematerialization", "after-four-consumer-gates"]
    require(len(contexts) == 3 and [row["phase"] for row in contexts] == phases,
            "Fresh context phases are missing or relabeled.")
    providers = selected["external_provider_roots"]
    require(selected["external_counts"] == {"modules": 5312, "companions": 10624,
                "runtime_pins": 15940, "providers": 9}
            and len(providers) == len(set(providers)) == 9
            and external["provider_roots"] == providers,
            "Fresh external provider order or complete scope differs.")
    entries = external["entries"]
    require(len(entries) == len({row["module"] for row in entries}) == 5312
            and sum(len(row["companions"]) for row in entries) == 10624,
            "Fresh external object/companion inventory is incomplete.")
    records = [record for row in entries for record in [row["object"], *row["companions"]]]
    require(len({row["path"] for row in records}) == 15936 and len(runtime) == 15940
            and all(runtime.get(row["path"]) == row["sha256"] for row in records),
            "Fresh external entries differ from the complete accepted runtime hashes.")
    for mapping in [frozen, remat_frozen]:
        require({path: h for path, h in mapping.items()
                 if path.startswith(("/mathlib/", "/workspace/toolchains/"))} == runtime,
                "Fresh context omitted or changed a frozen original runtime pin.")
    stable = lambda row: {k: v for k, v in row.items() if k not in {"phase", "started_utc", "finished_utc"}}
    require(all(stable(row) == stable(contexts[0]) for row in contexts),
            "Actual fresh context changed between recovery and consumer gates.")
    for row in contexts:
        require(row["schema"] == "p25-actual-fresh-external-context-v8"
                and row["module_count"] == 5312 and row["companion_count"] == 10624
                and row["runtime_pin_count"] == 15940 and row["provider_roots"] == providers
                and row["entries"] == entries and row["historical_missing_hashes_invented"] is False
                and all(isinstance(row[key], str) and row[key] for key in ["started_utc", "finished_utc"]),
                "Fresh context is incomplete or disagrees with the accepted complete snapshot.")
        for key, pin in [("source_complete_snapshot", selected["upstream_snapshot"]),
                         ("source_accepted_receipt", selected["upstream_accepted_receipt"])]:
            require(row[key]["sha256"] == pin["sha256"] and row[key]["bytes"] == pin["bytes"],
                    "Fresh context changed its accepted upstream provenance.")
    require(contexts[0]["source_complete_snapshot"] == external["source_complete_snapshot"],
            "Fresh observation and complete snapshot have different upstream sources.")
    extras = set(runtime) - {row["path"] for row in records}
    require(extras == {str(LEAN), str(CHECKER), "/mathlib/lean-toolchain", "/mathlib/lake-manifest.json"},
            "The four non-object runtime pins changed.")
    return sorted(extras)


def validate_fresh_workflow_context(cell00, selected, recovery, previous, V8):
    """Read and freeze actual v8 evidence; never execute its preflight or Lean gates."""
    paths = []
    frozen = cell00["frozen_inputs"]

    def artifact(row, expected_path=None):
        require(expected_path is None or row["path"] == str(expected_path),
                "Fresh evidence path differs from the fixed attempt008 artifact.")
        path = checked_artifact(row)
        require(path.is_file() and not path.is_symlink() and frozen.get(str(path)) == row["sha256"],
                "Actual v8 did not freeze this exact artifact: " + str(path))
        paths.append(path)
        return path

    phase = CELL00_RESULT.parent / "rematerialization"
    remat = json.loads(artifact(cell00["normal_rematerialization_receipt"], phase / "RESULT.json").read_text())
    validate_normal_accounting(cell00, remat, selected, recovery)
    require(selected["normal_order"] == V8.full_missing_order(recovery["objects"],
                set(recovery["objects"]) - set(selected["only_normal_modules"]), selected["only_normal_modules"])
            and cell00["dependency_modules_compiled"] == V8.full_missing_order(recovery["objects"],
                remat["available_objects_reused_without_normal"], selected["only_normal_modules"]),
            "Recovery normal order differs from the complete 41-object dependency graph.")
    require(cell00["fresh_context_before"] == remat["fresh_context_before"],
            "Recovery and consumers have different actual initial context records.")
    context_records = [(cell00["fresh_context_before"], CELL00_RESULT.parent / "FRESH_CONTEXT_BEFORE.json"),
                       (remat["fresh_context_after"], phase / "FRESH_CONTEXT_AFTER.json"),
                       (cell00["fresh_context_after"], CELL00_RESULT.parent / "FRESH_CONTEXT_AFTER.json")]
    contexts = [json.loads(artifact(row, path).read_text()) for row, path in context_records]
    external = json.loads(artifact(cell00["complete_external_before"],
                                  CELL00_RESULT.parent / "COMPLETE_EXTERNAL_BEFORE.json").read_text())
    runtime = {path: h for path, h in previous["frozen_inputs"].items()
               if path.startswith(("/mathlib/", "/workspace/toolchains/"))}
    extra_runtime = validate_fresh_context_records(contexts, external, selected, runtime, frozen, remat["frozen_inputs"])
    for path in extra_runtime:
        require(digest(path) == runtime[path], "Accepted runtime metadata or tool bytes changed: " + path)
        paths.append(Path(path))
    for key in ["source_complete_snapshot", "source_accepted_receipt"]:
        artifact(contexts[0][key])
    gap_paths = {row["path"] for row in cell00["historical_archive_gaps"]}
    for row in selected["historical_envelope_exceptions"]:
        if row["path"] in gap_paths:
            require(row["path"] not in frozen and row["path"] not in remat["frozen_inputs"],
                    "An unread historical envelope was falsely frozen as available.")
        else:
            artifact(row)
    restore = selected["prior_partial_restore"]
    require(cell00["prior_partial_restore"]["path"] == remat["prior_partial_restore"]["path"] == restore["path"]
            and cell00["prior_partial_restore"]["sha256"] == remat["prior_partial_restore"]["sha256"] == restore["sha256"],
            "Actual partial-restore provenance differs.")
    artifact(cell00["prior_partial_restore"])
    for module, row in recovery["objects"].items():
        dependency = cell00["dependency_objects"][module]
        require(dependency["companions"] == [], "Accepted project companion scope changed.")
        for name in [dependency["path"], dependency["isolated_path"], str(ROOT / row["source"])]:
            expected = row["source_sha256"] if name == str(ROOT / row["source"]) else row["sha256"]
            path = Path(name)
            require(path.is_file() and not path.is_symlink() and digest(path) == expected
                    and frozen.get(name) == expected, "Original dependency source/object changed: " + name)
            paths.append(path)
    for stage in remat["normal_stages"]:
        artifact(stage["object"])
        expected_log = phase / (stage["module"].split(".")[-1] + "-NORMAL.log")
        artifact({"path": stage["log"], "sha256": stage["log_sha256"], "bytes": stage["log_bytes"]}, expected_log)
        source = Path(stage["command"][-1])
        require(digest(source) == recovery["objects"][stage["module"]]["source_sha256"]
                == frozen.get(str(source)), "Exact normal source changed after recovery.")
        paths.append(source)
    return list(dict.fromkeys(paths)), {
        "rematerialization_receipt": cell00["normal_rematerialization_receipt"],
        "rematerialization_normal_modules": cell00["dependency_modules_compiled"],
        "consumer_phase_dependency_modules_compiled": [], "historical_archive_gaps": cell00["historical_archive_gaps"],
        "fresh_context_records": [row for row, _ in context_records],
        "old_v7_preflight_passed": False, "old_snapshots_synthesized": False}


def qualify_external_context(cell00, tails):
    """Reuse the existing accepted complete snapshot, including every companion."""
    global QUALIFIED_EXTERNAL
    record = cell00["complete_external_before"]
    snapshot = json.loads(checked_artifact(record).read_text())
    providers = [LEAN.parent.parent / "lib/lean", *map(Path, tails)]
    require(snapshot["schema"] == "p25-complete-current-external-snapshot-reuse-v1" and
            snapshot["provider_roots"] == list(map(str, providers)) and
            len(providers) == len(set(providers)) and
            snapshot["module_count"] == len(snapshot["entries"]) == 5312 and
            sum(len(row["companions"]) for row in snapshot["entries"]) == 10624 and
            snapshot["all_hashes_reused_from_accepted_current_snapshot"] is True and
            snapshot["historical_missing_hashes_invented"] is False,
            "Accepted complete external context or provider selection differs.")
    require(len({row["module"] for row in snapshot["entries"]}) == 5312,
            "External snapshot has duplicate module names.")
    original_record = snapshot["source_complete_snapshot"]
    require(original_record["sha256"] == "b94ab99b39a831a616d626c55c4b89c0a921d15c95319de19063d375bc982728",
            "The accepted original external snapshot selection changed.")
    original = json.loads(checked_artifact(original_record).read_text())
    require({row["module"]: (row["object"], row["companions"]) for row in original["entries"]} ==
            {row["module"]: (row["object"], row["companions"]) for row in snapshot["entries"]} and
            original["provider_roots"] == snapshot["provider_roots"],
            "Cell00 current external context differs from its accepted original snapshot.")
    for row in snapshot["entries"]:
        for artifact in [row["object"], *row["companions"]]:
            require(cell00["frozen_inputs"].get(artifact["path"]) == artifact["sha256"],
                    "Accepted Cell00 did not freeze this external object or companion.")
    QUALIFIED_EXTERNAL = {"record": record, "original_record": original_record,
                          "snapshot": snapshot, "providers": providers}
    return recheck_external_context()


def recheck_external_context():
    require(QUALIFIED_EXTERNAL is not None, "Complete accepted external context is not initialized.")
    context = QUALIFIED_EXTERNAL
    checked_artifact(context["record"])
    checked_artifact(context["original_record"])
    providers = context["providers"]
    require(all(provider.is_dir() and not (provider / "ImbalancedChen").exists() for provider in providers),
            "Unexpected external project fallback root.")
    for row in context["snapshot"]["entries"]:
        relative = row["module"].replace(".", "/") + ".olean"
        found = [provider / relative for provider in providers if (provider / relative).is_file()]
        require([str(path) for path in found] == [row["object"]["path"]],
                "Missing or shadowed accepted external object: " + row["module"])
        checked_artifact(row["object"])
        companions = [str(found[0]) + suffix for suffix in [".private", ".server"]
                      if Path(str(found[0]) + suffix).is_file()]
        require(companions == [item["path"] for item in row["companions"]],
                "Accepted external companion inventory changed: " + row["module"])
        for companion in row["companions"]:
            checked_artifact(companion)
    return {"source_accepted_cell00_receipt_sha256": CELL00_RESULT_SHA256,
            "complete_snapshot": context["record"], "original_snapshot": context["original_record"],
            "module_count": 5312, "companion_count": 10624,
            "historical_missing_hashes_invented": False}


def check_disk_space(required, purpose):
    free = shutil.disk_usage(ROOT).free
    require(free >= required, f"DISK_SPACE: {purpose}: {free} bytes free; require {required}.")
    return {"purpose": purpose, "free_bytes": free, "required_free_bytes": required}


def frozen_snapshot(B, U, paths, rows, publication):
    require(output(["git", "rev-parse", "HEAD"]) == publication, "Published worktree HEAD changed")
    require(not output(["git", "status", "--porcelain", "--untracked-files=no"]),
            "Published tracked worktree changed")
    require(output(["git", "rev-parse", "HEAD"], MATHLIB) == MATHLIB_PIN, "Mathlib pin changed")
    require(Path("/workspace/compile-deps/mathlib").resolve() == MATHLIB.resolve(),
            "Mathlib alias changed")
    external = recheck_external_context()
    return {"files": {str(path): B.file_snapshot(path) for path in paths},
            "inputs": U.input_snapshot(rows), "publication": publication,
            "mathlib_pin": MATHLIB_PIN, "mathlib_path": str(MATHLIB.resolve()),
            "complete_external_context": external}


def run_stage(label, target, graph, objects, shared_paths, rows, publication,
              published, out, B, U, parse_audit, template, shared_reference):
    """One target receives its own durable receipt and separate union library."""
    require(target in FRESH_MODULES, "Only the two fresh Cell01 owners may run compiler gates.")
    initial_space = check_disk_space(GATE_WORKING_HEADROOM_BYTES, "before fresh Cell01 stage directory")
    stage = out / label
    stage.mkdir()
    receipt_path = stage / "RESULT.json"
    state = {"schema": "p25-canonical-cell01-stage-v1", "module": target, "accepted": False,
             "status": "PREPARING", "source_sha256": graph[target]["sha256"],
             "project_closure": sorted(graph), "dependency_objects": objects,
             "strict_flags": STRICT_FLAGS, "phase_wall_limits_seconds": 180,
             "fresh_readFile_this_stage": False,
             "input_binding": "Transitive reuse of exact accepted OriginalInput and, for binding, the accepted loader object.",
             "disk_checks": [initial_space],
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
        state["disk_checks"].append(check_disk_space(
            sum(Path(info["path"]).stat().st_size for info in objects.values()) + GATE_WORKING_HEADROOM_BYTES,
            "immediately before exact Cell01 dependency copies"))
        saved(receipt_path, state)
        for name, info in objects.items():
            require(not any(Path(info["path"] + suffix).exists() for suffix in [".private", ".server"]),
                    "Unexpected accepted project companion; separate reviewed inventory required.")
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
            state["disk_checks"].append(check_disk_space(GATE_WORKING_HEADROOM_BYTES,
                                                        "immediately before " + target + "/" + phase))
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
        goals = set(REQUIRED_PUBLIC_NAMES[target])
        external_imports = {name for name in parsed["imports"] if not name.startswith("ImbalancedChen.")}
        require(external_imports <= {row["module"] for row in QUALIFIED_EXTERNAL["snapshot"]["entries"]},
                "Actual Cell01 audit imported an external module outside the accepted complete context.")
        state["actual_external_import_count"] = len(external_imports)
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
        print("P25_CELL01_STAGE_RESULT " + json.dumps({"stage": label, "status": state["status"],
              "accepted": state["accepted"], "receipt": str(receipt_path),
              "receipt_sha256": digest(receipt_path)}), flush=True)
    if not state["accepted"]:
        return None
    return {"path": str(target_object), "sha256": digest(target_object),
            "receipt": str(receipt_path), "receipt_sha256": digest(receipt_path),
            "stage_directory": str(stage), "accepted": True}


def main():
    require_workflow_ready()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("publication_commit", help="Full already-fetched commit; no network operation")
    args = parser.parse_args()
    require(ROOT.is_dir() and not ROOT.is_symlink(), "Fixed own worktree absent or symlinked")
    out = ROOT / ATTEMPT
    require(not out.exists(), "Preserve the existing attempt; do not overwrite evidence")
    require(out.parent.resolve().is_relative_to(ROOT.resolve()), "Output parent leaves fixed root")
    initial_space = check_disk_space(MIN_INITIAL_FREE_BYTES, "before fresh Cell01 output")
    out.mkdir(parents=True)
    receipt_path = out / "RESULT.json"
    state = {"schema": "p25-canonical-cell01-two-stage-v1", "accepted": False, "status": "PREPARING",
             "publication_commit": args.publication_commit, "previous_commit": PREVIOUS_COMMIT,
             "loader_accepted": False, "cell01_canonical_binding_accepted": False,
             "cell01_parse_decode_accepted": False, "original_input_recompiled": False,
             "accepted_cell00_gates_rerun": [], "accepted_dependency_gates_rerun": [],
             "private_records_written": False, "disk_checks": [initial_space],
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
                  BASE_RUNNER: BASE_RUNNER_SHA256, INPUT_RUNNER: INPUT_RUNNER_SHA256,
                  ADAPTED_FROM: ADAPTED_FROM_SHA256, CELL00_DRIVER: CELL00_RUNNER_SHA256,
                  CELL00_VALIDATOR_DRIVER: CELL00_VALIDATOR_SHA256,
                  CELL00_SELECTION: CELL00_SELECTION_SHA256, RECOVERY_SELECTION: RECOVERY_SELECTION_SHA256}
        pinned.update(source_manifest["protected_current_source_and_gate_sha256"])
        for row in source_manifest["modules"].values():
            pinned[row["path"]] = row["sha256"]
        pinned.update(manifest["gate_sources"])
        published = {path: publication_bytes(args.publication_commit, path) for path in pinned}
        for path, expected in pinned.items():
            require(sha(published[path]) == expected, "Published source/gate differs: " + path)
        graphs = source_graphs(source_manifest, published)
        require(digest(CELL00_RESULT) == CELL00_RESULT_SHA256, "Actual Cell00 prerequisite receipt bytes differ.")
        canonical_path = CANONICAL00_ROOT / "canonical/RESULT.json"
        canonical_outer_path = CANONICAL00_ROOT / "RESULT.json"
        require(digest(canonical_path) == CANONICAL00_RECEIPT_SHA256 and
                digest(canonical_outer_path) == CANONICAL00_OUTER_SHA256, "Original canonical00 workflow evidence changed.")
        cell00 = json.loads(CELL00_RESULT.read_text())
        canonical = json.loads(canonical_path.read_text())
        canonical_outer = json.loads(canonical_outer_path.read_text())
        require(digest(PREVIOUS_CONSUMER) == PREVIOUS_CONSUMER_SHA256 and
                digest(DISK_FAILURE) == DISK_FAILURE_SHA256, "Prior failed Cell00 aggregate identity differs.")
        previous_consumer = json.loads(PREVIOUS_CONSUMER.read_text())
        disk_failure = json.loads(DISK_FAILURE.read_text())
        V6 = import_exact("p25_cell00_v6_receipt_reuse", ROOT / CELL00_VALIDATOR_DRIVER, CELL00_VALIDATOR_SHA256)
        V6.validate_failed_consumer(disk_failure)
        V6.validate_failed_parse(previous_consumer, disk_failure)
        validate_workflow_receipts(cell00, canonical, canonical_outer, previous_consumer)
        V8 = import_exact("p25_cell00_v8_order_reuse", ROOT / CELL00_DRIVER, CELL00_RUNNER_SHA256)
        fresh_paths, fresh_evidence = validate_fresh_workflow_context(cell00,
            json.loads(published[CELL00_SELECTION]), json.loads(published[RECOVERY_SELECTION]), previous_consumer, V8)
        parse_owner = cell00["modules"][CELL00_MODULES[0]]
        require(V6.validate_parse_helpers(parse_owner["owned_declarations"]) ==
                parse_owner["private_expression_helpers"] == cell00["private_parse_helper_records"],
                "Cell00 actual owned inventory must include the three reviewed private parse wrappers.")
        workflow_owners = {**cell00["modules"], DECODED: cell00["reused_decoded_owner_receipt"]}
        workflow_paths = [CELL00_RESULT, canonical_path, canonical_outer_path,
                          checked_artifact(cell00["runner"]), PREVIOUS_CONSUMER, DISK_FAILURE,
                          ROOT / CELL00_DRIVER, checked_artifact(previous_consumer["runner"]),
                          checked_artifact(previous_consumer["exception_log"]),
                          checked_artifact(disk_failure["exception_log"]), *fresh_paths]
        for module, owner in workflow_owners.items():
            for key in ["source_copy", "object", "audit_source", "declarations", "inventory"]:
                workflow_paths.append(checked_artifact(owner[key]))
            for companion in owner.get("object_companions", []):
                workflow_paths.append(checked_artifact(companion))
            for row in owner["stages"].values():
                log = Path(row["log"])
                require(digest(log) == row["log_sha256"] and log.stat().st_size == row["log_bytes"],
                        "Actual accepted Cell00 stage log identity differs.")
                workflow_paths.append(log)
        for relative, expected in canonical["artifacts"].items():
            path = canonical_path.parent / relative
            require(digest(path) == expected, "Original accepted canonical00 artifact differs.")
            workflow_paths.append(path)
        state["cell00_workflow_prerequisite"] = {"receipt": str(CELL00_RESULT), "sha256": CELL00_RESULT_SHA256,
            "publication_commit": CELL00_PUBLICATION, "accepted": True, "cell00_gates_rerun": [],
            "fresh_owner_order": CELL00_MODULES, "reused_decoded_original_publication": DECODED_PUBLICATION,
            "previous_failed_consumer_receipt": str(PREVIOUS_CONSUMER),
            "previous_failed_consumer_sha256": PREVIOUS_CONSUMER_SHA256, "previous_consumer_accepted": False}
        state["cell00_fresh_context_provenance"] = fresh_evidence
        state["original_canonical00_workflow"] = {"accepted_stage_receipt": str(canonical_path),
            "accepted_stage_sha256": CANONICAL00_RECEIPT_SHA256, "historical_outer_receipt": str(canonical_outer_path),
            "historical_outer_sha256": CANONICAL00_OUTER_SHA256, "historical_outer_accepted": False}
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
            manifest, graphs[BINDING], B, U, parse_audit, rows)
        for module, owner in workflow_owners.items():
            parsed = parse_audit(Path(owner["stages"]["audit"]["log"]), module, set(owner["actual_project_closure"]))
            require(parsed["declarations"] == owner["owned_declarations"] and
                    parsed["declaration_count"] == owner["owned_count"],
                    "Actual Cell00 prerequisite full owned audit differs from its receipt.")
        state["complete_external_context"] = qualify_external_context(cell00, U.MATHLIB_PATHS)
        state["accepted_dependency_evidence"] = evidence
        state["input_snapshot_before_advance"] = before
        state["accepted_dependency_objects_before_advance"] = {
            name: B.file_snapshot(info["path"]) for name, info in objects.items()}
        saved(receipt_path, state)
        actual_copy_bytes = 2 * sum(Path(info["path"]).stat().st_size for info in objects.values())
        free = shutil.disk_usage(out).free
        state["disk_preflight"] = {"free_bytes": free, "known_dependency_copy_bytes": actual_copy_bytes,
                                   "new_target_sizes_not_predicted": True}
        require(free >= max(MIN_INITIAL_FREE_BYTES, actual_copy_bytes + GATE_WORKING_HEADROOM_BYTES),
                "Insufficient live disk for both exact OriginalInput copies and working headroom")
        old_dependencies = {str(path): B.file_snapshot(path) for path in dependency_paths
                            if path not in {ROOT / row["source_path"] for row in graphs[BINDING].values()}}
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
            *workflow_paths, LEAN, CHECKER, LEAN.parent.parent / "lib/lean/Lean.olean",
            LEAN.parent.parent / "lib/lean/Lean/Util/CollectAxioms.olean", *dependency_paths]))
        for path in U.MATHLIB_PATHS:
            require(Path(path).is_dir(), "Approved Mathlib dependency library missing")
        shared_reference = frozen_snapshot(B, U, shared_paths, rows, args.publication_commit)
        require(shared_reference["inputs"] == before, "Original inputs changed before stage preparation")
        state["shared_frozen_context"] = shared_reference
        saved(receipt_path, state)
        a_objects = {INPUT: objects[INPUT]}
        first = run_stage("loader", LOADER, graphs[LOADER], a_objects, shared_paths,
                          rows, args.publication_commit, published, out, B, U, parse_audit,
                          published[B.AUDIT_TEMPLATE], shared_reference)
        if first is None:
            state["status"] = "LOADER_NOT_ACCEPTED_CELL01_BINDING_NOT_STARTED"
            return 1
        state["loader_accepted"] = True
        state["loader_accepted_object"] = first
        state["status"] = "LOADER_ACCEPTED_CELL01_BINDING_PENDING"
        saved(receipt_path, state)
        # Stage A is finalized above. Stage B reads/copies it without changing
        # any A artifact or receipt, including when B fails or times out.
        a_paths = [p for p in Path(first["stage_directory"]).rglob("*") if p.is_file()]
        require(frozen_snapshot(B, U, shared_paths, rows, args.publication_commit) == shared_reference,
                "Accepted shared context changed after the loader stage")
        second_reference = frozen_snapshot(B, U, [*shared_paths, *a_paths], rows, args.publication_commit)
        second_objects = {**objects, LOADER: first}
        second = run_stage("binding", BINDING, graphs[BINDING], second_objects,
                           [*shared_paths, *a_paths], rows, args.publication_commit, published,
                           out, B, U, parse_audit, published[B.AUDIT_TEMPLATE], second_reference)
        require(digest(Path(first["receipt"])) == first["receipt_sha256"]
                and digest(Path(first["path"])) == first["sha256"],
                "Stage B changed the already accepted loader evidence")
        if second is None:
            state["status"] = "LOADER_ACCEPTED_CELL01_BINDING_NOT_ACCEPTED"
            return 1
        state["cell01_canonical_binding_accepted"] = True
        state["cell01_binding_accepted_object"] = second
        require(frozen_snapshot(B, U, shared_paths, rows, args.publication_commit) == shared_reference,
                "Accepted shared context changed before final acceptance")
        state["accepted"] = True
        state["status"] = "LOADER_AND_CELL01_CANONICAL_BINDING_ACCEPTED"
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
        print("P25_CELL01_RESULT " + json.dumps({key: state[key] for key in [
            "status", "accepted", "loader_accepted", "cell01_canonical_binding_accepted",
            "Q96_proved", "P2_5_proved"]}), flush=True)
        print("P25_CELL01_RECEIPT " + str(receipt_path) + " " + digest(receipt_path), flush=True)
    return 0 if state["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())

