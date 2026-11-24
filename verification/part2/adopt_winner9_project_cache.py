#!/usr/bin/env python3
"""Adopt only source/import/runtime-qualified T01 project cache candidates.

Run after a complete native qualification and a zero-budget owner-closure pass
of the private driver. Existing valid records remain untouched. No old project
record is upgraded: a new historical-cache record requires its own original
guarded checkpoint row and exact current actual import artifacts. This command
does not run a source compiler or the kernel and grants no proof acceptance.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
import json
from pathlib import Path
import subprocess

from qualify_winner9_native_cache import Qualification, atomic_missing, read, write, LOAD_SUFFIXES
from run_winner9_private_checks import CACHE_SCHEMA, EXTERNAL_CACHE_SCHEMA, closure_signature, imports, json_digest
from run_winner9_private_audit import project_nodes, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes, native, require
import repack_winner9_native_cache as carrier


def source_snapshot(qualifier: Qualification, nodes: dict, toolchain: dict, external: dict) -> dict:
    project = {}
    for name, node in nodes.items():
        source = node["source"]
        obj = qualifier.private_lib / (name.replace(".", "/") + ".olean")
        require(obj.is_file(), "Current project dependency object is missing: " + name)
        project[name] = {"source": str(source.relative_to(qualifier.project)),
                         "source_sha256": qualifier.hashes.digest(source), "object": str(obj),
                         "object_sha256": qualifier.hashes.digest(obj)}
    return {"project": project, "toolchain": toolchain, "lean_binary_sha256": toolchain["lean_binary_sha256"],
            "external_snapshot": external}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", type=Path, required=True)
    parser.add_argument("--external-snapshot", type=Path, required=True)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--baseline-root", type=Path, default=Path("/workspace/goldbach-p2"))
    parser.add_argument("--mathlib-root", type=Path, default=Path("/workspace/compile-deps/mathlib"))
    parser.add_argument("--toolchain-root", type=Path, default=Path("/workspace/toolchains/lean-4.33.0-rc1-linux"))
    args = parser.parse_args()
    qualifier = Qualification(args)
    pin = qualifier.request["locked_packages"]["mathlib"]["rev"]
    external = ExternalSnapshot(args.external_snapshot, lean=str(qualifier.lean), mathlib_pin=pin,
                                project_lib=qualifier.private_lib)
    before = external.binding()
    require(external.value["runtime"]["lean_path"] == list(map(str, qualifier.paths)),
            "The original checkpoint adapter and native snapshot select different actual roots")
    require(external.value["qualification"]["status"] == "ALL_REQUIRED_NATIVE_PROVIDERS_QUALIFIED",
            "Project cache reuse requires the complete native context")
    toolchain = {"lean_version": subprocess.check_output([str(qualifier.lean), "--version"], text=True).strip(),
                 "lean_binary_sha256": qualifier.hashes.digest(qualifier.lean), "mathlib_commit": pin}
    path = qualifier.project / ".lake/p2-private/records.json"
    original_raw = path.read_bytes() if path.exists() else None
    original = json.loads(original_raw) if original_raw else {}
    records = deepcopy(original)
    adoption_root = qualifier.stage / "project-adoptions"
    adoption_root.mkdir(exist_ok=True)
    attempt = adoption_root / f"attempt-{len(list(adoption_root.glob('attempt-*'))) + 1:03}"
    attempt.mkdir()
    adopted, skipped, blocked = {}, {}, {}
    nodes = {name: {"source": qualifier.project / wanted["source_path"],
                    "deps": [dep for dep in wanted["direct_imports"] if dep.startswith("ImbalancedChen.")]}
             for name, wanted in qualifier.request["requested"].items() if wanted["package"] == "project"}
    mark_project_nodes(nodes, set(external.modules))
    for name in qualifier.census["topological_order"]:
        if name not in nodes:
            continue
        try:
            closure = project_nodes(qualifier.project, name)
            require(set(closure) <= set(nodes), "Project source closure escaped the frozen request")
            for module, row in closure.items():
                wanted = qualifier.request["requested"][module]
                require(qualifier.hashes.digest(row["source"]) == wanted["source_sha256"]
                        and row["deps"] == [dep for dep in wanted["direct_imports"] if dep.startswith("ImbalancedChen.")],
                        "Current project source/imports changed after the request: " + module)
            try:
                verify_compilation(records, closure, source_snapshot(qualifier, closure, toolchain, before))
            except (OSError, ValueError, KeyError):
                pass
            else:
                skipped[name] = "CURRENT_VALID_COMPILE_RECORD_RETAINED"
                continue
            require(name in qualifier.selected and qualifier.selected[name]["original_classification"] == carrier.PROJECT_CLASSIFIED,
                    "No matching original completed guarded project row")
            source = nodes[name]["source"]
            require(qualifier.hashes.digest(source) == qualifier.selected[name]["source"]["sha256"],
                    "Original compiled source differs from the selected current postimage")
            dependencies = {module: row for module, row in closure.items() if module != name}
            verify_compilation(records, dependencies, source_snapshot(qualifier, dependencies, toolchain, before))
            row, setup, setup_path, trace_path = qualifier.original(name)
            mapped, actual_imports = qualifier.inputs(name, row, setup, exact_original=True)
            actual_native = {module for module in actual_imports if native(module)}
            require(not actual_native or nodes[name]["requires_external"],
                    "Actual checkpoint imports contain native ancestry missing from the source graph")
            require(not mapped["dynlibs"] and not mapped["plugins"], "Project cache would load native executable code")
            stem = qualifier.stage / "candidates/project/.lake/build/lib/lean" / name.replace(".", "/")
            facets = []
            for suffix in LOAD_SUFFIXES:
                candidate = Path(str(stem) + suffix)
                if not candidate.is_file():
                    continue
                destination = qualifier.private_lib / (name.replace(".", "/") + suffix)
                expected = qualifier.hashes.digest(candidate)
                require(not destination.exists() or qualifier.hashes.digest(destination) == expected,
                        "An existing different project object must be retained for explicit diagnosis")
                facets.append((candidate, destination, expected))
            require(any(destination.suffix == ".olean" for _, destination, _ in facets), "Missing original public project object")
            for candidate, destination, expected in facets:
                atomic_missing(destination, candidate.read_bytes(), expected)
            obj = qualifier.private_lib / (name.replace(".", "/") + ".olean")
            deps = nodes[name]["deps"]
            record = {"module": name, "source": str(source.relative_to(qualifier.project)),
                      "source_sha256": qualifier.hashes.digest(source), "object": str(obj),
                      "object_sha256": qualifier.hashes.digest(obj), "exit_code": 0,
                      "deps": {dep: records[dep]["object_sha256"] for dep in deps},
                      "dependency_signatures": {dep: records[dep]["closure_signature"] for dep in deps},
                      "cache_schema": EXTERNAL_CACHE_SCHEMA if nodes[name]["requires_external"] else CACHE_SCHEMA,
                      "toolchain": toolchain, "new_strict_compile": False,
                      "provenance": "original guarded T01 project checkpoint, exact current source/import/runtime rebind",
                      "original_checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
                      "original_classification": carrier.PROJECT_CLASSIFIED}
            if nodes[name]["requires_external"]:
                # Provisional in-memory records let later candidates bind their
                # provenanced parents. Nothing is published until final checks.
                record["external_snapshot"] = before
                record["external_check"] = {"status": "PASSED_BATCH_PRE_POST", "before": before, "after": before}
            record["closure_signature"] = closure_signature(record)
            trace_copy = attempt / "original-traces" / (name + ".trace.json")
            atomic_missing(trace_copy, trace_path.read_bytes(), qualifier.hashes.digest(trace_path))
            adopted_row = {"source_sha256": record["source_sha256"], "object_sha256": record["object_sha256"],
                             "original_guarded_row_index": qualifier.selected[name]["original_guarded_row_index"],
                             "original_import_map_sha256": row["actual_import_map_sha256"],
                             "actual_import_map": actual_imports, "actual_import_map_sha256": json_digest(actual_imports),
                             "original_setup": str(setup_path), "original_setup_sha256": qualifier.hashes.digest(setup_path),
                             "original_trace": str(trace_path), "original_trace_text_copy": str(trace_copy),
                             "original_trace_sha256": qualifier.hashes.digest(trace_path),
                             "closure_signature": record["closure_signature"], "new_strict_compile": False,
                             "kernel_credit": False}
            print("PROJECT_CACHE_CANDIDATE", name, flush=True)
            # Publish the provisional item only after all fallible artifact
            # preparation and output. A caught late OSError must leave neither
            # an accepted record nor an incomplete adoption entry in memory.
            records[name] = record
            adopted[name] = adopted_row
        except (OSError, ValueError, KeyError) as error:
            blocked[name] = str(error)
    qualifier.recheck()
    after = external.verify()
    require(after == before, "Native inputs changed during the project cache adoption batch")
    for name in adopted:
        closure = project_nodes(qualifier.project, name)
        verify_compilation(records, closure, source_snapshot(qualifier, closure, toolchain, before))
    require((path.read_bytes() if path.exists() else None) == original_raw,
            "Another writer changed the compile registry; do not overwrite its work")
    receipt = {"schema": "p2-winner9-original-project-cache-adoption-v1", "status": "EXACT_SOURCE_IMPORT_RUNTIME_REBIND_ONLY",
               "request_sha256": carrier.file_sha(qualifier.stage / "REQUEST.json"),
               "checkpoint_sha256": carrier.ARTIFACT["checkpoint_sha256"],
               "script_sha256": carrier.file_sha(Path(__file__)), "external_before": before, "external_after": after,
               "adopted": adopted, "existing_valid_records_retained": skipped, "not_adopted": blocked,
               "source_compiler_invocations": 0, "new_strict_compile_credit": False, "kernel_credit": False}
    receipt_path = attempt / "PROJECT_CACHE_ADOPTION.json"
    write(receipt_path, receipt)
    qualification_sha = carrier.file_sha(receipt_path)
    for name in adopted:
        records[name]["checkpoint_cache_qualification"] = {"path": str(receipt_path.resolve()),
                                                          "sha256": qualification_sha}
    if adopted:
        temporary = path.with_suffix(".project-adoption.tmp")
        require(not temporary.exists(), "A previous project cache transaction needs diagnosis")
        temporary.write_text(json.dumps(records, sort_keys=True, indent=2) + "\n")
        temporary.replace(path)
    print(json.dumps({"adopted": len(adopted), "retained": len(skipped), "not_adopted": len(blocked),
                      "receipt": str(receipt_path), "source_compiler_invocations": 0, "kernel_credit": False}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
