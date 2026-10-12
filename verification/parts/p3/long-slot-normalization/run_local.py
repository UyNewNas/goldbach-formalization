#!/usr/bin/env python3
"""Explicit, single-module gates; never build or modify prerequisite caches.

Use the unchanged P0 frontend driver with stock pinned Lake, or the stock
leanchecker.  This local receipt does not replace the complete Part 3 verifier.
The runtime configuration points to an independently copied project overlay and
the matching read-only dependency caches.  Every invocation hashes its complete
expected import inventory before and after execution.  The Lean audit then
confirms those paths against the imported environment and Lean.findOLean.
"""

from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import time

TARGET = "ImbalancedChen.Part3LongSlotNormalization"
AUDIT = "verification.parts.p3.LongSlotNormalizationAudit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def object_parts(path):
    path = Path(path)
    candidates = [path, Path(str(path) + ".server"), Path(str(path) + ".private"),
                  path.with_suffix(".ir"), path.with_suffix(".ir.sig")]
    return [p for p in candidates if p.is_file()]


def resolve(config, module):
    top = module.split(".")[0]
    relative = Path(*module.split(".")).with_suffix(".olean")
    # Exact root selection in the pinned Lean.SearchPath.findWithExt.
    for root_name in config["search_roots"]:
        root = Path(root_name)
        if (root / top).is_dir() or (root / top).with_suffix(".olean").exists():
            return root / relative
    raise RuntimeError("No Lean namespace root for " + module)


def capture(config, modules):
    paths = set()
    layout = []
    for record in modules:
        name = record["module"]
        obj = resolve(config, name)
        if not obj.is_file():
            raise RuntimeError("Missing resolved import object: " + str(obj))
        if str(obj) != record["resolved_olean"]:
            raise RuntimeError("Object resolution changed for " + name)
        parts = object_parts(obj)
        source = Path(record["source"])
        paths.add(source)
        paths.update(parts)
        layout.append({"module": name, "source": str(source),
                       "olean": str(obj), "parts": list(map(str, parts))})
    ordered = sorted(paths)
    with ThreadPoolExecutor(max_workers=4) as pool:
        hashes = dict(zip(map(str, ordered), pool.map(digest, ordered)))
    for record in modules:
        if hashes[record["source"]] != record["source_sha256"]:
            raise RuntimeError("Import source changed: " + record["module"])
    return {"modules": layout, "sha256": hashes}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["compile", "replay", "audit"])
    parser.add_argument("--runtime-config", required=True, type=Path)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    config = json.loads(args.runtime_config.read_text())
    repo = Path(config["repo"])
    target_source = repo / Path(*TARGET.split(".")).with_suffix(".lean")
    module = AUDIT if args.action == "audit" else TARGET
    source = repo / Path(*module.split(".")).with_suffix(".lean")
    target_object = resolve(config, TARGET)
    output = Path(config["overlay_object_root"]) / Path(*module.split(".")).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    closure = json.loads(Path(config["source_closure_manifest"]).read_text())
    imports = list(closure["modules"])
    if args.action == "audit":
        imports.append({"module": TARGET, "source": str(target_source),
                        "source_sha256": digest(target_source),
                        "resolved_olean": str(target_object)})
    if len({r["module"] for r in imports}) != len(imports):
        raise RuntimeError("Duplicate expected import module")
    for path, record in config["stock_tools_and_driver"].items():
        if digest(path) != record["sha256"]:
            raise RuntimeError("Pinned tool or unchanged frontend driver changed: " + path)
    if config["missing_dependency_objects"]:
        raise RuntimeError("Unmet dependencies; this runner never starts a build")
    if not all(p["matches"] and not p["tracked_status"] for p in closure["package_pins"]):
        raise RuntimeError("Dependency source pin mismatch")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    stem = stamp + "-" + args.action
    logfile = args.output_dir / (stem + ".log")
    before = capture(config, imports)
    snapshot_file = args.output_dir / (stem + "-imports.json")
    # Complete, compact inventory; every path and hash is retained.
    snapshot_file.write_text(json.dumps(before, separators=(",", ":")) + "\n")
    toolroot = Path(config["toolroot"])
    if args.action == "replay":
        command = [str(toolroot / "bin/leanchecker"), "--verbose", TARGET]
    else:
        command = [str(toolroot / "bin/lake"), "-d", config["driver"],
                   "-f", "lakefile.lean", "script", "run", "compileOne",
                   str(source), module, str(output), "strict"]
    env = os.environ.copy()
    env.update(config["environment"])
    env["PATH"] = str(toolroot / "bin") + os.pathsep + env.get("PATH", "")
    record = {"action": args.action, "module": module, "command": command,
              "cwd": str(repo), "started_utc": stamp,
              "source": str(source), "source_sha256_before": digest(source),
              "production_source_sha256_before": digest(target_source),
              "target_parts_before": {str(p): digest(p) for p in object_parts(target_object)},
              "runtime_config_sha256": digest(args.runtime_config),
              "runner_sha256": digest(Path(__file__)),
              "environment": config["environment"],
              "trustLevel": None if args.action == "replay" else 0,
              "warningAsError": args.action != "replay",
              "import_snapshot": str(snapshot_file),
              "import_snapshot_sha256": digest(snapshot_file),
              "import_module_count": len(imports),
              "import_source_and_object_file_count": len(before["sha256"])}
    print("START " + args.action + " " + module, flush=True)
    start = time.monotonic()
    with logfile.open("w") as stream:
        stream.write(json.dumps(record) + "\n")
        stream.flush()
        run = subprocess.run(command, cwd=repo, env=env, stdout=stream,
                             stderr=subprocess.STDOUT)
    record.update(returncode=run.returncode, elapsed_seconds=round(time.monotonic()-start, 3),
                  log=str(logfile), log_sha256=digest(logfile),
                  source_sha256_after=digest(source),
                  production_source_sha256_after=digest(target_source),
                  target_parts_after={str(p): digest(p) for p in object_parts(target_object)})
    after = capture(config, imports)
    failures = []
    if run.returncode:
        failures.append("tool_exit_nonzero")
    if record["source_sha256_before"] != record["source_sha256_after"]:
        failures.append("source_changed")
    if record["production_source_sha256_before"] != record["production_source_sha256_after"]:
        failures.append("production_source_changed")
    changed = sorted(p for p in set(before["sha256"]) | set(after["sha256"])
                     if before["sha256"].get(p) != after["sha256"].get(p))
    record["import_hash_changes"] = changed
    record["import_layout_unchanged"] = before["modules"] == after["modules"]
    record["all_import_sources_and_object_parts_unchanged"] = before == after
    if before != after:
        failures.append("import_sources_or_objects_changed")
    if args.action in ("replay", "audit") and record["target_parts_before"] != record["target_parts_after"]:
        failures.append("production_object_changed")
    log = logfile.read_text()
    if args.action == "replay":
        record["replay_line_present"] = bool(re.search(r"^replaying " + re.escape(TARGET) + r"$", log, re.MULTILINE))
        if not record["replay_line_present"]:
            failures.append("missing_production_replay_line")
    else:
        if "FRONTEND_OK module=" + module + " trustLevel=0" not in log:
            failures.append("missing_successful_strict_frontend_marker")
        if not output.is_file():
            failures.append("missing_output_object")
    if args.action == "audit" and not run.returncode:
        def rows(prefix):
            return [json.loads(line[len(prefix):]) for line in log.splitlines()
                    if line.startswith(prefix)]
        actual = rows("PART3_LOCAL_IMPORT ")
        expected = {r["module"]: r["olean"] for r in before["modules"]}
        observed = {r["module"]: r["olean"] for r in actual}
        record["actual_lean_import_count"] = len(actual)
        record["actual_imports_match_predicted_paths"] = observed == expected and len(actual) == len(observed)
        if not record["actual_imports_match_predicted_paths"]:
            record["actual_import_differences"] = {"unexpected": sorted(set(observed)-set(expected)),
                "missing": sorted(set(expected)-set(observed)),
                "path_mismatch": [m for m in expected.keys() & observed.keys() if expected[m] != observed[m]]}
            failures.append("actual_import_inventory_mismatch")
        declarations = rows("PART3_LOCAL_DECL ")
        module_counts = rows("PART3_LOCAL_MODULE ")
        counts = [int(line.split()[-1]) for line in log.splitlines() if line.startswith("PART3_LOCAL_COUNT ")]
        if counts != [len(declarations)] or module_counts != [{"module": TARGET, "count": len(declarations)}]:
            failures.append("declaration_module_count_mismatch")
        if len({d["name"] for d in declarations}) != len(declarations):
            failures.append("duplicate_declaration")
        required = {"ImbalancedChen.part3_eventually_longSlot_logAccuracy",
                    "ImbalancedChen.part3_eventually_longSlot_singularNormalization"}
        if not required <= {d["name"] for d in declarations}:
            failures.append("missing_requested_theorem")
        for declaration in declarations:
            if declaration["module"] != TARGET or declaration["kind"] == "axiom" or not set(declaration["axioms"]) <= ALLOWED_AXIOMS:
                failures.append("forbidden_declaration_or_transitive_axiom")
            if any("⋯" in declaration[key] for key in ("type", "readable_type")):
                failures.append("truncated_type")
        record["owned_declaration_count"] = len(declarations)
        write_json(args.output_dir / (stem + "-compiler-declarations.json"), declarations)
        write_json(args.output_dir / (stem + "-actual-imports.json"), actual)
    record["verification_failure_reasons"] = failures
    record["scoped_gate_passed"] = not failures
    write_json(args.output_dir / (stem + "-receipt.json"), record)
    print(json.dumps({k: record[k] for k in ["action", "returncode", "elapsed_seconds",
        "scoped_gate_passed", "verification_failure_reasons", "log"]}), flush=True)
    if failures:
        print("\n".join(log.splitlines()[-40:]), flush=True)
    return 0 if not failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
