#!/usr/bin/env python3
"""Restore the fixed 93-object P2.10 environment; grant no new proof credit.

Run only in an isolated, otherwise idle CI worktree. The workflow verifies and
installs the three public helper objects and the original SeedTypes Lake files.
This program does not download objects, invent Lake traces, change source, or
rewrite historical compilation records. It invokes only ordinary Lake builds
of the 90 historical baseline modules, skipping every already exact object.
The current source tree has 17 symlinks and 73 regular files in that group;
both require the historical Lake package/module setup.

Before each new build, Lake's --no-build check of the same module's :deps facet
must succeed. That facet uses the same presetup dependency job as :leanArts.
Existing exact objects and their original traces are frozen around both calls.
No other process may mutate this worktree while this program is running.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import importlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


REFERENCE_SHA = "ee3d1b8d4dd962ba4195b90299062ab972de82422cb24114822a1a5442e77689"
LEAN_SHA = "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
CHECKER_SHA = "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"
LEAN = Path("/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean")
LAKE = LEAN.with_name("lake")
MATHLIB = Path("/workspace/compile-deps/mathlib")
PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
HELPERS = {"ImbalancedChen.P2Winner9" + suffix for suffix in (
    "RowArithmeticChecker", "SelectedArchiveChecker", "MaterializedLogChecker")}
DRIVERS = {
    "run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
    "winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
}
CONFIG = {
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
}


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def regular(path):
    need(path.is_file() and not path.is_symlink(), "Missing/nonregular file: " + str(path))


def stem(directory, module):
    return directory / module.replace(".", "/")


def suffix(path, extension):
    return Path(str(path) + extension)


def lake_files(root, module):
    lib = stem(root / ".lake/build/lib/lean", module)
    ir = stem(root / ".lake/build/ir", module)
    return [suffix(lib, x) for x in (".olean", ".olean.hash", ".ilean", ".ilean.hash", ".trace")] + [
        suffix(ir, x) for x in (".c", ".c.hash", ".setup.json")]


def exact_lake_object(root, module, record):
    paths = lake_files(root, module)
    for path in paths:
        regular(path)
    need(sha(paths[0]) == record["object_sha256"], "Historical object SHA mismatch: " + module)
    trace = json.loads(paths[4].read_bytes())
    setup = json.loads(paths[7].read_bytes())
    need(trace.get("synthetic") is False and trace.get("schemaVersion") == "2025-09-10",
         "Missing original successful Lake trace: " + module)
    need(setup.get("name") == module and setup.get("package") == "imbalancedChen"
         and setup.get("isModule") is False and setup.get("options") == {},
         "Unexpected Lake module setup: " + module)
    outputs = trace.get("outputs", {})
    need(outputs.get("m") is False, "Expected a legacy single-olean module: " + module)
    need(outputs.get("o") == [paths[1].read_text().strip() + ".olean"]
         and outputs.get("i") == paths[3].read_text().strip() + ".ilean"
         and outputs.get("c") == paths[6].read_text().strip() + ".c",
         "Lake trace/hash sidecars disagree: " + module)
    for extension in (".olean.server", ".olean.private", ".ir", ".ir.sig"):
        need(not suffix(stem(root / ".lake/build/lib/lean", module), extension).exists(),
             "Unexpected extra import facet: " + module + extension)
    return paths


def file_hashes(paths):
    return {str(path): sha(path) for path in paths}


def object_stamps(paths):
    # Lake may normalize mtimes on the first no-build call. Freeze afterwards.
    return {str(path): (path.stat().st_ino, path.stat().st_size, path.stat().st_mtime_ns)
            for path in paths if path.suffix in (".olean", ".trace")}


def unchanged_sources(root, nodes, reference):
    for module, node in nodes.items():
        need(sha(node["source"]) == reference[module]["source_sha256"],
             "Source changed: " + module)
    for name, expected in CONFIG.items():
        need(sha(root / name) == expected, "Build configuration changed: " + name)


def project_outputs(root):
    lib = root / ".lake/build/lib/lean"
    paths = list((lib / "ImbalancedChen").rglob("*.olean"))
    if (lib / "ImbalancedChen.olean").exists():
        paths.append(lib / "ImbalancedChen.olean")
    return {p.relative_to(lib).with_suffix("").as_posix().replace("/", "."): sha(p) for p in paths}


def copy_exact(source, target, expected):
    regular(source)
    need(sha(source) == expected, "Copy source changed: " + str(source))
    if target.exists() or target.is_symlink():
        regular(target)
        need(sha(target) == expected, "Refusing to overwrite an existing object: " + str(target))
        return
    target.parent.mkdir(parents=True, exist_ok=True)
    with source.open("rb") as incoming, target.open("xb") as outgoing:
        shutil.copyfileobj(incoming, outgoing)
    need(sha(target) == expected, "Object changed during copy: " + str(target))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--public-objects", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path.cwd().resolve()
    args.reference = args.reference.resolve()
    args.public_objects = args.public_objects.resolve()
    args.output = args.output.resolve()
    need(args.output.is_relative_to(root), "Recovery receipt must be inside this CI worktree")
    need(not args.output.exists(), "Use a new recovery receipt path; never overwrite a prior receipt")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    lock = (root / ".lake/p210-lake-recovery.lock").open("a")
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    raw_reference = args.reference.read_bytes()
    need(hashlib.sha256(raw_reference).hexdigest() == REFERENCE_SHA, "Unexpected public reference bytes")
    reference = json.loads(raw_reference)
    need(len(reference) == 93 and HELPERS <= reference.keys(), "Unexpected recovery scope")
    legacy = set(reference) - HELPERS
    driver_dir = root / "verification/part2"
    for name, expected in DRIVERS.items():
        need(sha(driver_dir / name) == expected, "Original driver/template changed: " + name)
    sys.path.insert(0, str(driver_dir))
    C = importlib.import_module("run_winner9_private_checks")
    A = importlib.import_module("run_winner9_private_audit")
    nodes = {}
    for module in sorted(reference):
        nodes.update(A.project_nodes(root, module))
    need(set(nodes) == set(reference), "Project closure escapes the exact 93 public modules")
    need(not any("NumericalPage" in m or "NumericalCheck" in m for m in nodes), "Numerical work is forbidden")
    toolchain = reference[next(iter(reference))]["toolchain"]
    for module, node in nodes.items():
        record = reference[module]
        need(record["module"] == module and record["cache_schema"] == 2 and record["exit_code"] == 0
             and record["toolchain"] == toolchain and record["closure_signature"] == C.closure_signature(record),
             "Invalid historical record: " + module)
        need(record["deps"] == {d: reference[d]["object_sha256"] for d in node["deps"]}
             and record["dependency_signatures"] == {d: reference[d]["closure_signature"] for d in node["deps"]},
             "Historical dependency graph mismatch: " + module)
        need(node["source"].resolve().is_relative_to(root), "Project source escapes this worktree")
        if module in legacy:
            need(record.get("baseline_commit") == C.BASELINE, "Not an original baseline record: " + module)
            need(not HELPERS.intersection(node["deps"]), "Lake recovery would require a helper build")
        else:
            regular(node["source"])
            regular(suffix(stem(args.public_objects, module), ".olean"))
            need(sha(suffix(stem(args.public_objects, module), ".olean")) == record["object_sha256"],
                 "Public helper object differs: " + module)
    unchanged_sources(root, nodes, reference)
    need(sha(LEAN) == LEAN_SHA and sha(LEAN.with_name("leanchecker")) == CHECKER_SHA,
         "Pinned Lean/checker binary mismatch")
    need(subprocess.check_output([str(LEAN), "--version"], text=True).strip() == toolchain["lean_version"],
         "Lean version differs from historical records")
    need(toolchain["lean_binary_sha256"] == LEAN_SHA and toolchain["mathlib_commit"] == PIN,
         "Historical toolchain mismatch")
    need(subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip() == PIN
         and (root / ".lake/packages/mathlib").resolve() == MATHLIB.resolve(), "Mathlib environment mismatch")
    lake_version = subprocess.check_output([str(LAKE), "--version"], text=True).strip()
    need("62eed1" in lake_version, "Lake is not from the fixed Lean installation")
    registry = root / ".lake/p2-private/records.json"
    need(not registry.exists() or registry.read_bytes() == raw_reference, "Existing registry is not the original public records")
    initial = project_outputs(root)
    need(set(initial) <= legacy, "Unexpected project object in Lake build directory")
    done = set()
    for module, digest in initial.items():
        need(digest == reference[module]["object_sha256"], "Existing nonexact Lake object: " + module)
        exact_lake_object(root, module, reference[module])
        done.add(module)
    need("ImbalancedChen.P2Winner9CompleteSeedTypes" in done, "Restore the exact successful SeedTypes probe first")
    order = []
    def visit(module):
        if module in order:
            return
        for dep in nodes[module]["deps"]:
            visit(dep)
        order.append(module)
    for module in sorted(legacy):
        visit(module)
    need(set(order) == legacy, "Unexpected Lake topological scope")
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        env.pop(key, None)
    logs = Path(tempfile.mkdtemp(prefix="lake-recovery-", dir=args.output.parent))
    receipt = {"schema": 1, "status": "running", "reference_sha256": REFERENCE_SHA,
               "lake_binary_sha256": sha(LAKE), "lake_version": lake_version,
               "toolchain": toolchain, "reused_helpers": sorted(HELPERS), "initial_exact_lake": sorted(done),
               "source_symlinks": sorted(m for m in legacy if nodes[m]["source"].is_symlink()),
               "recovered": [], "steps": [], "new_mathematical_credit": 0,
               "new_strict_compile_credit": 0, "new_replay_credit": 0}
    def save():
        temporary = args.output.with_suffix(args.output.suffix + ".tmp")
        temporary.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
        temporary.replace(args.output)
    def run(module, phase, no_build, facet):
        command = [str(LAKE), "--offline", "--no-cache", "--rehash", "--verbose"]
        if no_build:
            command.append("--no-build")
        command += ["build", "+" + module + ":" + facet]
        log = logs / f"{len(receipt['steps']):03}-{module.rsplit('.', 1)[-1]}-{phase}.log"
        started = time.monotonic()
        with log.open("x") as stream:
            code = subprocess.run(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT).returncode
        receipt["steps"].append({"module": module, "phase": phase, "command": command,
                                 "exit_code": code, "seconds": round(time.monotonic() - started, 3),
                                 "log": str(log.relative_to(root)), "log_sha256": sha(log)})
        save()
        need(code == 0, "Lake rejected " + phase + " for " + module + "; see " + str(log))
    try:
        save()
        initial_paths = [p for name in sorted(done) for p in exact_lake_object(root, name, reference[name])]
        initial_hashes = file_hashes(initial_paths)
        for module in sorted(done):
            run(module, "initial-reuse-check", True, "leanArts")
            need(file_hashes(initial_paths) == initial_hashes and project_outputs(root) == initial,
                 "Restored Lake files are not reusable without rebuilding")
        unchanged_sources(root, nodes, reference)
        for module in order:
            if module in done:
                print("REUSE_EXACT_LAKE", module, flush=True)
                continue
            protected = [p for name in sorted(done) for p in exact_lake_object(root, name, reference[name])]
            before = file_hashes(protected)
            outputs_before = project_outputs(root)
            unchanged_sources(root, nodes, reference)
            run(module, "dependencies-only", True, "deps")
            need(file_hashes(protected) == before and project_outputs(root) == outputs_before,
                 "A no-build check changed existing artifacts")
            unchanged_sources(root, nodes, reference)
            stamps = object_stamps(protected)
            need(all(dep in done for dep in nodes[module]["deps"]), "Dependency not restored before build")
            print("RESTORE_ENVIRONMENT_ONLY", module, flush=True)
            run(module, "ordinary-lake-recovery", False, "leanArts")
            need(file_hashes(protected) == before and object_stamps(protected) == stamps,
                 "Lake attempted to alter or rebuild an already exact module")
            need(project_outputs(root) == {**outputs_before, module: reference[module]["object_sha256"]},
                 "Lake produced an unexpected project module or a nonhistorical object")
            exact_lake_object(root, module, reference[module])
            unchanged_sources(root, nodes, reference)
            done.add(module)
            receipt["recovered"].append(module)
            save()
        need(done == legacy, "Incomplete historical Lake recovery")
        private_lib = root / ".lake/p2-private/lib"
        for module in sorted(reference):
            source = suffix(stem(args.public_objects if module in HELPERS else root / ".lake/build/lib/lean", module), ".olean")
            for extension in (".olean.server", ".olean.private", ".ir", ".ir.sig"):
                need(not suffix(stem(private_lib, module), extension).exists(), "Unexpected private import facet")
            copy_exact(source, suffix(stem(private_lib, module), ".olean"), reference[module]["object_sha256"])
        frozen = A.snapshot(root, private_lib, nodes, toolchain)
        A.verify_compilation(reference, nodes, frozen)
        need(frozen["leanchecker_sha256"] == CHECKER_SHA, "Checker changed during recovery")
        for name, expected in DRIVERS.items():
            need(sha(driver_dir / name) == expected, "Original driver/template changed during recovery")
        need(args.reference.read_bytes() == raw_reference, "Public reference changed during recovery")
        if not registry.exists():
            fd, temporary_name = tempfile.mkstemp(prefix="records-recovery-", suffix=".tmp", dir=registry.parent)
            temporary_registry = Path(temporary_name)
            try:
                with os.fdopen(fd, "wb") as stream:
                    stream.write(raw_reference)
                    stream.flush()
                    os.fsync(stream.fileno())
                os.link(temporary_registry, registry)  # Atomic publication; never replaces an existing file.
            finally:
                temporary_registry.unlink(missing_ok=True)
        need(registry.read_bytes() == raw_reference, "Historical record bytes changed")
        need(A.snapshot(root, private_lib, nodes, toolchain) == frozen, "Final environment changed")
        receipt.update(status="complete", modules=sorted(reference), records_sha256=sha(registry),
                       historical_records_preserved_verbatim=True, original_a_verify_compilation="passed")
        save()
    except BaseException as error:
        receipt.update(status="failed", error=f"{type(error).__name__}: {error}")
        save()
        raise


if __name__ == "__main__":
    main()
