#!/usr/bin/env python3
"""Compile P2 candidates with source/dependency-bound cache reuse.

Run in a verification worktree. The original accepted worktree is read-only.
Historical objects retain their historical provenance; reuse is not described
as a new strict compilation or an independent kernel replay.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

from inspect_winner9_owner_native import imports as parsed_source_imports

PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
BASELINE = "8657cfffef159185f73c6a04ae4d31c846c0d0a9"
LEAN = "/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean"
MATHLIB = "/workspace/compile-deps/mathlib"
CACHE_SCHEMA = 2
EXTERNAL_CACHE_SCHEMA = 3


def compilation_resources(workers: int, memory_mb: int, external_memory_mb: int,
                          needs_external: bool) -> tuple[int, int]:
    """Keep the qualified native environment within one worker's heap budget.

    Loading the native Rosser bridge exceeded a 5800 MiB Lean heap in the
    P2.5 preflight. Two such workers also compete for the private job's total
    memory. Zero explicitly disables this native-context resource profile.
    This changes resources only; all proof-checking flags remain unchanged.
    """
    if needs_external and external_memory_mb > 0:
        return 1, max(memory_mb, external_memory_mb)
    return workers, memory_mb


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_digest(payload: dict) -> str:
    return hashlib.sha256(json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def imports(path: Path) -> list[str]:
    return [name for name in parsed_source_imports(path.read_text()) if name.startswith("ImbalancedChen.")]


def closure_signature(record: dict) -> str:
    """Bind the source/object to the recursively frozen dependency environment.

    A parent's .olean bytes can remain identical when an imported definition
    changes. Object hashes alone therefore do not identify the proof context.
    This helper must only be called for actual compilation snapshots or an
    explicitly evidenced historical migration, never to backfill an old probe
    with whatever dependency objects happen to exist now.
    """
    payload = {key: record[key] for key in (
        "module", "source_sha256", "object_sha256", "toolchain", "dependency_signatures")}
    payload["cache_schema"] = record.get("cache_schema", CACHE_SCHEMA)
    if payload["cache_schema"] == EXTERNAL_CACHE_SCHEMA:
        payload["external_snapshot"] = record["external_snapshot"]
    return json_digest(payload)


def main() -> int:
    started = time.monotonic()
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--baseline-root", type=Path, default=Path("/workspace/goldbach-p2"))
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--memory-mb", type=int, default=6144)
    parser.add_argument("--external-memory-mb", type=int, default=11264,
                        help="Minimum Lean heap for native-context closures, compiled with one worker; "
                             "0 preserves the requested worker/heap settings")
    parser.add_argument("--install-candidates", action="store_true")
    parser.add_argument("--time-budget-seconds", type=float,
                        help="Stop starting uncached modules after this elapsed time; finish running tasks")
    parser.add_argument("--external-snapshot", type=Path,
                        help="Previously qualified native source/object/import/runtime environment")
    args = parser.parse_args()
    if args.external_memory_mb < 0:
        parser.error("--external-memory-mb must be nonnegative")
    if args.time_budget_seconds is not None and not 0 <= args.time_budget_seconds < float("inf"):
        parser.error("--time-budget-seconds must be a finite nonnegative number")
    deadline = None if args.time_budget_seconds is None else started + args.time_budget_seconds
    root = Path.cwd()
    baseline = args.baseline_root
    mathlib_commit = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=MATHLIB, text=True).strip()
    assert mathlib_commit == PIN, "Mathlib checkout does not match the pinned environment"
    toolchain = {
        "lean_version": subprocess.check_output([LEAN, "--version"], text=True).strip(),
        "lean_binary_sha256": digest(Path(LEAN)),
        "mathlib_commit": mathlib_commit,
    }
    out = root / ".lake/p2-private"
    lib, logs = out / "lib", out / "logs"
    for path in (lib, logs):
        path.mkdir(parents=True, exist_ok=True)
    if args.install_candidates:
        source = root / "docs/source-only/20261124-p2-winner9/ImbalancedChen"
        for path in source.glob("*.lean"):
            shutil.copy2(path, root / "ImbalancedChen" / path.name)
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=baseline,
                                   text=True).strip() == BASELINE
    assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"],
                                       cwd=baseline, text=True).strip()
    baseline_lib = baseline / ".lake/build/lib/lean"
    # Lean chooses a package root before looking up a module, so a second
    # LEAN_PATH entry is not a per-file fallback for the same package.
    # Copy rather than symlink: a new object must never overwrite the baseline.
    for path in baseline_lib.rglob("*"):
        if path.is_file():
            target = lib / path.relative_to(baseline_lib)
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                shutil.copy2(path, target)
    nodes: dict[str, dict] = {}
    order: list[str] = []

    def visit(name: str) -> None:
        if name in nodes:
            return
        path = root / (name.replace(".", "/") + ".lean")
        if not path.is_file():
            raise FileNotFoundError(f"Missing project source: {path}")
        nodes[name] = {"source": path, "deps": imports(path)}
        for dep in nodes[name]["deps"]:
            visit(dep)
        order.append(name)

    for name in args.modules:
        visit(name)
    for name in order:
        nodes[name]["dependency_closure"] = set(nodes[name]["deps"]).union(
            *(nodes[dep]["dependency_closure"] for dep in nodes[name]["deps"]))
    from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes
    external = (ExternalSnapshot(args.external_snapshot, lean=LEAN, mathlib_pin=PIN, project_lib=lib)
                if args.external_snapshot else None)
    mark_project_nodes(nodes, set(external.modules) if external else set())
    requested_resources = (args.workers, args.memory_mb)
    args.workers, args.memory_mb = compilation_resources(
        args.workers, args.memory_mb, args.external_memory_mb,
        any(node["requires_external"] for node in nodes.values()))
    if (args.workers, args.memory_mb) != requested_resources:
        print("NATIVE_CONTEXT_RESOURCE_PROFILE", json.dumps({
            "requested_workers": requested_resources[0],
            "requested_memory_mb": requested_resources[1],
            "workers": args.workers, "memory_mb": args.memory_mb,
        }), flush=True)
    external_before = external.binding() if external else None
    records_path = out / "records.json"
    records = json.loads(records_path.read_text()) if records_path.exists() else {}
    env = dict(os.environ)
    env["LEAN_PATH"] = f"{lib}:{baseline_lib}:" + env.get("LEAN_PATH", "")
    if external:
        env = external.environment(env)
    flags = ["-t0", f"-j{args.threads}", f"-M{args.memory_mb}", "-DwarningAsError=true",
             "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
    # These are recorded historical style exceptions, never proof-warning exceptions.
    baseline_style: dict[str, list[str]] = {}
    reusable_baseline: set[str] = set()
    baseline_records: dict[str, dict] = {}
    for name in order:
        path = nodes[name]["source"]
        original = baseline / path.relative_to(root)
        obj = lib / (name.replace(".", "/") + ".olean")
        old_obj = baseline_lib / (name.replace(".", "/") + ".olean")
        if (not nodes[name]["requires_external"]
                and original.is_file() and obj.is_file() and old_obj.is_file()
                and digest(obj) == digest(old_obj) and digest(path) == digest(original)
                and all(dep in reusable_baseline for dep in nodes[name]["deps"])):
            reusable_baseline.add(name)
            record = {
                "module": name, "source": str(path.relative_to(root)),
                "source_sha256": digest(path), "object": str(obj),
                "object_sha256": digest(obj), "exit_code": 0,
                "deps": {dep: baseline_records[dep]["object_sha256"] for dep in nodes[name]["deps"]},
                "dependency_signatures": {
                    dep: baseline_records[dep]["closure_signature"] for dep in nodes[name]["deps"]},
                "provenance": "existing accepted baseline cache",
                "baseline_commit": BASELINE, "new_strict_compile": False,
                "cache_schema": CACHE_SCHEMA, "toolchain": toolchain,
            }
            record["closure_signature"] = closure_signature(record)
            baseline_records[name] = record

    def save() -> None:
        temporary = records_path.with_suffix(".tmp")
        # A terminated batch cannot leave fresh native-context records with
        # successful credit before its final physical-file check completes.
        persisted = {
            name: (dict(record, exit_code=125, new_strict_compile=False)
                   if record.get("external_check", {}).get("status") == "PENDING_BATCH_POSTCHECK"
                   else record)
            for name, record in records.items()
        }
        temporary.write_text(json.dumps(persisted, indent=2, sort_keys=True) + "\n")
        temporary.replace(records_path)

    def dependencies(name: str) -> dict[str, str]:
        return {dep: records[dep]["object_sha256"] for dep in nodes[name]["deps"]}

    def dependency_signatures(name: str) -> dict[str, str]:
        return {dep: records[dep]["closure_signature"] for dep in nodes[name]["deps"]}

    def dependency_files(name: str) -> dict:
        snapshot = {}
        for dep in sorted(nodes[name]["dependency_closure"]):
            paths = {"source_sha256": nodes[dep]["source"],
                     "object_sha256": lib / (dep.replace(".", "/") + ".olean")}
            snapshot[dep] = {}
            for key, path in paths.items():
                try:
                    snapshot[dep][key] = digest(path)
                except OSError:
                    snapshot[dep][key] = None
        return snapshot

    def valid_record(name: str, old: dict) -> bool:
        needs_external = nodes[name]["requires_external"]
        schema = EXTERNAL_CACHE_SCHEMA if needs_external else CACHE_SCHEMA
        if needs_external and (old.get("external_snapshot") != external_before
                               or old.get("external_check", {}).get("status") != "PASSED_BATCH_PRE_POST"
                               or old["external_check"].get("before") != external_before
                               or old["external_check"].get("after") != external_before):
            return False
        if (old.get("cache_schema") != schema or old.get("module") != name
                or old.get("toolchain") != toolchain or old.get("exit_code") != 0
                or old.get("source_sha256") != digest(nodes[name]["source"])):
            return False
        if (old.get("deps") != dependencies(name)
                or old.get("dependency_signatures") != dependency_signatures(name)):
            return False
        # Check the object Lean will actually import, not an old absolute path
        # that might still exist in another worktree after records are copied.
        obj = lib / (name.replace(".", "/") + ".olean")
        return (obj.is_file() and digest(obj) == old.get("object_sha256")
                and old.get("closure_signature") == closure_signature(old))

    # Legacy probes without frozen dependency signatures remain historical
    # evidence, but cannot automatically certify the current proof environment.
    probe_path = out / "probe-records.json"
    probes = json.loads(probe_path.read_text()) if probe_path.exists() else {}

    def adopt_probe(name: str) -> bool:
        source = nodes[name]["source"]
        obj = lib / (name.replace(".", "/") + ".olean")
        for previous in probes.values():
            if (previous.get("source") == str(source.relative_to(root))
                    and previous.get("new_strict_compile") is True
                    and valid_record(name, previous)):
                record = dict(previous)
                record.update({"object": str(obj),
                               "provenance": "initial private strict-compile benchmark"})
                records[name] = record
                return True
        return False

    def compile_one(name: str) -> dict:
        source = nodes[name]["source"]
        obj = lib / (name.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        attempt = len(records.get(name, {}).get("attempts", [])) + 1
        log = logs / f"{name}.attempt{attempt}.log"
        command = [LEAN, *flags, *baseline_style.get(name, []), "-o", str(obj),
                   str(source.relative_to(root))]
        source_before = digest(source)
        deps_before = dependencies(name)
        signatures_before = dependency_signatures(name)
        expected_files = {dep: {key: records[dep][key] for key in ("source_sha256", "object_sha256")}
                          for dep in nodes[name]["dependency_closure"]}
        files_before = dependency_files(name)
        start = time.monotonic()
        print("START", name, flush=True)
        original = baseline / source.relative_to(root)
        unchanged_baseline = original.is_file() and digest(source) == digest(original)
        attempts = list(records.get(name, {}).get("attempts", []))
        while True:
            with log.open("w") as stream:
                result = subprocess.run(command, cwd=root, env=env, stdout=stream,
                                        stderr=subprocess.STDOUT)
            attempts.append({"command": command.copy(), "exit_code": result.returncode,
                             "log": str(log.relative_to(root))})
            if result.returncode == 0 or not unchanged_baseline:
                break
            options = sorted(set(re.findall(r"set_option (linter\.[\w.]+) false", log.read_text())))
            extra = [f"-D{option}=false" for option in options
                     if f"-D{option}=false" not in command]
            if not extra:
                break
            print("BASELINE_STYLE_OPTIONS", name, extra, flush=True)
            command = command[:-3] + extra + command[-3:]
            log = logs / f"{name}.attempt{len(attempts) + 1}.log"
        exit_code = result.returncode
        files_after = dependency_files(name)
        if exit_code == 0 and (digest(source) != source_before or dependencies(name) != deps_before
                               or dependency_signatures(name) != signatures_before
                               or files_before != expected_files or files_after != expected_files):
            exit_code = 125
            with log.open("a") as stream:
                stream.write("\nProof-cache source/dependency snapshot changed or disagreed with records; "
                             "result not accepted.\n")
        record = {
            "module": name, "source": str(source.relative_to(root)),
            "source_sha256": source_before, "deps": deps_before,
            "dependency_signatures": signatures_before,
            "dependency_file_check": {
                "modules": len(expected_files), "expected_sha256": json_digest(expected_files),
                "before_sha256": json_digest(files_before), "after_sha256": json_digest(files_after),
                "before_matches_records": files_before == expected_files,
                "after_matches_records": files_after == expected_files,
            },
            "cache_schema": CACHE_SCHEMA, "toolchain": toolchain,
            "command": command, "exit_code": exit_code,
            "seconds": round(time.monotonic() - start, 3), "log": str(log.relative_to(root)),
            "attempts": attempts, "mathlib_commit": PIN, "lean": "4.33.0-rc1",
            "new_strict_compile": exit_code == 0, "object": str(obj),
        }
        if nodes[name]["requires_external"]:
            record.update({"cache_schema": EXTERNAL_CACHE_SCHEMA, "external_snapshot": external_before,
                           "external_check": {"status": "PENDING_BATCH_POSTCHECK", "before": external_before}})
        if exit_code == 0:
            record["object_sha256"] = digest(obj)
            record["closure_signature"] = closure_signature(record)
        return record

    done: set[str] = set()
    failed: set[str] = set()
    pending = set(nodes)
    running = {}
    reused = 0
    budget_exhausted = False
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        while pending or running:
            for name in order:
                if name not in pending or len(running) >= args.workers:
                    continue
                deps = nodes[name]["deps"]
                if any(dep in failed for dep in deps):
                    pending.remove(name)
                    failed.add(name)
                    continue
                if not all(dep in done for dep in deps):
                    continue
                if not valid_record(name, records.get(name, {})):
                    if name in baseline_records and valid_record(name, baseline_records[name]):
                        records[name] = baseline_records[name]
                    else:
                        adopt_probe(name)
                if valid_record(name, records.get(name, {})):
                    pending.remove(name)
                    records[name]["object"] = str(lib / (name.replace(".", "/") + ".olean"))
                    done.add(name)
                    reused += 1
                else:
                    if deadline is not None and time.monotonic() >= deadline:
                        if not budget_exhausted:
                            print("TIME_BUDGET_REACHED", "finishing running tasks; retaining pending modules", flush=True)
                        budget_exhausted = True
                        continue
                    pending.remove(name)
                    running[pool.submit(compile_one, name)] = name
            if not running:
                if pending:
                    if not budget_exhausted:
                        raise RuntimeError(f"Unresolved import cycle: {sorted(pending)}")
                break
            finished, _ = concurrent.futures.wait(running, return_when=concurrent.futures.FIRST_COMPLETED)
            for future in finished:
                name = running.pop(future)
                record = future.result()
                records[name] = record
                if record["exit_code"] == 0:
                    done.add(name)
                    print("PASS", name, record["seconds"], flush=True)
                else:
                    failed.add(name)
                    print("FAIL", name, record["exit_code"], flush=True)
                    print((root / record["log"]).read_text()[-10000:], flush=True)
                save()
    if external:
        try:
            external_after = external.verify()
            if external_after != external_before:
                raise ValueError("External native environment binding changed during the batch")
            for name in done:
                record = records[name]
                if record.get("external_check", {}).get("status") == "PENDING_BATCH_POSTCHECK":
                    record["external_check"] = {"status": "PASSED_BATCH_PRE_POST", "before": external_before,
                                                "after": external_after}
        except (OSError, ValueError, subprocess.CalledProcessError) as error:
            print("FAIL_EXTERNAL_POSTCHECK", str(error), flush=True)
            affected = {name for name in done if nodes[name]["requires_external"]}
            for name in affected:
                records[name].update({"exit_code": 125, "new_strict_compile": False,
                                      "external_check": {"status": "FAILED_BATCH_POSTCHECK", "error": str(error),
                                                         "before": external_before}})
            done.difference_update(affected)
            failed.update(affected)
    save()
    exit_code = 1 if failed else 2 if pending else 0
    print(json.dumps({"roots": args.modules, "successful_closure": len(done),
                      "reused": reused, "failed_or_blocked": sorted(failed),
                      "pending": sorted(pending), "complete": not failed and not pending,
                      "status": "failed" if failed else "partial" if pending else "complete",
                      "budget_exhausted": budget_exhausted, "time_budget_seconds": args.time_budget_seconds,
                      "elapsed_seconds": round(time.monotonic() - started, 3),
                      "exit_code": exit_code, "total": len(nodes)}), flush=True)
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
