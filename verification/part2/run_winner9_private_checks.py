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

PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
BASELINE = "8657cfffef159185f73c6a04ae4d31c846c0d0a9"
LEAN = "/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def imports(path: Path) -> list[str]:
    return [name for line in path.read_text().splitlines()
            if line.startswith("import ") for name in line[7:].split()
            if name.startswith("ImbalancedChen.")]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--baseline-root", type=Path, default=Path("/workspace/goldbach-p2"))
    parser.add_argument("--workers", type=int, default=1)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--memory-mb", type=int, default=6144)
    parser.add_argument("--install-candidates", action="store_true")
    args = parser.parse_args()
    root = Path.cwd()
    baseline = args.baseline_root
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
    records_path = out / "records.json"
    records = json.loads(records_path.read_text()) if records_path.exists() else {}
    env = dict(os.environ)
    env["LEAN_PATH"] = f"{lib}:{baseline_lib}:" + env.get("LEAN_PATH", "")
    flags = ["-t0", f"-j{args.threads}", f"-M{args.memory_mb}", "-DwarningAsError=true",
             "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"]
    # These are recorded historical style exceptions, never proof-warning exceptions.
    baseline_style: dict[str, list[str]] = {}
    reusable_baseline: set[str] = set()
    for name in order:
        path = nodes[name]["source"]
        original = baseline / path.relative_to(root)
        obj = lib / (name.replace(".", "/") + ".olean")
        old_obj = baseline_lib / (name.replace(".", "/") + ".olean")
        if (original.is_file() and obj.is_file() and old_obj.is_file()
                and digest(obj) == digest(old_obj) and digest(path) == digest(original)
                and all(dep in reusable_baseline for dep in nodes[name]["deps"])):
            reusable_baseline.add(name)
            if name not in records:
                records[name] = {
                    "module": name, "source": str(path.relative_to(root)),
                    "source_sha256": digest(path), "object": str(obj),
                    "object_sha256": digest(obj), "exit_code": 0,
                    "deps": {dep: records[dep]["object_sha256"] for dep in nodes[name]["deps"]},
                    "provenance": "existing accepted baseline cache",
                    "baseline_commit": BASELINE, "new_strict_compile": False,
                }

    def save() -> None:
        temporary = records_path.with_suffix(".tmp")
        temporary.write_text(json.dumps(records, indent=2, sort_keys=True) + "\n")
        temporary.replace(records_path)

    def dependencies(name: str) -> dict[str, str]:
        return {dep: records[dep]["object_sha256"] for dep in nodes[name]["deps"]}

    def valid(name: str) -> bool:
        old = records.get(name, {})
        if old.get("exit_code") != 0 or old.get("source_sha256") != digest(nodes[name]["source"]):
            return False
        if old.get("deps") != dependencies(name):
            return False
        obj = Path(old["object"])
        return obj.is_file() and digest(obj) == old["object_sha256"]

    # Reuse the already completed, explicitly logged initial private benchmark.
    # This is the same isolated worktree and the same immutable baseline objects.
    probe_path = out / "probe-records.json"
    probes = json.loads(probe_path.read_text()) if probe_path.exists() else {}
    for name in order:
        source = nodes[name]["source"]
        obj = lib / (name.replace(".", "/") + ".olean")
        for previous in probes.values():
            if (previous.get("source") == str(source.relative_to(root))
                    and previous.get("exit_code") == 0
                    and previous.get("source_sha256") == digest(source)
                    and obj.is_file() and previous.get("object_sha256") == digest(obj)
                    and all(dep in records for dep in nodes[name]["deps"])):
                record = dict(previous)
                record.update({"module": name, "object": str(obj), "deps": dependencies(name),
                               "provenance": "initial private strict-compile benchmark",
                               "new_strict_compile": True, "mathlib_commit": PIN,
                               "lean": "4.33.0-rc1"})
                records[name] = record

    def compile_one(name: str) -> dict:
        source = nodes[name]["source"]
        obj = lib / (name.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        attempt = len(records.get(name, {}).get("attempts", [])) + 1
        log = logs / f"{name}.attempt{attempt}.log"
        command = [LEAN, *flags, *baseline_style.get(name, []), "-o", str(obj),
                   str(source.relative_to(root))]
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
        record = {
            "module": name, "source": str(source.relative_to(root)),
            "source_sha256": digest(source), "deps": dependencies(name),
            "command": command, "exit_code": result.returncode,
            "seconds": round(time.monotonic() - start, 3), "log": str(log.relative_to(root)),
            "attempts": attempts, "mathlib_commit": PIN, "lean": "4.33.0-rc1",
            "new_strict_compile": result.returncode == 0, "object": str(obj),
        }
        if result.returncode == 0:
            record["object_sha256"] = digest(obj)
        return record

    done: set[str] = set()
    failed: set[str] = set()
    pending = set(nodes)
    running = {}
    reused = 0
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
                pending.remove(name)
                if valid(name):
                    done.add(name)
                    reused += 1
                else:
                    running[pool.submit(compile_one, name)] = name
            if not running:
                if pending:
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
    save()
    print(json.dumps({"roots": args.modules, "successful_closure": len(done),
                      "reused": reused, "failed_or_blocked": sorted(failed),
                      "total": len(nodes)}), flush=True)
    return int(bool(failed))


if __name__ == "__main__":
    raise SystemExit(main())
