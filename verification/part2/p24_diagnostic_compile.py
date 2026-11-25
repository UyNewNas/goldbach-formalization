#!/usr/bin/env python3
"""Run isolated direct-Lean diagnostics; never create proof-acceptance records.

Only the output directory is writable. Donor project objects are unqualified
diagnostic inputs, even when their source/import ancestry matches. Packages are
read directly; Lake is never invoked. Snapshots bind the current source-header
closure, resolved loadable facets, and compiler --deps output before/after use.
They do not reconstruct historical compilation inputs or qualify old objects.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from qualify_winner9_native_cache import core_header

FACETS = (".olean", ".olean.server", ".olean.private", ".ir", ".ir.sig")
PIN = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
STATUS = "DIAGNOSTIC_ONLY_NOT_PROOF_ACCEPTANCE"
DONOR_INCOMPLETE = "DIAGNOSTIC_DONOR_INCOMPLETE"
DONOR_RECEIPT = "DIAGNOSTIC_DONOR.json"
DONOR_EVIDENCE = ("RUNTIME.json", "EXTERNAL_INPUTS_BEFORE.json", "EXTERNAL_INPUTS_AFTER.json",
                  "RECORDS.json", "SUMMARY.json")


class Hashes:
    def __init__(self):
        self.cache = {}

    @staticmethod
    def stamp(path):
        s = path.stat()
        return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)

    def digest(self, path):
        before = self.stamp(path)
        previous = self.cache.get(str(path))
        if previous and previous[0] == before:
            return previous[1]
        with path.open("rb") as stream:
            value = hashlib.file_digest(stream, "sha256").hexdigest()
        if self.stamp(path) != before:
            raise RuntimeError("File changed while hashing: " + str(path))
        self.cache[str(path)] = (before, value)
        return value

    def files(self, paths):
        return {str(p): {"bytes": p.stat().st_size, "sha256": self.digest(p)}
                for p in sorted(set(paths))}


def write(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def signature(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def physical_match(path, expected, hashes):
    return (path.is_file() and path.stat().st_size == expected["bytes"]
            and hashes.digest(path) == expected["sha256"])


def external_libraries(donor, toolchain):
    packages = sorted(p for p in (donor / ".lake/packages").iterdir()
                      if p.is_dir() and (p / ".lake/build/lib/lean").is_dir())
    return packages, [p / ".lake/build/lib/lean" for p in packages] + [toolchain / "lib/lean"]


def resolve_external_object(name, libraries):
    relative = Path(name.replace(".", "/") + ".olean")
    for directory in libraries:
        candidate = directory / relative
        if candidate.is_file():
            return candidate
        if (directory / name.split(".")[0]).is_dir():
            raise RuntimeError("Earlier incomplete package root shadows " + name)
    raise FileNotFoundError("Missing external import object: " + name)


def previous_external_binding(donor, toolchain, previous, runtime, snapshot, hashes):
    """Require the same ordered physical libraries and original loadable inputs."""
    if runtime.get("status") != STATUS or snapshot.get("status") != STATUS:
        raise ValueError("Previous diagnostic runtime/external status differs")
    if toolchain.resolve() != Path(runtime["lean_sysroot"]).resolve():
        raise ValueError("Prepared diagnostic donor toolchain differs from previous runtime")
    lean = toolchain / "bin/lean"
    if (lean.resolve() != Path(runtime["lean"]).resolve()
            or hashes.digest(lean) != runtime["lean_sha256"]):
        raise ValueError("Prepared diagnostic donor compiler differs from previous runtime")
    original = [Path(p).resolve() for p in runtime["lean_path"].split(os.pathsep) if p]
    if not original or original[0] != (previous / "lib").resolve():
        raise ValueError("Previous runtime does not start with its diagnostic project library")
    _, libraries = external_libraries(donor, toolchain)
    resolved = [p.resolve() for p in libraries]
    if resolved != original[1:]:
        raise ValueError("Current ordered external library roots differ from previous runtime")
    files = snapshot["files"]
    if not files or not snapshot["modules"]:
        raise ValueError("Previous external snapshot is empty")
    if any(not physical_match(Path(p), row, hashes) for p, row in files.items()):
        raise ValueError("Previous diagnostic external input bytes changed")
    for name, row in snapshot["modules"].items():
        old_object = Path(row["object"])
        current = resolve_external_object(name, libraries)
        if current.resolve() != old_object.resolve() or str(old_object) not in files:
            raise ValueError("Current external object resolution differs: " + name)
        old_stem, new_stem = old_object.with_suffix(""), current.with_suffix("")
        old_facets = {s for s in FACETS if str(old_stem) + s in files}
        new_facets = {s for s in FACETS if Path(str(new_stem) + s).is_file()}
        if old_facets != new_facets:
            raise ValueError("Current external loadable facet set differs: " + name)
    return {"external_libraries": list(map(str, resolved)), "toolchain_root": str(toolchain.resolve()),
            "lean": str(lean.resolve()), "lean_sha256": runtime["lean_sha256"]}


def diagnostic_donor_files(donor, hashes):
    """Bind the final private project sources and every loadable donor facet."""
    paths = list((donor / "ImbalancedChen").rglob("*.lean"))
    lib = donor / ".lake/build/lib/lean"
    paths.extend(p for p in lib.rglob("*") if p.is_file() and p.name.endswith(FACETS))
    return hashes.files(paths)


def validate_prepared_donor(donor, toolchain, hashes):
    marker = donor / DONOR_INCOMPLETE
    if marker.exists() or marker.is_symlink():
        raise RuntimeError("Prepared diagnostic donor is incomplete: " + str(donor))
    receipt_path = donor / DONOR_RECEIPT
    if not receipt_path.exists():
        return  # Ordinary pre-existing donors retain their unqualified diagnostic role.
    receipt = json.loads(receipt_path.read_text())
    if (receipt.get("status") != STATUS
            or any(receipt.get(k) is not False for k in ("proof_acceptance", "compile_credit", "kernel_credit"))):
        raise ValueError("Prepared donor receipt does not retain diagnostic-only status")
    previous = Path(receipt["previous_output"]).resolve()
    evidence = receipt["previous_evidence"]
    expected_paths = {str(previous / name) for name in DONOR_EVIDENCE}
    if set(evidence) != expected_paths or any(not physical_match(Path(p), row, hashes)
                                             for p, row in evidence.items()):
        raise ValueError("Prepared donor original evidence changed")
    old = {name: json.loads((previous / name).read_text()) for name in DONOR_EVIDENCE}
    summary, before, after = old["SUMMARY.json"], old["EXTERNAL_INPUTS_BEFORE.json"], old["EXTERNAL_INPUTS_AFTER.json"]
    if (summary.get("status") != STATUS or summary.get("current_inputs_stable") is not True
            or after.get("equal_to_before") is not True or before["files"] != after["files"]):
        raise ValueError("Prepared donor previous diagnostic inputs were not stable")
    binding = previous_external_binding(donor, toolchain, previous, old["RUNTIME.json"], before, hashes)
    if binding != receipt["runtime_binding"]:
        raise ValueError("Prepared donor runtime binding differs")
    if diagnostic_donor_files(donor, hashes) != receipt["prepared_files"]:
        raise ValueError("Prepared donor project source/object bytes or facet set changed")
    if any(not physical_match(Path(p), row, hashes) for p, row in evidence.items()):
        raise ValueError("Prepared donor original evidence changed during validation")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--donor-root", type=Path, default=Path("/workspace/blue-member-build"))
    parser.add_argument("--toolchain-root", type=Path,
                        default=Path("/workspace/toolchains/lean-4.33.0-rc1-linux"))
    parser.add_argument("--out", type=Path)
    parser.add_argument("--threads", type=int, default=1)
    parser.add_argument("--memory-mb", type=int, default=6144)
    parser.add_argument("--time-budget-seconds", type=float, default=3200)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args()
    if args.threads < 1 or args.memory_mb < 1024 or not 0 < args.time_budget_seconds < float("inf"):
        parser.error("Positive threads, memory >= 1024 MiB, and finite positive time budget required")
    root, donor, toolchain = (p.resolve() for p in (args.project_root, args.donor_root, args.toolchain_root))
    hashes = Hashes()
    validate_prepared_donor(donor, toolchain, hashes)
    nodes, order, visiting = {}, [], set()

    def visit(name):
        if name in visiting:
            raise RuntimeError("Project import cycle: " + name)
        if name in nodes:
            return
        source = root / (name.replace(".", "/") + ".lean")
        im, _ = core_header(source.read_text())
        nodes[name] = {"source": source, "sha256": hashes.digest(source), "imports": im,
                       "deps": [d for d in im if d.startswith("ImbalancedChen.")]}
        visiting.add(name)
        for dep in nodes[name]["deps"]:
            visit(dep)
        visiting.remove(name)
        order.append(name)

    for name in args.modules:
        if not name.startswith("ImbalancedChen."):
            parser.error("Only ImbalancedChen diagnostic roots are supported")
        visit(name)
    donor_lib = donor / ".lake/build/lib/lean"
    candidates = set()
    for name in order:
        node = nodes[name]
        original = donor / node["source"].relative_to(root)
        obj = donor_lib / (name.replace(".", "/") + ".olean")
        if (original.is_file() and obj.is_file()
                and hashes.digest(original) == node["sha256"]
                and core_header(original.read_text())[0] == node["imports"]
                and all(d in candidates for d in node["deps"])):
            candidates.add(name)
    plan = {"status": STATUS, "roots": args.modules, "closure_modules": len(nodes),
            "source_import_ancestor_matched_diagnostic_candidates": sorted(candidates),
            "requires_diagnostic_compile": [n for n in order if n not in candidates],
            "compile_credit": False, "kernel_credit": False, "cache_qualified": False}
    if args.plan_only:
        print(json.dumps(plan, indent=2), flush=True)
        return 0

    out = (args.out or root / ".lake/p24-diagnostic" / time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())).resolve()
    if out.exists():
        raise RuntimeError("Use a fresh diagnostic output directory: " + str(out))
    if not out.is_relative_to(root) or out.is_relative_to(donor):
        raise RuntimeError("Diagnostic output must be private to the target project")
    lib, logs = out / "lib", out / "logs"
    lib.mkdir(parents=True)
    logs.mkdir()
    write(out / "PLAN.json", plan)
    lean = toolchain / "bin/lean"
    packages, external_libs = external_libraries(donor, toolchain)
    mathlib = donor / ".lake/packages/mathlib"
    revision = subprocess.check_output(["git", "-C", str(mathlib), "rev-parse", "HEAD"], text=True).strip()
    if revision != PIN:
        raise RuntimeError("P1 Mathlib revision differs from the fixed pin")
    source_roots = packages + [toolchain / "src/lean"]
    env = dict(os.environ)
    # Preserve any P0 guard/controller markers. The absolute direct Lean command
    # has no reason to alter those coordination flags.
    for key in ("LEAN_SRC_PATH", "LEAN", "LEAN_AR", "LEAN_CC", "LAKE", "LAKE_HOME",
                "LAKE_OVERRIDE_LEAN"):
        env.pop(key, None)
    env["LEAN_SYSROOT"] = str(toolchain)
    env["LEAN_PATH"] = os.pathsep.join(map(str, [lib, *external_libs]))
    runtime = {"lean": str(lean), "lean_sha256": hashes.digest(lean),
               "version": subprocess.check_output([str(lean), "--version"], text=True).strip(),
               "mathlib_commit": revision, "lean_path": env["LEAN_PATH"], "lean_sysroot": str(toolchain),
               "script_sha256": hashes.digest(Path(__file__).resolve()), "status": STATUS}
    write(out / "RUNTIME.json", runtime)

    def resolve_object(name):
        return resolve_external_object(name, external_libs)

    def facets(stem):
        return [Path(str(stem) + suffix) for suffix in FACETS if Path(str(stem) + suffix).is_file()]

    external, external_files = {}, {lean, toolchain / "lib/libLean.so"}
    external_files = {p for p in external_files if p.is_file()}

    def external_visit(name):
        if name in external or name.startswith("ImbalancedChen."):
            return
        obj = resolve_object(name)
        source = next((p / (name.replace(".", "/") + ".lean") for p in source_roots
                       if (p / (name.replace(".", "/") + ".lean")).is_file()), None)
        im, prelude = core_header(source.read_text()) if source else ([], True)
        external[name] = {"object": str(obj), "source": str(source) if source else None,
                          "imports_from_current_source": im, "historical_inputs_qualified": False}
        external_files.update(facets(obj.with_suffix("")))
        if source:
            external_files.add(source)
        for dep in im + ([] if prelude or name == "Init" else ["Init"]):
            external_visit(dep)

    for node in nodes.values():
        for dep in node["imports"]:
            if not dep.startswith("ImbalancedChen."):
                external_visit(dep)
    external_visit("Init")
    before_external = hashes.files(external_files)
    write(out / "EXTERNAL_INPUTS_BEFORE.json", {"status": STATUS, "modules": external,
          "files": before_external, "scope": "Current source-header import closure and resolved loadable facets; no historical qualification"})
    records, failed = {}, set()
    for name in order:
        if name not in candidates:
            continue
        copied = []
        for path in facets(donor_lib / name.replace(".", "/")):
            target = lib / path.relative_to(donor_lib)
            target.parent.mkdir(parents=True, exist_ok=True)
            original_sha = hashes.digest(path)
            shutil.copyfile(path, target)
            if hashes.digest(path) != original_sha or hashes.digest(target) != original_sha:
                raise RuntimeError("Donor facet changed during diagnostic copy")
            copied.append({"donor": str(path), "private_copy": str(target), "sha256": original_sha})
        records[name] = {"status": "UNQUALIFIED_DONOR_DIAGNOSTIC_INPUT", "source_sha256": nodes[name]["sha256"],
                         "facets": copied, "compile_credit": False, "kernel_credit": False}
    write(out / "RECORDS.json", records)
    started = time.monotonic()
    pending = []
    for name in order:
        if name in candidates:
            continue
        if any(dep in failed for dep in nodes[name]["deps"]):
            failed.add(name)
            records[name] = {"status": "BLOCKED_BY_DIAGNOSTIC_FAILURE", "compile_credit": False}
            continue
        if time.monotonic() - started >= args.time_budget_seconds:
            pending.append(name)
            continue
        if any(dep in pending for dep in nodes[name]["deps"]):
            pending.append(name)
            continue
        source = nodes[name]["source"]
        needed = set()
        def project_inputs(dep):
            if dep in needed:
                return
            needed.add(dep)
            for parent in nodes[dep]["deps"]:
                project_inputs(parent)
        for dep in nodes[name]["deps"]:
            project_inputs(dep)
        input_files = {source}
        for dep in needed:
            input_files.add(nodes[dep]["source"])
            input_files.update(facets(lib / dep.replace(".", "/")))
        deps_command = [str(lean), "--deps", str(source)]
        deps_result = subprocess.run(deps_command, cwd=root, env=env, text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        deps_log = logs / (name + ".deps.log")
        deps_log.write_text(deps_result.stdout)
        observed = []
        for line in deps_result.stdout.splitlines():
            candidate = Path(line.strip())
            if candidate.suffix == ".olean":
                candidate = candidate if candidate.is_absolute() else root / candidate
                if candidate.is_file():
                    observed.append(str(candidate))
                    input_files.update(facets(candidate.with_suffix("")))
        before = hashes.files(input_files)
        target = lib / (name.replace(".", "/") + ".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        command = [str(lean), "-t0", f"-j{args.threads}", f"-M{args.memory_mb}",
                   "-DwarningAsError=true", "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000",
                   "-o", str(target), str(source)]
        log = logs / (name + ".log")
        print("DIAGNOSTIC_START", name, flush=True)
        start = time.monotonic()
        with log.open("w") as stream:
            result = subprocess.run(command, cwd=root, env=env, stdout=stream, stderr=subprocess.STDOUT)
        after = hashes.files(input_files)
        unchanged = before == after and hashes.digest(source) == nodes[name]["sha256"]
        code = result.returncode if unchanged else 125
        records[name] = {"status": STATUS, "source_sha256": nodes[name]["sha256"],
                         "command": command, "cwd": str(root), "exit_code": code,
                         "compiler_exit_code": result.returncode, "seconds": round(time.monotonic()-start, 3),
                         "log": str(log), "deps_command": deps_command, "deps_exit_code": deps_result.returncode,
                         "deps_log": str(deps_log), "compiler_reported_dependency_paths": observed,
                         "project_dependency_modules": sorted(needed), "inputs_before": before, "inputs_after": after,
                         "inputs_unchanged": unchanged, "external_before_signature": signature(before_external),
                         "output_facets": hashes.files(facets(target.with_suffix(""))) if code == 0 else {},
                         "compile_credit": False, "kernel_credit": False, "historical_inputs_qualified": False}
        if code:
            failed.add(name)
            print("DIAGNOSTIC_FAIL", name, code, flush=True)
            print(log.read_text()[-16000:], flush=True)
        else:
            print("DIAGNOSTIC_PASS_NOT_ACCEPTANCE", name, flush=True)
        write(out / "RECORDS.json", records)
    after_external = hashes.files(external_files)
    write(out / "EXTERNAL_INPUTS_AFTER.json", {"status": STATUS, "files": after_external,
          "equal_to_before": after_external == before_external})
    sources_unchanged = all(hashes.digest(node["source"]) == node["sha256"] for node in nodes.values())
    stable = before_external == after_external and sources_unchanged and hashes.digest(lean) == runtime["lean_sha256"]
    summary = {"status": STATUS, "roots": args.modules, "closure_modules": len(nodes),
               "unqualified_diagnostic_cache_inputs": len(candidates), "failed_or_blocked": sorted(failed),
               "pending": pending, "current_inputs_stable": stable, "output": str(out),
               "proof_acceptance": False, "compile_credit": False, "kernel_credit": False,
               "exit_code": 125 if not stable else 1 if failed else 2 if pending else 0}
    write(out / "RECORDS.json", records)
    write(out / "SUMMARY.json", summary)
    print(json.dumps(summary), flush=True)
    return summary["exit_code"]


if __name__ == "__main__":
    raise SystemExit(main())
