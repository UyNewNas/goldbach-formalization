"""Build and freshly replay the five Part 4 modules at the frozen dependency pins.

Run with the pinned Lean/Lake on PATH:
    python3 verification/verify_part4_upper.py

The standalone CI workflow calls this runner without importing a project root.
Each run gets its own logs and inventories. The top-level report is reset
before any gate. Success verifies the displayed declarations and hypotheses;
it does not discharge the missing analytic inputs to K or hUpper.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

# Reusing the frozen source lexer must not create untracked files in verification/.
sys.dont_write_bytecode = True
from verify_variable_envelope_boxes import lean_code

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "ImbalancedChen.ActualUpperPolicyDensity",
    "ImbalancedChen.UpperCoefficientPerturbation",
    "ImbalancedChen.ActualUpperDensityAssembly",
    "ImbalancedChen.RealPhysicalUpperWeightBridge",
    "ImbalancedChen.RealUpperCountingAssembly",
)
AUDIT = "verification/Part4UpperAudit.lean"
BASE_COMMIT = "1a80c1bcce67886f699d097fc37fd245cd3620bf"
TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
LOCK_SHA256 = {
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_SOURCE = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b")
IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def check_lockfiles() -> dict:
    for relative, expected in LOCK_SHA256.items():
        if digest(ROOT / relative) != expected:
            raise RuntimeError(f"Frozen dependency/toolchain file changed: {relative}")
    if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
        raise RuntimeError("Unexpected Lean toolchain pin")
    return json.loads((ROOT / "lake-manifest.json").read_text())


def dependency_roots(manifest: dict) -> list[Path]:
    return [
        ROOT / manifest["packagesDir"] / package["name"]
        for package in manifest["packages"]
    ]


def check_dependency_heads(manifest: dict) -> dict[str, str]:
    revisions = {}
    for package, directory in zip(manifest["packages"], dependency_roots(manifest)):
        actual = subprocess.check_output(
            ["git", "-C", str(directory), "rev-parse", "--verify", "HEAD"],
            text=True, stderr=subprocess.STDOUT,
        ).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"Wrong pinned dependency HEAD for {package['name']}: {actual}")
        changed = subprocess.check_output(
            ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=normal"],
            text=True, stderr=subprocess.STDOUT,
        ).strip()
        if changed:
            raise RuntimeError(f"Dependency source is not clean: {package['name']}\n{changed}")
        revisions[package["name"]] = actual
    return revisions


def import_closure(manifest: dict) -> tuple[list[str], set[Path]]:
    """Follow project and supplier imports; Mathlib cache follows its own graph."""
    roots = [ROOT, *dependency_roots(manifest)]
    pending = list(MODULES)
    seen: set[str] = set()
    mathlib: set[str] = set()
    sources: set[Path] = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        if module == "Mathlib" or module.startswith("Mathlib."):
            mathlib.add(module)
            continue
        if module.split(".", 1)[0] in {"Lean", "Lake", "Std", "Init"}:
            continue
        relative = Path(module.replace(".", "/") + ".lean")
        path = next((directory / relative for directory in roots
                     if (directory / relative).is_file()), None)
        if path is None:
            raise RuntimeError(f"Cannot resolve an imported source at the frozen pins: {module}")
        sources.add(path)
        for line in lean_code(path.read_text(encoding="utf-8")).splitlines():
            match = IMPORT.match(line)
            if match:
                names = match.group(1).split()
                if names and names[0] == "all":
                    names = names[1:]
                if not names or any(not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9'.]*", name)
                                    for name in names):
                    raise RuntimeError(f"Unsupported import syntax in {path}: {line}")
                pending.extend(names)
    if not mathlib:
        raise RuntimeError("No explicit Mathlib imports found for the audited modules")
    # Some frozen upstream suppliers import Mathlib itself. That is a necessary
    # cache dependency, not a reason to alter or reject the pinned supplier.
    return (["Mathlib"] if "Mathlib" in mathlib else sorted(mathlib)), sources


def parse_inventory(log: str) -> tuple[list[dict], list[dict]]:
    records = [json.loads(line.removeprefix("PART4_UPPER_AUDIT_DECL "))
               for line in log.splitlines() if line.startswith("PART4_UPPER_AUDIT_DECL ")]
    counts = [json.loads(line.removeprefix("PART4_UPPER_AUDIT_MODULE "))
              for line in log.splitlines() if line.startswith("PART4_UPPER_AUDIT_MODULE ")]
    totals = [int(line.removeprefix("PART4_UPPER_AUDIT_COUNT "))
              for line in log.splitlines() if line.startswith("PART4_UPPER_AUDIT_COUNT ")]
    if totals != [len(records)] or not records:
        raise RuntimeError("Missing or inconsistent Lean declaration inventory")
    names = [record["name"] for record in records]
    if len(names) != len(set(names)):
        raise RuntimeError("Duplicate names in Lean declaration inventory")
    if len(counts) != len(MODULES) or {item["module"] for item in counts} != set(MODULES):
        raise RuntimeError("Audit does not cover each required Part 4 module")
    actual_counts = Counter(record["module"] for record in records)
    for item in counts:
        if type(item["count"]) is not int or item["count"] <= 0:
            raise RuntimeError(f"Empty or invalid audit for {item['module']}")
        if actual_counts[item["module"]] != item["count"]:
            raise RuntimeError(f"Inconsistent inventory count for {item['module']}")
    for record in records:
        if record["module"] not in MODULES or record["kind"] == "axiom":
            raise RuntimeError(f"Unexpected declaration in audit: {record['name']}")
        if not isinstance(record["axioms"], list) or set(record["axioms"]) - ALLOWED:
            raise RuntimeError(f"Forbidden transitive axioms for {record['name']}")
        if not isinstance(record.get("universe_parameters"), list):
            raise RuntimeError(f"Missing universe parameters for {record['name']}")
        printed = record.get("type")
        if not isinstance(printed, str) or not printed.strip() or "⋯" in printed:
            raise RuntimeError(f"Missing or abbreviated type for {record['name']}")
    return records, counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    options = parser.add_mutually_exclusive_group()
    options.add_argument("--check-lockfiles", action="store_true",
                         help="Check frozen configuration bytes only; does not verify proofs")
    options.add_argument("--cache-imports", action="store_true",
                         help="Print targeted Mathlib imports after dependencies have been resolved")
    args = parser.parse_args()
    if args.check_lockfiles:
        check_lockfiles()
        print("Frozen configuration hashes match; proof verification has not run.")
        return
    if args.cache_imports:
        manifest = check_lockfiles()
        check_dependency_heads(manifest)
        print("\n".join(import_closure(manifest)[0]))
        return

    output = ROOT / ".lake" / "part4-upper-verification"
    output.mkdir(parents=True, exist_ok=True)
    run_output = output / f"run-{time.time_ns()}"
    run_output.mkdir()
    report_path = output / "report.json"
    report: dict = {
        "status": "RUNNING",
        "scope": "Five Part 4 modules only. Verified conditional interfaces keep all hypotheses; "
                 "a successful run is not a proof of the missing sharp K certificate or hUpper.",
        "base_commit": BASE_COMMIT,
        "modules": list(MODULES),
        "run_directory": run_output.relative_to(ROOT).as_posix(),
        "allowed_transitive_axioms": sorted(ALLOWED),
        "kernel_replay": "Bundled leanchecker --fresh, one explicitly named module per invocation",
        "stages": [],
    }

    def save_report() -> None:
        data = json.dumps(report, indent=2) + "\n"
        (run_output / "report.json").write_text(data, encoding="utf-8")
        temporary = report_path.with_suffix(".json.tmp")
        temporary.write_text(data, encoding="utf-8")
        temporary.replace(report_path)

    def run(arguments: list[str], log_name: str) -> str:
        stage = {
            "command": arguments,
            "log": (run_output / log_name).relative_to(ROOT).as_posix(),
            "started_utc": datetime.now(timezone.utc).isoformat(),
            "status": "RUNNING",
        }
        report["stages"].append(stage)
        save_report()
        started = time.monotonic()
        log_path = run_output / log_name
        print(f"START {log_name}", flush=True)
        try:
            with log_path.open("w", encoding="utf-8") as handle:
                handle.write("command=" + json.dumps(arguments) + "\n")
                handle.flush()
                result = subprocess.run(
                    arguments, cwd=ROOT, stdout=handle, stderr=subprocess.STDOUT,
                    text=True, timeout=1800,
                )
            stage["exit_code"] = result.returncode
            stage["status"] = "PASSED" if result.returncode == 0 else "FAILED"
            if result.returncode:
                tail = log_path.read_text(encoding="utf-8", errors="replace").splitlines()[-60:]
                print("\n".join(tail), flush=True)
                raise RuntimeError(f"{log_name} failed with exit code {result.returncode}")
        except BaseException as error:
            stage.update(status="FAILED", error=str(error))
            raise
        finally:
            stage["elapsed_seconds"] = round(time.monotonic() - started, 3)
            save_report()
        print(f"PASS {log_name}", flush=True)
        return log_path.read_text(encoding="utf-8", errors="replace").split("\n", 1)[1]

    save_report()
    try:
        manifest = check_lockfiles()
        report["dependency_revisions"] = check_dependency_heads(manifest)
        report["head_commit"] = run(["git", "rev-parse", "HEAD"], "head-commit.log").strip()
        report["working_tree"] = run(
            ["git", "status", "--porcelain"], "working-tree.log"
        ).strip()
        # Equality itself proves the baseline relation in a verified snapshot.
        # Descendant commits require the full-history ancestry check used by CI.
        if report["head_commit"] == BASE_COMMIT:
            report["baseline_relation"] = "HEAD is the exact accepted baseline"
        else:
            run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"],
                "baseline-ancestor.log")
            report["baseline_relation"] = "The accepted baseline is an ancestor of HEAD"
        cache_imports, closure = import_closure(manifest)
        report["mathlib_cache_imports"] = cache_imports
        report["mathlib_cache_scope"] = (
            "Full Mathlib is required by the frozen supplier import closure"
            if cache_imports == ["Mathlib"] else "Explicit imported Mathlib modules and their closure"
        )
        files = closure | {
            ROOT / AUDIT, Path(__file__).resolve(),
            ROOT / "verification/verify_variable_envelope_boxes.py",
            ROOT / ".github/workflows/part4-upper.yml",
            *(ROOT / relative for relative in LOCK_SHA256),
        }
        hashes = {path.relative_to(ROOT).as_posix(): digest(path) for path in sorted(files)}
        report["source_sha256"] = hashes
        for path in [*(source_path(module) for module in MODULES), ROOT / AUDIT]:
            code = lean_code(path.read_text(encoding="utf-8"))
            if FORBIDDEN_SOURCE.search(code) or "debug.skipKernelTC" in code:
                raise RuntimeError(f"Forbidden proof escape in {path.relative_to(ROOT)}")
        save_report()
        version = run([args.lake, "env", "lean", "--version"], "lean-version.log").strip()
        if not re.search(r"\bversion 4\.33\.0-rc1(?:[, )]|$)", version):
            raise RuntimeError(f"Unexpected Lean executable version: {version}")
        report["lean_version"] = version
        sysroot = Path(run(
            [args.lake, "env", "lean", "--print-prefix"], "lean-prefix.log"
        ).strip()).resolve(strict=True)
        checker = sysroot / "bin" / "leanchecker"
        if not checker.is_file():
            raise RuntimeError(f"Missing bundled checker: {checker}")
        report["toolchain_binaries"] = {
            name: {"path": str(sysroot / "bin" / name),
                   "sha256": digest(sysroot / "bin" / name)}
            for name in ("lean", "lake", "leanchecker")
        }
        # Existing dependencies have baseline linter warnings. Build their
        # closure normally, then force a warning-as-error compilation of every
        # new target. No warning from a new source can pass this second gate.
        run([args.lake, "build", *MODULES], "dependencies-and-targets-build.log")
        for module in MODULES:
            relative = module.replace(".", "/")
            target = ROOT / ".lake/build/lib/lean" / (relative + ".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            run([args.lake, "env", "lean", "-DwarningAsError=true",
                 "-o", str(target), relative + ".lean"],
                module.rsplit(".", 1)[1] + "-strict-build.log")
        olean_hashes = {}
        for module in MODULES:
            path = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
            if not path.is_file() or path.stat().st_size == 0:
                raise RuntimeError(f"Missing compiled target module: {module}")
            for part in (path, path.with_suffix(".olean.server"), path.with_suffix(".olean.private")):
                if part.is_file():
                    olean_hashes[part.relative_to(ROOT).as_posix()] = digest(part)
            replay = run(
                [args.lake, "env", str(checker), "--fresh", "--verbose", module],
                module.rsplit(".", 1)[1] + "-fresh-replay.log",
            )
            expected = f"replaying {module} with --fresh"
            if replay.splitlines().count(expected) != 1:
                raise RuntimeError(f"Missing explicit fresh kernel replay evidence for {module}")
        report["compiled_module_sha256"] = olean_hashes
        audit_log = run(
            [args.lake, "env", "lean", "-DwarningAsError=true", AUDIT], "axioms-and-types.log"
        )
        records, counts = parse_inventory(audit_log)
        (run_output / "declarations.json").write_text(
            json.dumps(records, indent=2) + "\n", encoding="utf-8"
        )
        (run_output / "declarations.tsv").write_text(
            "module\tkind\tname\ttransitive_axioms\n" + "".join(
                f"{record['module']}\t{record['kind']}\t{record['name']}\t"
                f"{','.join(record['axioms'])}\n" for record in records
            ), encoding="utf-8",
        )
        header = (
            f"head_commit={report['head_commit']}\n"
            "Complete types printed by the pinned Lean elaborator with pp.all=true.\n"
            "Includes private and generated declarations. Hypotheses remain hypotheses.\n\n"
        )
        for filename, selected in (
            ("declaration-types.txt", records),
            ("theorem-types.txt", [record for record in records if record["kind"] == "theorem"]),
        ):
            (run_output / filename).write_text(
                header + "\n\n".join(
                    f"[{record['module']}]\n{record['name']}\n"
                    f"universe_parameters={','.join(record['universe_parameters'])}\n"
                    f"type:\n{record['type']}\n"
                    f"transitive_axioms={','.join(record['axioms'])}"
                    for record in selected
                ) + "\n", encoding="utf-8",
            )
        for relative, expected_hash in {**hashes, **olean_hashes}.items():
            if digest(ROOT / relative) != expected_hash:
                raise RuntimeError(f"Verification input changed during this run: {relative}")
        if check_dependency_heads(manifest) != report["dependency_revisions"]:
            raise RuntimeError("A fixed dependency changed during verification")
        final_head = run(["git", "rev-parse", "HEAD"], "final-head-commit.log").strip()
        if final_head != report["head_commit"]:
            raise RuntimeError("HEAD changed during verification")
        report.update(status="PASSED", declaration_count=len(records), module_counts=counts)
        save_report()
        print(f"PASS: {len(MODULES)} explicit builds and bundled fresh kernel replays; "
              f"{len(records)} declarations with complete types and only allowed axioms.", flush=True)
        print("This verifies the stated interfaces, not unprovided analytic hypotheses.", flush=True)
        print(f"Report: {report_path}", flush=True)
    except BaseException as error:
        report.update(status="FAILED", error=str(error))
        save_report()
        print(f"FAILED: {error}\nActual logs: {run_output}", flush=True)
        raise


if __name__ == "__main__":
    main()
