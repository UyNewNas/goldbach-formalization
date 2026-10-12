"""Verify the owned Part 3 modules without modifying the shared root.

Run with the original pinned Lean/Lake on PATH. Every module is built
explicitly, strictly compiled, replayed by the bundled kernel checker, and
included in the defining-module/transitive-axiom inventory. Failures retain
their actual commands, logs and exit codes. --source-only performs no proof
verification and is labelled accordingly.
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

# Importing the shared lexer must not dirty an otherwise clean checkout.
sys.dont_write_bytecode = True
from verify_variable_envelope_boxes import lean_code

ROOT = Path(__file__).resolve().parents[1]
BASELINE = "1a80c1bcce67886f699d097fc37fd245cd3620bf"
TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
PINS = {"mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
        "goldbach": "09b97db5764ade1246bfb77206baa1b124760958"}
# Exact bytes at BASELINE: this also fixes all inherited dependency revisions
# and the Lake package configuration, not just the two direct requirements.
CONFIG_SHA256 = {
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
}
MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3DistributionTargets", "Part3PrimeAPDistribution",
    "Part3CurrentLowerDistribution", "Part3LongSlotDistribution",
    "Part3LongSlotNormalization", "Part3RoughAuxiliarySW",
    "Part3RoughAuxiliarySWNormalization"))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDIT = "verification/Part3DistributionAudit.lean"
WORKFLOW = ".github/workflows/part3-distribution.yml"
LEXER = "verification/verify_variable_envelope_boxes.py"
FORBIDDEN = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|skipKernel(?:TC)?)\b")


def validate_inventory(log: str) -> tuple[list[dict], list[dict]]:
    """Reject incomplete or inconsistent output from the Lean audit command."""
    records = [json.loads(line.removeprefix("PART3_AUDIT_DECL "))
               for line in log.splitlines() if line.startswith("PART3_AUDIT_DECL ")]
    counts = [json.loads(line.removeprefix("PART3_AUDIT_MODULE "))
              for line in log.splitlines() if line.startswith("PART3_AUDIT_MODULE ")]
    totals = [int(line.removeprefix("PART3_AUDIT_COUNT "))
              for line in log.splitlines() if line.startswith("PART3_AUDIT_COUNT ")]
    if not records or totals != [len(records)]:
        raise RuntimeError("Missing or inconsistent declaration inventory")
    if len({r["name"] for r in records}) != len(records):
        raise RuntimeError("Duplicate declaration in inventory")
    by_module = Counter(r["module"] for r in records)
    if len(counts) != len(MODULES) or {c["module"] for c in counts} != set(MODULES):
        raise RuntimeError("Incomplete module coverage")
    for c in counts:
        if type(c["count"]) is not int or by_module[c["module"]] != c["count"] or c["count"] <= 0:
            raise RuntimeError("Empty or inconsistent module inventory")
    kinds = {"theorem", "definition", "opaque", "quotient", "inductive", "constructor", "recursor"}
    for r in records:
        if (r["module"] not in MODULES or set(r["axioms"]) - ALLOWED
                or r["kind"] not in kinds or not isinstance(r["name"], str) or not r["name"]
                or not isinstance(r["type"], str) or not r["type"]):
            raise RuntimeError("Invalid declaration audit record")
    return records, counts


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / ".lake/part3-distribution-verification")
    parser.add_argument("--expected-head", help="Require this exact checked-out commit")
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    # Old compiled inventories must not accompany a source-only or failed rerun.
    for name in ("declarations.json", "theorem-types.txt"):
        (out / name).unlink(missing_ok=True)
    report = {"status": "RUNNING", "baseline": BASELINE, "modules": list(MODULES),
              "scope": "Part 3 only; not the high-modulus medium obligation or main theorem",
              "started_utc": datetime.now(timezone.utc).isoformat(),
              "expected_head": args.expected_head,
              "allowed_transitive_axioms": sorted(ALLOWED), "stages": []}

    def save() -> None:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    save()

    def run(command: list[str], name: str) -> str:
        print("START " + name, flush=True)
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        path = out / (name + ".log")
        with path.open("w") as handle:
            handle.write("command=" + json.dumps(command) + "\n")
            handle.flush()
            try:
                result = subprocess.run(command, cwd=ROOT, text=True, stdout=handle,
                                        stderr=subprocess.STDOUT)
            except OSError as error:
                handle.write("Process could not start: " + str(error) + "\n")
                report["stages"].append({"name": name, "command": command,
                                         "started_utc": started, "exit_code": None,
                                         "error": str(error)})
                save()
                raise
        text = path.read_text(errors="replace").split("\n", 1)[1]
        report["stages"].append({"name": name, "command": command, "started_utc": started,
                                 "elapsed_seconds": round(time.monotonic() - tick, 3),
                                 "exit_code": result.returncode})
        save()
        if result.returncode:
            raise RuntimeError(f"{name}: exit {result.returncode}\n{text}")
        print("PASS " + name, flush=True)
        return text

    try:
        for relative, expected in CONFIG_SHA256.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                raise RuntimeError("Frozen baseline configuration changed: " + relative)
        if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise RuntimeError("Lean toolchain pin changed")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        actual = {p["name"]: p["rev"] for p in manifest["packages"]}
        if any(actual.get(name) != rev for name, rev in PINS.items()):
            raise RuntimeError("Dependency pin changed")
        files = [ROOT / (m.replace(".", "/") + ".lean") for m in MODULES]
        files += [ROOT / AUDIT, Path(__file__).resolve(), ROOT / LEXER, ROOT / WORKFLOW,
                  *(ROOT / relative for relative in CONFIG_SHA256)]
        hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in files}
        report["source_sha256"] = hashes
        for path in files:
            if path.suffix == ".lean":
                code = lean_code(path.read_text())
                if FORBIDDEN.search(code):
                    raise RuntimeError(f"Forbidden proof escape: {path.relative_to(ROOT)}")
        if args.source_only:
            report["status"] = "SOURCE_ONLY_NOT_COMPILED"
            save()
            print("Source/pin checks passed; no Lean compilation or kernel verification was run.")
            return
        report["head_commit"] = run(["git", "rev-parse", "HEAD"], "head").strip()
        if args.expected_head and report["head_commit"] != args.expected_head:
            raise RuntimeError("Checked-out commit differs from expected head")
        run(["git", "merge-base", "--is-ancestor", BASELINE, "HEAD"], "baseline-ancestor")
        report["working_tree"] = run(
            ["git", "status", "--porcelain", "--untracked-files=all"], "working-tree").strip()
        if report["working_tree"]:
            raise RuntimeError("Working tree is not clean; HEAD would not identify the checked source")
        version = run(["lake", "env", "lean", "--version"], "lean-version").strip()
        if not re.search(r"\bversion 4\.33\.0-rc1(?:,|\))", version):
            raise RuntimeError("Unexpected compiler version: " + version)
        report["lean_version"] = version
        paths = json.loads(run(["lake", "env", sys.executable, "-c",
            "import json,os,shutil; print(json.dumps({"
            "'sysroot':os.environ.get('LEAN_SYSROOT'),"
            "'lean':shutil.which('lean'),'leanchecker':shutil.which('leanchecker')}))"],
            "bundled-tools"))
        if not all(paths.get(name) for name in ("sysroot", "lean", "leanchecker")):
            raise RuntimeError("Could not identify the bundled Lean/checker installation")
        for name in ("lean", "leanchecker"):
            expected = (Path(paths["sysroot"]) / "bin" / name).resolve()
            if Path(paths[name]).resolve() != expected or not expected.is_file():
                raise RuntimeError("Tool is not from the detected Lean toolchain: " + name)
        report["tool_paths"] = paths
        for package in manifest["packages"]:
            revision = run(["git", "-C", str(ROOT / ".lake/packages" / package["name"]),
                            "rev-parse", "HEAD"], "pin-" + package["name"]).strip()
            if revision != package["rev"]:
                raise RuntimeError("Actual package checkout changed: " + package["name"])
            dirty = run(["git", "-C", str(ROOT / ".lake/packages" / package["name"]),
                         "status", "--porcelain", "--untracked-files=all"],
                        "clean-" + package["name"]).strip()
            if dirty:
                raise RuntimeError("Dependency checkout has uncommitted changes: " + package["name"])
        run(["lake", "build", *MODULES], "build")
        objects: dict[str, str] = {}
        for module in MODULES:
            relative = module.replace(".", "/")
            olean = ROOT / ".lake/build/lib/lean" / (relative + ".olean")
            # leanchecker reads the most-private available olean part. Never let
            # an obsolete private/server part from a restored cache be replayed.
            parts = [Path(str(olean) + suffix) for suffix in ("", ".server", ".private")]
            for part in parts:
                part.unlink(missing_ok=True)
            run(["lake", "env", "lean", "-DwarningAsError=true", "-o", str(olean),
                 relative + ".lean"], module.rsplit(".", 1)[1] + "-strict")
            if not olean.is_file():
                raise RuntimeError("Strict compilation produced no olean: " + module)
            objects.update({p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in parts if p.is_file()})
        report["olean_sha256"] = objects
        for module in MODULES:
            replay = run(["lake", "env", paths["leanchecker"], "--verbose", module],
                         module.rsplit(".", 1)[1] + "-replay")
            if f"replaying {module}" not in replay.splitlines():
                raise RuntimeError("Missing replay evidence: " + module)
        log = run(["lake", "env", "lean", "-DwarningAsError=true", AUDIT], "axioms")
        records, counts = validate_inventory(log)
        for relative, expected in {**hashes, **objects}.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                raise RuntimeError("Source or compiled object changed during verification: " + relative)
        if run(["git", "status", "--porcelain", "--untracked-files=all"], "final-working-tree").strip():
            raise RuntimeError("Working tree changed during verification")
        (out / "declarations.json").write_text(json.dumps(records, indent=2) + "\n")
        (out / "theorem-types.txt").write_text("head_commit=" + report["head_commit"] + "\n\n" +
            "\n\n".join(r["name"] + " :\n" + r["type"] + "\naxioms=" +
                       ",".join(r["axioms"]) for r in records if r["kind"] == "theorem") + "\n")
        report.update(status="PASSED", declaration_count=len(records), module_counts=counts)
        save()
        print(f"PASS: {len(records)} declarations, all five builds, strict compiles, kernel replays and full transitive audits.")
    except BaseException as error:
        report.update(status="FAILED", error=str(error))
        save()
        raise


if __name__ == "__main__":
    main()
