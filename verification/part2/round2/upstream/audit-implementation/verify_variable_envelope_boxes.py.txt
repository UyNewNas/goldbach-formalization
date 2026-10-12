"""Build, replay and inventory all VE declarations with the pinned Lean toolchain.

Run with Lean/Lake on PATH: python3 verification/verify_variable_envelope_boxes.py
The separate VE workflow calls this same runner; no root import is needed.
Complete logs, declaration inventory, hashes and timings are retained under
.lake/variable-envelope-boxes-verification, including when a stage fails.
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

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "ImbalancedChen.VariableEnvelope",
    "ImbalancedChen.VariableEnvelopeConsequences",
    "ImbalancedChen.VariableEnvelopeRegularity",
    "ImbalancedChen.VariableEnvelopeScaled",
    "ImbalancedChen.VariableEnvelopeBoxes",
    "ImbalancedChen.VariableEnvelopeCertificates",
)
BOUNDARIES = (
    "verification.VariableEnvelopeBoundary",
    "verification.VariableEnvelopeBoxesBoundary",
)
AUDIT = "verification/VariableEnvelopeBoxesAudit.lean"
TOOLCHAIN = "leanprover/lean4:v4.33.0-rc1"
MATHLIB_REV = "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
BASE_COMMIT = "7ba701070c5481acf9de1adb4489fd8016e08089"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ALL_MODULES = MODULES + BOUNDARIES


def source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def lean_code(text: str) -> str:
    """Strip nested block comments, line comments and strings for escape checks.

    This is an additional source guard only. Coverage and transitive axiom
    enforcement use Lean's entire module inventory, never this lexer.
    """
    out: list[str] = []
    pos = depth = 0
    while pos < len(text):
        if text.startswith("/-", pos):
            depth += 1
            pos += 2
        elif depth and text.startswith("-/", pos):
            depth -= 1
            pos += 2
            out.append(" ")
        elif depth:
            out.append("\n" if text[pos] == "\n" else " ")
            pos += 1
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = len(text) if end == -1 else end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == "\\":
                    pos += 2
                elif text[pos] == '"':
                    pos += 1
                    break
                else:
                    pos += 1
            out.append(" ")
        else:
            out.append(text[pos])
            pos += 1
    if depth:
        raise RuntimeError("Unterminated Lean block comment")
    return "".join(out)


def mathlib_imports() -> list[str]:
    imports: set[str] = set()
    for module in ALL_MODULES:
        for line in lean_code(source_path(module).read_text(encoding="utf-8")).splitlines():
            match = re.match(r"\s*import\s+(.+?)\s*$", line)
            if match:
                imports.update(name for name in match.group(1).split() if name.startswith("Mathlib."))
                if "Mathlib" in match.group(1).split():
                    raise RuntimeError("Use explicit Mathlib imports rather than importing all Mathlib")
    if not imports:
        raise RuntimeError("No targeted Mathlib imports found")
    return sorted(imports)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--reference-source-dir", type=Path,
                        help="Optionally recheck complete original Python source files against their pinned hashes")
    parser.add_argument("--cache-imports", action="store_true",
                        help="Print the exact direct Mathlib imports to pass to cache get")
    args = parser.parse_args()
    if args.cache_imports:
        print("\n".join(mathlib_imports()))
        return
    output = ROOT / ".lake" / "variable-envelope-boxes-verification"
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "report.json"
    report: dict = {
        "status": "RUNNING",
        "scope": "Complete three-variable VE only on 0 <= z <= y <= x <= 25/128; "
                 "not the extended x >= mu expression or full numerical certificates.",
        "base_commit": BASE_COMMIT,
        "modules": list(MODULES),
        "boundary_modules": list(BOUNDARIES),
        "allowed_transitive_axioms": sorted(ALLOWED),
        "stages": [],
    }

    def save_report() -> None:
        report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")

    def run(arguments: list[str], log_name: str) -> str:
        started = datetime.now(timezone.utc).isoformat()
        start = time.monotonic()
        log_path = output / log_name
        print(f"START {log_name}", flush=True)
        # Stream to a file so killed or timed-out CI still retains partial logs.
        with log_path.open("w", encoding="utf-8") as handle:
            handle.write("command=" + json.dumps(arguments) + "\n")
            handle.flush()
            result = subprocess.run(arguments, cwd=ROOT, stdout=handle,
                                    stderr=subprocess.STDOUT, text=True)
        log = log_path.read_text(encoding="utf-8", errors="replace")
        report["stages"].append({"log": log_name, "started_utc": started,
                                 "elapsed_seconds": round(time.monotonic() - start, 3),
                                 "exit_code": result.returncode})
        save_report()
        if result.returncode:
            raise RuntimeError(f"{log_name} failed with exit code {result.returncode}:\n{log}")
        print(f"PASS {log_name}", flush=True)
        # The first line records command provenance, not tool output.
        return log.split("\n", 1)[1]

    save_report()
    try:
        if (ROOT / "lean-toolchain").read_text().strip() != TOOLCHAIN:
            raise RuntimeError("Unexpected Lean toolchain pin")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        mathlib = [p for p in manifest["packages"] if p["name"] == "mathlib"]
        if len(mathlib) != 1 or mathlib[0]["rev"] != MATHLIB_REV:
            raise RuntimeError("Unexpected Mathlib revision")
        report["head_commit"] = run(["git", "rev-parse", "HEAD"], "head-commit.log").strip()
        report["working_tree"] = run(["git", "status", "--porcelain"], "working-tree.log").strip()
        files = [source_path(module) for module in ALL_MODULES]
        files += [ROOT / AUDIT, Path(__file__).resolve(), ROOT / "lean-toolchain",
                  ROOT / "lake-manifest.json", ROOT / "lakefile.toml",
                  ROOT / ".github/workflows/variable-envelope.yml",
                  ROOT / "verification/check_variable_envelope_reference.py"]
        files += sorted(path for path in (ROOT / "verification/reference").iterdir()
                        if path.suffix in {".py", ".json"})
        hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in files}
        report["source_sha256"] = hashes
        for path in files:
            if path.suffix == ".lean":
                code = lean_code(path.read_text(encoding="utf-8"))
                if re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code):
                    raise RuntimeError(f"Forbidden proof escape in {path.relative_to(ROOT)}")
        report["mathlib_cache_imports"] = mathlib_imports()
        reference_command = [sys.executable, "verification/check_variable_envelope_reference.py"]
        if args.reference_source_dir is not None:
            reference_command += ["--source-dir", str(args.reference_source_dir.resolve())]
        run(reference_command, "python-reference.log")
        version = run([args.lake, "env", "lean", "--version"], "lean-version.log").strip()
        if "4.33.0-rc1" not in version:
            raise RuntimeError(f"Unexpected Lean executable version: {version}")
        report["lean_version"] = version
        # All six modules are named explicitly: success never depends on root imports.
        run([args.lake, "build", *MODULES], "build.log")
        for module in BOUNDARIES:
            relative = module.replace(".", "/")
            olean = ROOT / ".lake/build/lib/lean" / (relative + ".olean")
            olean.parent.mkdir(parents=True, exist_ok=True)
            run([args.lake, "env", "lean", "-DwarningAsError=true", "-o", str(olean),
                 relative + ".lean"], module.rsplit(".", 1)[1] + "-build.log")
        for module in ALL_MODULES:
            replay = run([args.lake, "env", "leanchecker", "--verbose", module],
                         module.rsplit(".", 1)[1] + "-replay.log")
            if f"replaying {module}" not in replay.splitlines():
                raise RuntimeError(f"Missing bundled kernel replay evidence for {module}")
        log = run([args.lake, "env", "lean", "-DwarningAsError=true", AUDIT], "axioms.log")
        records = [json.loads(line.removeprefix("VE_AUDIT_DECL "))
                   for line in log.splitlines() if line.startswith("VE_AUDIT_DECL ")]
        counts = [json.loads(line.removeprefix("VE_AUDIT_MODULE "))
                  for line in log.splitlines() if line.startswith("VE_AUDIT_MODULE ")]
        totals = [int(line.removeprefix("VE_AUDIT_COUNT "))
                  for line in log.splitlines() if line.startswith("VE_AUDIT_COUNT ")]
        if totals != [len(records)] or not records:
            raise RuntimeError("Missing or inconsistent Lean declaration inventory")
        names = [record["name"] for record in records]
        if len(names) != len(set(names)):
            raise RuntimeError("Duplicate names in Lean declaration inventory")
        if len(counts) != len(ALL_MODULES) or {c["module"] for c in counts} != set(ALL_MODULES):
            raise RuntimeError("Audit does not cover every required module")
        actual_counts = Counter(record["module"] for record in records)
        for item in counts:
            if actual_counts[item["module"]] != item["count"]:
                raise RuntimeError(f"Inconsistent count for {item['module']}")
            if item["count"] == 0 and item["module"] != BOUNDARIES[0]:
                raise RuntimeError(f"Empty audit for {item['module']}")
        for record in records:
            if record["module"] not in ALL_MODULES:
                raise RuntimeError(f"Unexpected module in audit: {record['module']}")
            unexpected = set(record["axioms"]) - ALLOWED
            if unexpected:
                raise RuntimeError(f"Forbidden axioms for {record['name']}: {unexpected}")
            if not isinstance(record.get("type"), str) or not record["type"]:
                raise RuntimeError(f"Missing Lean-printed type for {record['name']}")
        (output / "declarations.json").write_text(json.dumps(records, indent=2) + "\n",
                                                encoding="utf-8")
        (output / "declarations.tsv").write_text(
            "module\tkind\tname\ttransitive_axioms\n" + "".join(
                f"{r['module']}\t{r['kind']}\t{r['name']}\t{','.join(r['axioms'])}\n"
                for r in records), encoding="utf-8")
        (output / "theorem-types.txt").write_text(
            f"head_commit={report['head_commit']}\n"
            "Theorem types printed by the pinned Lean elaborator.\n"
            "Includes private and automatically generated theorems.\n\n" + "\n\n".join(
                f"[{r['module']}]\n{r['name']} :\n{r['type']}\n"
                f"transitive_axioms={','.join(r['axioms'])}"
                for r in records if r["kind"] == "theorem") + "\n", encoding="utf-8")
        for relative, expected in hashes.items():
            if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
                raise RuntimeError(f"Source changed during verification: {relative}")
        report.update(status="PASSED", declaration_count=len(records), module_counts=counts)
        save_report()
        print(f"PASS: {len(records)} declarations, all module builds, regression checks, "
              "bundled kernel replays and full transitive axiom audit.", flush=True)
        print(f"Report: {report_path}", flush=True)
    except BaseException as error:
        report.update(status="FAILED", error=str(error))
        save_report()
        raise


if __name__ == "__main__":
    main()
