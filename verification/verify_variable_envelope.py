"""Build, replay and audit the isolated VE modules without changing the root import.

Run from any directory with the pinned Lean/Lake binaries on PATH:
    python3 verification/verify_variable_envelope.py
Results are written under the ignored .lake/variable-envelope-verification/.
Only the standard propext, Classical.choice and Quot.sound axioms are allowed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "ImbalancedChen.VariableEnvelope",
    "ImbalancedChen.VariableEnvelopeConsequences",
)
PREFIX = "ImbalancedChen.VariableEnvelope."
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED = {PREFIX + name for name in (
    "original", "six", "Ordered", "v_eq_min", "original_eq_six",
    "pair_gate_margin", "xz_gate_margin", "yz_gate_margin",
    "continuousOn_original", "original_margin", "original_margin_sharp",
    "threshold_597_le_original",
)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake")
    args = parser.parse_args()
    output = ROOT / ".lake" / "variable-envelope-verification"
    output.mkdir(parents=True, exist_ok=True)
    report_path = output / "report.json"
    # A failed rerun must not leave a stale successful result at the report path.
    report_path.write_text(json.dumps({"status": "RUNNING"}) + "\n", encoding="utf-8")

    def run(arguments: list[str], log_name: str) -> str:
        result = subprocess.run(arguments, cwd=ROOT, capture_output=True,
                                encoding="utf-8", errors="replace")
        log = result.stdout + result.stderr
        (output / log_name).write_text(log, encoding="utf-8")
        if result.returncode:
            report_path.write_text(json.dumps({"status": "FAILED", "stage": log_name,
                                               "exit_code": result.returncode}) + "\n",
                                   encoding="utf-8")
            raise RuntimeError(f"{log_name} failed:\n{log}")
        print(f"PASS {log_name}", flush=True)
        return log

    files = [ROOT / (module.replace(".", "/") + ".lean") for module in MODULES]
    files.append(ROOT / "verification" / "VariableEnvelopeBoundary.lean")
    hashes = {}
    declarations = []
    for path in files:
        source = path.read_text(encoding="utf-8")
        hashes[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
        code = re.sub(r"/\-.*?\-/", "", source, flags=re.S)
        code = re.sub(r"--[^\n]*", "", code)
        if re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b", code):
            raise RuntimeError(f"Unexpected proof escape in {path.name}")
        if path in files[:2]:
            declarations.extend(PREFIX + name for name in re.findall(
                r"^(?:def|theorem|lemma)\s+([A-Za-z_0-9]+)", code, re.M))
    if len(set(declarations)) != len(declarations):
        raise RuntimeError("Duplicate public declaration names")
    if not REQUIRED <= set(declarations):
        raise RuntimeError(f"Missing required declarations: {sorted(REQUIRED - set(declarations))}")

    version = run([args.lake, "env", "lean", "--version"], "lean-version.log").strip()
    run([args.lake, "build", *MODULES], "build.log")
    run([args.lake, "env", "lean", "-DwarningAsError=true",
         "verification/VariableEnvelopeBoundary.lean"], "boundaries.log")
    for module in MODULES:
        run([args.lake, "env", "leanchecker", "--verbose", module],
            module.rsplit(".", 1)[1] + "-replay.log")

    audit = output / "AxiomAudit.lean"
    audit.write_text("import ImbalancedChen.VariableEnvelopeConsequences\n\n" +
                     "\n".join("#print axioms " + name for name in declarations) + "\n",
                     encoding="utf-8")
    log = run([args.lake, "env", "lean", str(audit)], "axioms.log")
    matches = re.findall(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if len(matches) != len(declarations) or {name for name, _ in matches} != set(declarations):
        raise RuntimeError("Axiom output does not cover every public declaration exactly once")
    axioms = {}
    for name, raw in matches:
        actual = {entry.strip() for entry in raw.split(",") if entry.strip()}
        if not actual <= ALLOWED:
            raise RuntimeError(f"Unexpected transitive axioms for {name}: {actual - ALLOWED}")
        axioms[name] = sorted(actual)
    # Ensure that the hashes describe the same files that were just checked.
    for relative, expected in hashes.items():
        if hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() != expected:
            raise RuntimeError(f"Source changed during verification: {relative}")
    report = {
        "status": "PASSED",
        "scope": "Only the two new VE modules and exact boundary checks; not the full Chen theorem.",
        "lean_version": version,
        "modules": list(MODULES),
        "public_declaration_count": len(declarations),
        "source_sha256": hashes,
        "axioms": axioms,
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {len(declarations)} public VE declarations; build, kernel replay and axiom audit.")
    print(f"Report: {report_path}")


if __name__ == "__main__":
    main()
