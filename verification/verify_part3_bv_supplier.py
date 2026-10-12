#!/usr/bin/env python3
"""Strictly compile, replay and fully audit the exact Part 3 BV supplier."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time


ROOT = Path(__file__).resolve().parents[1]
MODULE = "MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional"
GOLDBACH_PIN = "09b97db5764ade1246bfb77206baa1b124760958"
SOURCE_SHA256 = "26de321b7b9ad1f3259c61461cd7259486c72a3404a9e32edabffd0cb9fb2f10"
AUDIT_MODULE = "verification.parts.p3.Bombieri1965Richert418UnconditionalAudit"
AUDIT_SOURCE = ROOT / "verification/parts/p3/Bombieri1965Richert418UnconditionalAudit.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--output-dir", required=True, type=Path)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report: dict = {
        "status": "RUNNING",
        "module": MODULE,
        "expected_head": args.expected_head,
        "goldbach_pin": GOLDBACH_PIN,
        "source_sha256_expected": SOURCE_SHA256,
        "allowed_transitive_axioms": sorted(ALLOWED),
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "stages": [],
    }

    def save() -> None:
        (out / "bv-supplier-report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(command: list[str], name: str, cwd: Path = ROOT) -> str:
        print("START " + name, flush=True)
        started = datetime.now(timezone.utc).isoformat()
        tick = time.monotonic()
        log = out / (name + ".log")
        with log.open("w") as handle:
            handle.write("command=" + json.dumps(command) + "\n")
            handle.flush()
            result = subprocess.run(command, cwd=cwd, text=True, stdout=handle,
                                    stderr=subprocess.STDOUT)
        body = log.read_text(errors="replace").split("\n", 1)[1]
        report["stages"].append({
            "name": name, "command": command, "cwd": str(cwd),
            "started_utc": started,
            "elapsed_seconds": round(time.monotonic() - tick, 3),
            "exit_code": result.returncode,
        })
        save()
        if result.returncode:
            raise RuntimeError(f"{name}: exit {result.returncode}\n{body}")
        print("PASS " + name, flush=True)
        return body

    save()
    try:
        head = run(["git", "rev-parse", "HEAD"], "bv-head").strip()
        if head != args.expected_head:
            raise RuntimeError("Checked-out commit differs from expected head")
        if run(["git", "status", "--porcelain", "--untracked-files=all"],
               "bv-working-tree").strip():
            raise RuntimeError("Working tree is not clean")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        package = next(p for p in manifest["packages"] if p["name"] == "goldbach")
        if package["rev"] != GOLDBACH_PIN:
            raise RuntimeError("Frozen goldbach pin changed")
        goldbach = ROOT / ".lake/packages/goldbach"
        actual_pin = run(["git", "rev-parse", "HEAD"], "bv-goldbach-pin", goldbach).strip()
        if actual_pin != GOLDBACH_PIN:
            raise RuntimeError("Actual goldbach checkout changed")
        if run(["git", "status", "--porcelain", "--untracked-files=all"],
               "bv-goldbach-clean", goldbach).strip():
            raise RuntimeError("Goldbach dependency checkout is dirty")

        relative = Path(*MODULE.split("."))
        source = goldbach / relative.with_suffix(".lean")
        if digest(source) != SOURCE_SHA256:
            raise RuntimeError("Exact supplier source changed")
        audit_hash = digest(AUDIT_SOURCE)
        report["source"] = {"path": str(source.relative_to(ROOT)), "sha256": digest(source)}
        report["audit_source"] = {
            "path": str(AUDIT_SOURCE.relative_to(ROOT)), "sha256": audit_hash}

        run(["lake", "build", MODULE], "bv-build")
        object_path = goldbach / ".lake/build/lib/lean" / relative.with_suffix(".olean")
        setup = goldbach / ".lake/build/ir" / Path(str(relative) + ".setup.json")
        if not setup.is_file():
            raise RuntimeError("Lake did not retain the supplier setup file")
        for suffix in ("", ".server", ".private"):
            Path(str(object_path) + suffix).unlink(missing_ok=True)
        run(["lake", "env", "lean", "-DwarningAsError=true", "-t0",
             "-o", str(object_path), "--setup", str(setup), str(source)], "bv-strict")
        if not object_path.is_file():
            raise RuntimeError("Strict supplier compile produced no object")
        report["production_objects"] = {
            str(path.relative_to(ROOT)): digest(path)
            for path in [Path(str(object_path) + suffix)
                         for suffix in ("", ".server", ".private")]
            if path.is_file()
        }
        report["archived_production_objects"] = {}
        for suffix in ("", ".server", ".private"):
            path = Path(str(object_path) + suffix)
            if path.is_file():
                archived = out / ("bv-production.olean" + suffix)
                shutil.copy2(path, archived)
                report["archived_production_objects"][archived.name] = digest(archived)
        version = run(["lake", "env", "lean", "--version"], "bv-lean-version").strip()
        if not re.search(r"\bversion 4\.33\.0-rc1(?:,|\))", version):
            raise RuntimeError("Unexpected Lean version: " + version)
        lean = run(["lake", "env", "bash", "-c", "command -v lean"],
                   "bv-lean-path").strip()
        lake = run(["lake", "env", "bash", "-c", "command -v lake"],
                   "bv-lake-path").strip()
        checker = run(["lake", "env", "bash", "-c", "command -v leanchecker"],
                      "bv-checker-path").strip()
        replay = run(["lake", "env", checker, "--verbose", MODULE], "bv-production-replay")
        if f"replaying {MODULE}" not in replay.splitlines():
            raise RuntimeError("Missing supplier replay marker")

        audit_object = ROOT / ".lake/build/lib/lean" / Path(*AUDIT_MODULE.split(".")).with_suffix(".olean")
        audit_object.parent.mkdir(parents=True, exist_ok=True)
        for suffix in ("", ".server", ".private"):
            Path(str(audit_object) + suffix).unlink(missing_ok=True)
        audit_log = run(["lake", "env", "lean", "-DwarningAsError=true", "-t0",
                         "-o", str(audit_object), str(AUDIT_SOURCE)], "bv-audit-strict")
        audit_replay = run(["lake", "env", checker, "--verbose", AUDIT_MODULE],
                           "bv-audit-replay")
        if f"replaying {AUDIT_MODULE}" not in audit_replay.splitlines():
            raise RuntimeError("Missing audit replay marker")
        declarations = [json.loads(line.removeprefix("PART3_BV_SUPPLIER_DECL "))
                        for line in audit_log.splitlines()
                        if line.startswith("PART3_BV_SUPPLIER_DECL ")]
        summaries = [json.loads(line.removeprefix("PART3_BV_SUPPLIER_MODULE "))
                     for line in audit_log.splitlines()
                     if line.startswith("PART3_BV_SUPPLIER_MODULE ")]
        imports = [json.loads(line.removeprefix("PART3_BV_SUPPLIER_IMPORT "))
                   for line in audit_log.splitlines()
                   if line.startswith("PART3_BV_SUPPLIER_IMPORT ")]
        if summaries != [{"count": len(declarations), "module": MODULE}]:
            raise RuntimeError("Missing or inconsistent supplier declaration summary")
        if not declarations or len({row["name"] for row in declarations}) != len(declarations):
            raise RuntimeError("Empty or duplicate supplier declaration inventory")
        if {row["module"] for row in declarations} != {MODULE}:
            raise RuntimeError("Wrong defining module in supplier inventory")
        if any(set(row["axioms"]) - ALLOWED for row in declarations):
            raise RuntimeError("Forbidden transitive supplier axiom")
        if any(row["kind"] == "axiom" or "⋯" in row["type"] or
               "⋯" in row["readable_type"] for row in declarations):
            raise RuntimeError("Incomplete or unproved supplier declaration")
        if not imports or len({row["module"] for row in imports}) != len(imports):
            raise RuntimeError("Incomplete or duplicate actual import-object inventory")
        for row in imports:
            path = Path(row["olean"]).resolve()
            if not path.is_file():
                raise RuntimeError(f"Missing inventoried import object: {path}")
            row.update(olean=str(path), bytes=path.stat().st_size, sha256=digest(path))
        if len({row["olean"] for row in imports}) != len(imports):
            raise RuntimeError("Duplicate resolved object in actual import-object inventory")
        (out / "bv-supplier-declarations.json").write_text(
            json.dumps(declarations, indent=2) + "\n")
        (out / "bv-supplier-imports.json").write_text(json.dumps(imports, indent=2) + "\n")
        tools = {}
        for name, raw_path in (("lean", lean), ("lake", lake), ("leanchecker", checker)):
            path = Path(raw_path).resolve()
            if not path.is_file():
                raise RuntimeError(f"Missing resolved tool binary: {path}")
            tools[name] = {
                "reported_path": raw_path, "resolved_path": str(path),
                "bytes": path.stat().st_size, "sha256": digest(path)}
        report.update(
            status="PASSED", head_commit=head, lean_version=version,
            tools=tools, owned_declaration_count=len(declarations),
            actual_import_object_count=len(imports),
            audit_objects={
                str(path.relative_to(ROOT)): digest(path)
                for path in [Path(str(audit_object) + suffix)
                             for suffix in ("", ".server", ".private")]
                if path.is_file()
            },
            completed_utc=datetime.now(timezone.utc).isoformat(),
        )
        report["archived_audit_objects"] = {}
        for suffix in ("", ".server", ".private"):
            path = Path(str(audit_object) + suffix)
            if path.is_file():
                archived = out / ("bv-audit.olean" + suffix)
                shutil.copy2(path, archived)
                report["archived_audit_objects"][archived.name] = digest(archived)
        if digest(source) != SOURCE_SHA256 or digest(AUDIT_SOURCE) != audit_hash:
            raise RuntimeError("Source changed during verification")
        save()
        print(json.dumps({"status": "PASS", "module": MODULE,
                          "owned_declarations": len(declarations),
                          "actual_import_objects": len(imports)}, indent=2))
    except BaseException as error:
        report.update(status="FAILED", error=str(error),
                      completed_utc=datetime.now(timezone.utc).isoformat())
        save()
        raise


if __name__ == "__main__":
    main()
