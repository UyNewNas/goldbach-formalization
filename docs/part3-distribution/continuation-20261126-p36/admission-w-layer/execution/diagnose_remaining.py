#!/usr/bin/env python3
"""Diagnose unaccepted owner sources in private outputs; grants no formal credit."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def digest(path):
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--project", type=Path, required=True)
parser.add_argument("--source-commit", required=True)
parser.add_argument("--reference-report", type=Path, required=True)
parser.add_argument("--output", type=Path, required=True)
parser.add_argument("--modules", nargs="+", choices=("P3OriginalU5RootVInputs", "P3OriginalU5CoarseRootV",
                    "P3OriginalU5RoughEndpoints", "P3OriginalU5FullWLayer"),
                    default=("P3OriginalU5RootVInputs", "P3OriginalU5CoarseRootV",
                             "P3OriginalU5RoughEndpoints", "P3OriginalU5FullWLayer"))
args = parser.parse_args()
project = args.project.resolve(strict=True)
head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
if head != args.source_commit:
    raise RuntimeError("Diagnostic source commit differs")
subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=project, check=True)
reference = json.loads(args.reference_report.read_bytes())
if reference["project"] != str(project):
    raise RuntimeError("Reference environment project differs")
lean = Path(reference["compiler"]["path"])
if digest(lean) != "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550":
    raise RuntimeError("Diagnostic compiler differs")
args.output.mkdir(parents=True, exist_ok=False)
objroot = args.output / "lib/lean"
targets = tuple(args.modules)
# Lean selects a namespace directory as a unit. Mirror the existing first
# search root by file symlinks; an empty ImbalancedChen directory shadows it.
# Exclude every target facet so compilation cannot overwrite the original cache.
original_objects = Path(reference["lean_path"][0])
for cached in original_objects.rglob("*"):
    if cached.is_file() and cached.name.split(".", 1)[0] not in targets:
        mirrored = objroot / cached.relative_to(original_objects)
        mirrored.parent.mkdir(parents=True, exist_ok=True)
        mirrored.symlink_to(cached)
env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(objroot), *reference["lean_path"]]),
       "LEAN_SYSROOT": str(lean.parent.parent), "LEAN_NUM_THREADS": "1"}
records = []
coarse_failed = False
prerequisite = "P2OriginalU5PlateauRectangle"
needs_prerequisite = ("P3OriginalU5FullWLayer" in targets and
                      not (objroot / "ImbalancedChen" / (prerequisite + ".olean")).exists())
stems = (prerequisite, *targets) if needs_prerequisite else targets
for stem in stems:
    module = "ImbalancedChen." + stem
    if stem == "P3OriginalU5RoughEndpoints" and coarse_failed:
        records.append({"module": module, "status": "BLOCKED_BY_COARSE_DIAGNOSTIC"})
        continue
    source = project / "ImbalancedChen" / (stem + ".lean")
    output = objroot / "ImbalancedChen" / (stem + ".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    command = [str(lean), "-t0", "-j1", "-R", str(project), "-DwarningAsError=true",
               "-o", str(output), str(source)]
    result = subprocess.run(command, cwd=project, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=300)
    log = args.output / (stem + ".log")
    log.write_bytes(("command=" + json.dumps(command) + "\n").encode() + result.stdout)
    record = {"module": module, "source_sha256": digest(source), "exit_code": result.returncode,
              "command": command, "log": str(log), "log_sha256": digest(log)}
    records.append(record)
    print("P36_PRIVATE_DIAGNOSTIC " + json.dumps(record), flush=True)
    print(result.stdout.decode(), end="", flush=True)
    if stem == "P3OriginalU5CoarseRootV":
        coarse_failed = result.returncode != 0
summary = {"status": "DIAGNOSTIC_ONLY", "formal_credit": False, "source_commit": head,
           "reference_report": str(args.reference_report),
           "reference_report_sha256": digest(args.reference_report), "records": records}
(args.output / "diagnostics.json").write_text(json.dumps(summary, indent=2) + "\n")
print("P36_PRIVATE_DIAGNOSTIC_SUMMARY " + json.dumps(summary), flush=True)
raise SystemExit(0 if all(record.get("exit_code") == 0 for record in records) else 1)
