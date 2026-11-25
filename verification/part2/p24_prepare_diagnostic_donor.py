#!/usr/bin/env python3
"""Copy diagnostic inputs and unchanged earlier diagnostic outputs, without acceptance.

This transports bytes only. It never writes accepted compilation records,
runs Lean/Lake, or qualifies native inputs. Package links are read-only inputs
to p24_diagnostic_compile.py, which invokes Lean directly rather than Lake.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
from p24_diagnostic_compile import (
    DONOR_EVIDENCE, DONOR_INCOMPLETE, DONOR_RECEIPT, FACETS, Hashes, STATUS,
    core_header, diagnostic_donor_files, physical_match, previous_external_binding, write,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("modules", nargs="+")
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--donor-root", type=Path, required=True)
    parser.add_argument("--previous-output", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    root, donor, previous, out = (p.resolve() for p in
        (args.project_root, args.donor_root, args.previous_output, args.out))
    if out.exists() or not out.is_relative_to(root) or out.is_relative_to(donor):
        raise ValueError("Use a new private output directory, outside the donor")
    hashes = Hashes()
    nodes, order = {}, []

    def visit(name):
        if name in nodes:
            return
        if not name.startswith("ImbalancedChen."):
            raise ValueError("Unexpected project namespace")
        rel = Path(name.replace(".", "/") + ".lean")
        source = root / rel
        im, _ = core_header(source.read_text())
        nodes[name] = {"source": source, "relative": rel, "deps":
                       [x for x in im if x.startswith("ImbalancedChen.")]}
        for dep in nodes[name]["deps"]:
            visit(dep)
        order.append(name)

    for name in args.modules:
        visit(name)
    previous_evidence = hashes.files(previous / name for name in DONOR_EVIDENCE)
    old_runtime = json.loads((previous / "RUNTIME.json").read_text())
    old_records = json.loads((previous / "RECORDS.json").read_text())
    old_summary = json.loads((previous / "SUMMARY.json").read_text())
    old_external = json.loads((previous / "EXTERNAL_INPUTS_BEFORE.json").read_text())
    before = old_external["files"]
    after = json.loads((previous / "EXTERNAL_INPUTS_AFTER.json").read_text())
    if (old_summary.get("status") != STATUS or old_summary.get("current_inputs_stable") is not True
            or after.get("equal_to_before") is not True or before != after["files"]):
        raise ValueError("Previous diagnostic lacks stable recorded inputs")

    def matches(path, expected):
        return physical_match(path, expected, hashes)

    toolchain = Path(old_runtime["lean_sysroot"]).resolve()
    runtime_binding = previous_external_binding(donor, toolchain, previous, old_runtime, old_external, hashes)
    external_stable = True
    out.mkdir(parents=True)
    incomplete = out / DONOR_INCOMPLETE
    incomplete.write_text("Preparation incomplete; not eligible for diagnostic consumption.\n")
    lib = out / ".lake/build/lib/lean"
    lib.mkdir(parents=True)
    (out / ".lake/packages").symlink_to((donor / ".lake/packages").resolve(), target_is_directory=True)
    copied, reused, skipped = {}, {}, {}

    def copy_bound(source, target, expected=None):
        digest = hashes.digest(source)
        if expected is not None and (digest != expected["sha256"] or source.stat().st_size != expected["bytes"]):
            raise ValueError("Earlier output changed before diagnostic copy")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        if hashes.digest(source) != digest or hashes.digest(target) != digest:
            raise ValueError("Bytes changed during diagnostic copy")
        return {"source": str(source), "target": str(target), "sha256": digest}

    for name in order:
        rel = nodes[name]["relative"]
        src = donor / rel
        stem = name.replace(".", "/")
        if src.is_file():
            entries = [copy_bound(src, out / rel)]
            for suffix in FACETS:
                p = donor / ".lake/build/lib/lean" / (stem + suffix)
                if p.is_file():
                    entries.append(copy_bound(p, lib / (stem + suffix)))
            copied[name] = entries
        row = old_records.get(name, {})
        if row.get("exit_code") != 0 or row.get("compiler_exit_code") != 0:
            continue
        try:
            if not external_stable or row.get("inputs_unchanged") is not True:
                raise ValueError("Earlier external/input snapshot is not stable")
            if row["inputs_before"] != row["inputs_after"]:
                raise ValueError("Earlier compile inputs differ")
            raw = subprocess.check_output(["git", "show", args.source_commit + ":" + rel.as_posix()], cwd=root)
            if (hashlib.sha256(raw).hexdigest() != row["source_sha256"]
                    or nodes[name]["source"].read_bytes() != raw):
                raise ValueError("Current source differs from earlier diagnostic source")
            for path, expected in row["inputs_before"].items():
                p = Path(path)
                if not matches(p, expected):
                    raise ValueError("An original diagnostic input changed: " + path)
                if p.is_relative_to(previous / "lib"):
                    mapped = lib / p.relative_to(previous / "lib")
                    if not matches(mapped, expected):
                        raise ValueError("Current diagnostic dependency differs: " + str(mapped))
            for dep in row["project_dependency_modules"]:
                old_stem = previous / "lib" / dep.replace(".", "/")
                new_stem = lib / dep.replace(".", "/")
                old_suffixes = {s for s in FACETS if str(old_stem) + s in row["inputs_before"]}
                new_suffixes = {s for s in FACETS if Path(str(new_stem) + s).is_file()}
                if old_suffixes != new_suffixes:
                    raise ValueError("Diagnostic dependency facet set changed: " + dep)
            output = row["output_facets"]
            if not output or not any(p.endswith(".olean") for p in output):
                raise ValueError("Missing successful output facets")
            for path, expected in output.items():
                if not matches(Path(path), expected):
                    raise ValueError("Earlier output facet changed")
        except (KeyError, ValueError, OSError, subprocess.CalledProcessError) as error:
            skipped[name] = str(error)
            continue
        # All validation precedes mutation. A copy failure aborts the command;
        # it must not leave a partially overlaid donor eligible for the next step.
        wanted = {lib / Path(path).relative_to(previous / "lib") for path in output}
        for suffix in FACETS:
            stale = lib / (stem + suffix)
            if stale.is_file() and stale not in wanted:
                stale.unlink()
        entries = [copy_bound(Path(path), lib / Path(path).relative_to(previous / "lib"), expected)
                   for path, expected in output.items()]
        (out / rel).parent.mkdir(parents=True, exist_ok=True)
        (out / rel).write_bytes(raw)
        reused[name] = {"original_record": str(previous / "RECORDS.json"),
                        "source_commit": args.source_commit, "source_sha256": row["source_sha256"],
                        "facets": entries, "compile_credit": False, "kernel_credit": False}
    if previous_external_binding(out, toolchain, previous, old_runtime, old_external, hashes) != runtime_binding:
        raise ValueError("External runtime changed while preparing diagnostic donor")
    if not all(matches(Path(p), row) for p, row in previous_evidence.items()):
        raise ValueError("Previous diagnostic evidence changed while preparing donor")
    receipt = {"status": STATUS, "roots": args.modules, "old_external_inputs_stable": external_stable,
               "previous_output": str(previous), "previous_evidence": previous_evidence,
               "runtime_binding": runtime_binding, "prepared_files": diagnostic_donor_files(out, hashes),
               "base_inputs_copied": copied, "earlier_diagnostic_outputs_reused": reused,
               "earlier_outputs_not_reused": skipped, "proof_acceptance": False,
               "compile_credit": False, "kernel_credit": False}
    write(out / DONOR_RECEIPT, receipt)
    incomplete.unlink()
    print(json.dumps({"status": STATUS, "base_modules": len(copied),
                      "reused_prior_passes": sorted(reused), "not_reused": skipped,
                      "receipt": str(out / "DIAGNOSTIC_DONOR.json")}), flush=True)


if __name__ == "__main__":
    main()
