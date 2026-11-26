#!/usr/bin/env python3
"""Schedule original audits using the frozen exporter's exact selection block.

This helper does not replace the original audit runner or final full export.
It executes the unmodified receipt-selection AST from the SHA-pinned exporter,
including its original validate_receipt, artifact capture, candidate order and
duplicate-receipt handling. It omits only archive/provenance packaging, which is
not needed to choose the next original audit batch.
"""
from __future__ import annotations

import ast
from collections import defaultdict
import hashlib
import importlib
import json
from pathlib import Path
import sys

EXPORTER_SHA256 = "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645"
AUDIT_SHA256 = "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5"


def sha(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def select_current(root: Path, targets: list[str]) -> dict:
    root = root.resolve()
    exporter_path = root / "verification/part2/export_winner9_private_evidence.py"
    audit_path = root / "verification/part2/run_winner9_private_audit.py"
    assert sha(exporter_path) == EXPORTER_SHA256
    assert sha(audit_path) == AUDIT_SHA256
    sys.path.insert(0, str(exporter_path.parent))
    original = importlib.import_module("export_winner9_private_evidence")
    assert Path(original.__file__).resolve() == exporter_path
    live_pin = original.subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=original.MATHLIB, text=True).strip()
    original.require(live_pin == original.PIN,
                     "Live Mathlib checkout differs from the fixed pin")
    source = exporter_path.read_text()
    tree = ast.parse(source, filename=str(exporter_path))
    mains = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "main"]
    assert len(mains) == 1
    loops = [n for n in mains[0].body if isinstance(n, ast.For)
             and isinstance(n.target, ast.Name) and n.target.id == "target"
             and isinstance(n.iter, ast.Name) and n.iter.id == "targets"]
    assert len(loops) == 1
    loop = loops[0]
    original_block = ast.get_source_segment(source, loop)
    assert original_block is not None
    driver_paths = [
        root / "docs/verification/20261124-p2-private/driver-v1.py",
        root / "docs/verification/20261124-p2-private/audit-driver-v2.py",
        root / "docs/verification/20261125-p2-resume/audit-driver-v3.py",
        audit_path,
    ]
    drivers = {sha(p): p for p in driver_paths if p.is_file() and sha(p) in original.DRIVER_FILES}
    original.require({original.DRIVER_V1, original.DRIVER_V2} <= set(drivers),
                     "Both exact historical audit driver versions must be available")
    registry_path = root / ".lake/p2-private/records.json"
    registry_raw = registry_path.read_bytes()
    registry_sha256 = hashlib.sha256(registry_raw).hexdigest()
    evidence = original.Evidence()
    context = dict(vars(original))
    context.update(root=root, audit_root=root / ".lake/p2-private/audit",
                   records=json.loads(registry_raw), evidence=evidence, drivers=drivers,
                   targets=sorted(set(targets)), common=set(), module_files={},
                   accepted={}, rejected=[], unselected=[], warnings=[],
                   project_union={}, owned_names=defaultdict(list))
    program = ast.Module(body=[loop], type_ignores=[])
    exec(compile(program, str(exporter_path), "exec"), context, context)
    evidence.verify_frozen()
    # Preserve the exact captured receipt/artifact bytes through this read-only
    # selection. These are additions to the original selection checks.
    for item in evidence.files.values():
        origin = Path(item["origin"])
        if origin.is_absolute():
            original.require(sha(origin) == item["sha256"],
                             "Captured evidence changed during selection: " + str(origin))
    original.require(sha(registry_path) == registry_sha256,
                     "Compile registry changed during selection")
    original.require(sha(exporter_path) == EXPORTER_SHA256 and sha(audit_path) == AUDIT_SHA256,
                     "Original evidence tools changed during selection")
    live_pin_after = original.subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=original.MATHLIB, text=True).strip()
    original.require(live_pin_after == original.PIN,
                     "Live Mathlib checkout changed during selection")
    duplicates = {n: owners for n, owners in context["owned_names"].items() if len(owners) > 1}
    original.require(not duplicates, "Duplicate owned declaration names across selected modules")
    accepted = context["accepted"]
    unselected = context["unselected"]
    original.require(set(accepted).isdisjoint(unselected)
                     and set(accepted) | set(unselected) == set(targets),
                     "Selected/unselected partition differs from requested scope")
    return {
        "selection_only": True,
        "final_original_export_still_required": True,
        "original_exporter_sha256": EXPORTER_SHA256,
        "original_audit_driver_sha256": AUDIT_SHA256,
        "unchanged_selection_block_sha256": hashlib.sha256(original_block.encode()).hexdigest(),
        "records_snapshot_sha256": registry_sha256,
        "accepted_module_count": len(accepted),
        "owned_declaration_count": sum(x["declaration_count"] for x in accepted.values()),
        "unique_owned_declaration_count": len(context["owned_names"]),
        "duplicate_owned_declarations": duplicates,
        "accepted_modules": accepted,
        "unselected_modules": unselected,
        "rejected_candidates": context["rejected"],
        "warnings": context["warnings"],
        "full_p2_complete": False,
    }
