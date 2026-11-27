"""Identify the two family-budget terminals and their accepted source closure."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Callable


DOCS = Path("docs/part3-distribution/p31-family-scale-budget-20261127")
PRIOR_CLOSURE = Path("docs/part3-distribution/p31-actual-mass-budget-20261127/PROJECT_IMPORT_CLOSURE.json")
PRIOR_SHA256 = "bc9bc81b59ce4dd5b4a7b50af5d8ac6fa27df852b09d37fef3689a6d7566e01d"
INTAKE_SHA256 = "2ad289cf28396e28f415d10f0fb59a168260a92022efc47d24052a51963d5acb"


def pinned_json(path: Path, expected: str) -> dict:
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise RuntimeError(f"P3.1 family scale input digest mismatch: {path}")
    return json.loads(data)


def validate_family_scale_intake(
    root: Path, targets: tuple[str, ...],
    validate_project_closure: Callable[[Path, dict, tuple[str, ...]], tuple[str, ...]],
) -> tuple[tuple[str, ...], dict, dict, list[Path]]:
    intake_path = root / DOCS / "SOURCE_INTAKE.json"
    prior_path = root / PRIOR_CLOSURE
    closure_path = root / DOCS / "PROJECT_IMPORT_CLOSURE.json"
    intake = pinned_json(intake_path, INTAKE_SHA256)
    prior = pinned_json(prior_path, PRIOR_SHA256)
    closure = pinned_json(closure_path, intake["closure_sha256"])
    provenance_path = root / DOCS / "FAMILY_SCALE_PROVENANCE.json"
    pinned_json(provenance_path, intake["provenance_sha256"])

    current = {row["module"]: row for row in closure["project_sources"]}
    if (intake["whole_p31_complete"] is not False
            or intake["outer_mode_sum_paid"] is not False
            or intake["sources"] != [current[m] for m in targets]):
        raise RuntimeError("P3.1 family scale terminal identities or scope changed")

    # The common validator reads every reachable project source, checks its
    # digest and reconstructs imports from the Lean header, including externals.
    modules = validate_project_closure(root, closure, targets)
    old = {row["module"]: row for row in prior["project_sources"]}
    if (len(old) != 85 or set(targets) & old.keys()
            or set(modules) != set(targets) | old.keys()
            or any(current[m] != row for m, row in old.items())):
        raise RuntimeError("P3.1 family scale closure differs from its 85 frozen providers")

    paths = [intake_path, prior_path, closure_path, provenance_path,
             root / "verification/p31_family_scale_intake.py",
             root / "verification/build_part3_pinned_closure.py",
             root / "verification/test_part3_source_object_gate.py"]
    paths.extend(root / current[m]["path"] for m in modules)
    return modules, closure, intake, paths
