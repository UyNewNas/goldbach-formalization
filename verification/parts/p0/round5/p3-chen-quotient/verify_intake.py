#!/usr/bin/env python3
"""Verify P0's evidence-only intake of the fixed P3 quotient supplier."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import zipfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
ROOT_EVIDENCE = ROOT / "verification/parts/p0/round4/post-publication-d036"
MODULE = "ImbalancedChen.ChenQuotientSieveRemainders"
SOURCE = "ImbalancedChen/ChenQuotientSieveRemainders.lean"
IMPORT_LINE = f"import {MODULE}"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def run_json(command: list[str], cwd: Path) -> dict:
    result = subprocess.run(command, cwd=cwd, check=True, text=True, capture_output=True)
    return json.loads(result.stdout)


def git_bytes(commit: str, path: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=ROOT,
        check=True,
        capture_output=True,
    ).stdout


def git_blob(commit: str, path: str) -> str:
    return subprocess.run(
        ["git", "rev-parse", f"{commit}:{path}"],
        cwd=ROOT,
        check=True,
        text=True,
        capture_output=True,
    ).stdout.strip()


def main() -> None:
    receipt = json.loads((HERE / "INTAKE_RECEIPT.json").read_text(encoding="utf-8"))
    producer = json.loads((HERE / "PRODUCER_RECEIPT.json").read_text(encoding="utf-8"))
    require(receipt["status"] == "PASS", "intake receipt status")
    require(receipt["production_changes_in_batch"] is False, "production-change boundary")
    require(producer["status"] == "PASS", "producer receipt status")
    require(producer["production"]["module"] == MODULE, "producer module")
    require(producer["production"]["source"] == SOURCE, "producer source")

    source_hash = receipt["source_sha256"]
    source_blob = receipt["source_git_blob"]
    require(sha256(ROOT / SOURCE) == source_hash, "working-tree source hash")
    for commit in (
        receipt["p0_verified_root_commit"],
        receipt["p0_acceptance_parent"],
        receipt["p3_evidence_publication_commit"],
        receipt["p3_production_source_commit"],
    ):
        require(hashlib.sha256(git_bytes(commit, SOURCE)).hexdigest() == source_hash,
                f"source hash at {commit}")
        require(git_blob(commit, SOURCE) == source_blob, f"source blob at {commit}")

    imports = (ROOT / "ImbalancedChen.lean").read_text(encoding="utf-8").splitlines()
    require(IMPORT_LINE in imports, "public root import")
    retained = receipt["retained_evidence"]
    require(sha256(HERE / "PRODUCER_RECEIPT.json") == retained["producer_receipt_sha256"],
            "producer receipt hash")
    require(sha256(HERE / "PRODUCER_AUDIT_SOURCE.lean") ==
            retained["producer_audit_source_sha256"], "producer audit source hash")
    require(sha256(HERE / "producer-evidence.tar.xz") ==
            retained["producer_evidence_bundle_sha256"], "producer evidence hash")
    require(sha256(HERE / "verify_producer_evidence.py") ==
            retained["adapted_producer_verifier_sha256"], "producer verifier hash")
    require(sha256(ROOT_EVIDENCE / "core-artifact.zip") ==
            retained["p0_core_artifact_sha256"], "P0 core artifact hash")

    producer_result = run_json(["python3", str(HERE / "verify_producer_evidence.py")], ROOT)
    require(producer_result["status"] == "PASS", "producer evidence verifier")
    require(producer_result["owned_declarations"] == 34, "producer declaration count")
    require(producer_result["actual_import_objects"] == 4237, "producer import count")
    require(set(producer_result["transitive_axioms"]) == ALLOWED, "producer axiom union")
    require(producer_result["prime_ap_distribution_compiled"] is False,
            "producer mathematical boundary")

    root_result = run_json(["python3", str(ROOT_EVIDENCE / "verify_post_publication.py")], ROOT)
    require(root_result["status"] == "PASS", "P0 sealed-root verifier")
    require(root_result["sealed_commit"] == receipt["p0_verified_root_commit"],
            "P0 sealed-root commit")
    require(root_result["hLower_hUpper_discharged"] is False, "conditional-main boundary")

    with zipfile.ZipFile(ROOT_EVIDENCE / "core-artifact.zip") as archive:
        build_log = archive.read("_temp/lean-verification-logs/build.log").decode()
        replay_log = archive.read("_temp/lean-verification-logs/leanchecker.log").decode()
    require("Built ImbalancedChen.ChenQuotientSieveRemainders" in build_log,
            "module build line in sealed root")
    require("replaying ImbalancedChen.ChenQuotientSieveRemainders\n" in replay_log,
            "module replay line in sealed root")

    boundary = receipt["mathematical_boundary"]
    require(boundary == {
        "direct_supplier_gap_closed": True,
        "prime_ap_distribution_compiled": False,
        "bombieri_vinogradov_direct_supplier_restored": False,
        "new_part3_distribution_theorem": False,
        "hLower_discharged": False,
        "hUpper_discharged": False,
        "main_theorem_unconditional": False,
    }, "mathematical boundary")

    print(json.dumps({
        "status": "PASS",
        "module": MODULE,
        "source_sha256": source_hash,
        "owned_declarations": producer_result["owned_declarations"],
        "actual_import_objects": producer_result["actual_import_objects"],
        "producer_gates": "PASS",
        "existing_p0_root_gates": "PASS",
        "production_changes_in_batch": False,
        "prime_ap_distribution_compiled": False,
        "hLower_hUpper_discharged": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
