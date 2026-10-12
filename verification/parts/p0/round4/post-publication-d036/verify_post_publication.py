#!/usr/bin/env python3
"""Verify the immutable post-publication evidence for P0 commit d0366ce."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import zipfile


HERE = Path(__file__).resolve().parent
HEAD = "d0366ce64272e81faf6166a8a90050f56b328d38"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED_HASHES = {
    "core-artifact.zip": "4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8",
    "variable-envelope-artifact.zip": "70cb8852b79d8409d1982016ba60823982a30d7320c80195620ecf058f5d31a7",
    "core-run.json": "17678dc270a5330303efb609cc939b6b81cf5583ac8a6b2318e336c37c6303c8",
    "core-jobs.json": "3d6f3c6c01546a667001b187f24cff4639a9651cab74569781135c1741f34d8b",
    "core-artifacts.json": "4f85e3afe8903531995425c2f886f7887242e5d7d74757ed1327107739b49f67",
    "variable-envelope-run.json": "154cdf1a07a9be5a8d936f521f5999490ed089476d68ae95d98813a7dec57eb3",
    "variable-envelope-jobs.json": "6033cec586837e8fa5ec78cc6c54bdd9f358dcb97e6f6e9ba3cf456b100e0d53",
    "variable-envelope-artifacts.json": "b82db18e4a8a8612d7ba2d2a2682c258c1a5fbdad56ab565380b64a0c18f5bbc",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_json(name: str):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def safe_zip(archive: zipfile.ZipFile) -> None:
    for info in archive.infolist():
        path = PurePosixPath(info.filename)
        require(not path.is_absolute(), f"absolute ZIP member: {info.filename}")
        require(".." not in path.parts, f"parent traversal ZIP member: {info.filename}")
        mode = (info.external_attr >> 16) & 0o170000
        require(mode != 0o120000, f"symlink ZIP member: {info.filename}")


def unique_suffix(archive: zipfile.ZipFile, suffix: str) -> str:
    matches = [name for name in archive.namelist() if name.endswith(suffix)]
    require(len(matches) == 1, f"expected one {suffix}, found {len(matches)}")
    return matches[0]


def check_run(name: str, run_id: int, workflow: str) -> None:
    run = load_json(f"{name}-run.json")
    require(run["id"] == run_id, f"{name} run id")
    require(run["name"] == workflow, f"{name} workflow name")
    require(run["head_sha"] == HEAD, f"{name} head SHA")
    require(run["run_attempt"] == 1, f"{name} run attempt")
    require(run["status"] == "completed" and run["conclusion"] == "success", f"{name} run result")

    jobs = load_json(f"{name}-jobs.json")["jobs"]
    require(len(jobs) == 1, f"{name} job count")
    job = jobs[0]
    require(job["status"] == "completed" and job["conclusion"] == "success", f"{name} job result")
    require(all(step["status"] == "completed" and step["conclusion"] == "success" for step in job["steps"]),
            f"{name} step result")

    artifacts = load_json(f"{name}-artifacts.json")["artifacts"]
    require(len(artifacts) == 1, f"{name} artifact count")
    artifact = artifacts[0]
    require(not artifact["expired"], f"{name} artifact expired")
    require(artifact["workflow_run"]["id"] == run_id, f"{name} artifact run")
    require(artifact["workflow_run"]["head_sha"] == HEAD, f"{name} artifact SHA")


def check_core() -> dict[str, int]:
    with zipfile.ZipFile(HERE / "core-artifact.zip") as archive:
        safe_zip(archive)
        provenance = archive.read("_temp/lean-verification-logs/provenance.log").decode()
        require(f"project_commit={HEAD}\n" in provenance, "core provenance SHA")
        require("toolchain=leanprover/lean4:v4.33.0-rc1\n" in provenance, "core toolchain")
        require("run=38289734671 attempt=1\n" in provenance, "core run binding")

        outcomes = archive.read("_temp/lean-verification-logs/outcomes.log").decode().splitlines()
        expected_outcomes = {
            "build=success", "leanchecker=success", "axiom-audit=success",
            "round3-types=success", "round4-targets=success", "round4-types=success",
        }
        require(set(outcomes) == expected_outcomes, "core outcomes")

        for stage in ("build", "round4-targets", "leanchecker", "axiom-audit", "round3-types", "round4-types"):
            timing = archive.read(f"_temp/lean-verification-logs/{stage}.timing.tsv").decode().splitlines()
            require(len(timing) == 2 and timing[1].endswith("\t0"), f"{stage} exit code")

        build_log = archive.read("_temp/lean-verification-logs/build.log").decode()
        target_log = archive.read("_temp/lean-verification-logs/round4-targets.log").decode()
        replay_log = archive.read("_temp/lean-verification-logs/leanchecker.log").decode()
        audit_log = archive.read("_temp/lean-verification-logs/axiom-audit.log").decode()
        require("Build completed successfully (9802 jobs)." in build_log, "full build marker")
        require("Build completed successfully (3407 jobs)." in target_log, "round4 target marker")
        require("replaying ImbalancedChen\n" in replay_log, "root stock replay marker")
        require("audited 5872 declaration(s) under 'ImbalancedChen'" in audit_log, "root audit count")
        require("all within the allowlist [propext, Classical.choice, Quot.sound]" in audit_log, "root axiom allowlist")

        r3 = json.loads(archive.read(unique_suffix(archive, "/part0-round3-types/20261012T191009700344Z/receipt.json")))
        r4 = json.loads(archive.read(unique_suffix(archive, "/part0-round4-types/20261012T191316121045Z/receipt.json")))
        for label, receipt, count in (("round3", r3, 198), ("round4", r4, 414)):
            require(receipt["status"] == "PASS", f"{label} type receipt")
            require(receipt["source_commit"] == HEAD and receipt["source_commit_after"] == HEAD,
                    f"{label} type source binding")
            require(receipt["declaration_count"] == count, f"{label} declaration count")
            require(set(receipt["transitive_axiom_union"]) == ALLOWED, f"{label} axioms")
            require(receipt["bridge_count"] == 1, f"{label} bridge count")
            require(receipt["hLower_hUpper_discharged"] is False, f"{label} conditional bridge status")
        require(r4["expected_defining_module_counts"] == {
            "ImbalancedChen.StoredHistoricalBoxPermit": 14,
            "ImbalancedChen.Certificates.PairedV2Batch4To64Data": 72,
            "ImbalancedChen.Certificates.PairedV2Batch4To64": 207,
            "ImbalancedChen.Certificates.PairedV2Prefix64": 121,
        }, "round4 defining-module counts")
        return {"root_declarations": 5872, "round3_types": 198, "round4_types": 414}


def check_variable_envelope() -> int:
    with zipfile.ZipFile(HERE / "variable-envelope-artifact.zip") as archive:
        safe_zip(archive)
        require(archive.read("outcome.log").decode() == "verification=success\n", "VE outcome")
        head = archive.read("head-commit.log").decode()
        require(head.endswith(f"{HEAD}\n"), "VE head binding")
        report = json.loads(archive.read("report.json"))
        require(report["status"] == "PASSED" and report["head_commit"] == HEAD, "VE report result")
        require(report["declaration_count"] == 358, "VE declaration count")
        require(set(report["allowed_transitive_axioms"]) == ALLOWED, "VE axiom allowlist")
        require(all(stage["exit_code"] == 0 for stage in report["stages"]), "VE stage exit codes")
        require(report["working_tree"] == "", "VE CI working tree")
        return report["declaration_count"]


def main() -> None:
    actual_hashes = {name: sha256(HERE / name) for name in EXPECTED_HASHES}
    require(actual_hashes == EXPECTED_HASHES, "evidence SHA256 map")
    check_run("core", 38289734671, "Lean core verification")
    check_run("variable-envelope", 38289734726, "Variable envelope verification")
    require(load_json("core-artifacts.json")["artifacts"][0]["digest"] ==
            f"sha256:{EXPECTED_HASHES['core-artifact.zip']}", "core artifact digest")
    require(load_json("variable-envelope-artifacts.json")["artifacts"][0]["digest"] ==
            f"sha256:{EXPECTED_HASHES['variable-envelope-artifact.zip']}", "VE artifact digest")
    core_counts = check_core()
    ve_count = check_variable_envelope()
    print(json.dumps({
        "status": "PASS",
        "sealed_commit": HEAD,
        "core_run": 38289734671,
        "variable_envelope_run": 38289734726,
        **core_counts,
        "variable_envelope_declarations": ve_count,
        "hLower_hUpper_discharged": False,
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
