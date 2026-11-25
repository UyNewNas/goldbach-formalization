#!/usr/bin/env python3
"""Read-only source and saved-receipt checks; never invoke Lean or copy caches."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True

BASE_COMMIT = "d20acdf13882e17d97833064f5e7c54f3192b03c"
ACCEPTED_COMMIT = "a392cd8efcf4f0b4adf3d12f2d8db41370309ed3"
EXPECTED_MODULES = (
    "ImbalancedChen.P5OriginalHBMediumChartReserves",
    "ImbalancedChen.P5SmoothChartPhysicalHBBranch",
    "ImbalancedChen.P5ActualMultiGroupHBChartScale",
    "ImbalancedChen.P5ActualHBChartEventualClosure",
    "ImbalancedChen.P5OriginalChartRoughCutoff",
    "ImbalancedChen.P5ExactOriginalSmoothDyadicPartition",
    "ImbalancedChen.P5ActualLabelledPrimeSmoothCharts",
    "ImbalancedChen.Part3OriginalProperPowerChartCount",
    "ImbalancedChen.Part3ActualOriginalProperPowerChartBridge",
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def check_bytes(data: bytes, pin: dict, label: str) -> None:
    require(sha256(data) == pin["sha256"], label + ": SHA256 mismatch")
    if "bytes" in pin:
        require(len(data) == pin["bytes"], label + ": size mismatch")
    if "git_blob" in pin:
        require(blob_sha1(data) == pin["git_blob"], label + ": Git blob mismatch")


def repository_path(repo: Path, name: str) -> Path:
    path = repo / name
    require(not Path(name).is_absolute(), "absolute repository path")
    require(path.resolve().is_relative_to(repo), "path escaped repository")
    return path


def git_bytes(repo: Path, commit: str, name: str) -> bytes:
    repository_path(repo, name)
    require(commit in (BASE_COMMIT, ACCEPTED_COMMIT), "unapproved Git commit")
    env = dict(os.environ, GIT_NO_LAZY_FETCH="1", GIT_OPTIONAL_LOCKS="0")
    result = subprocess.run(
        ["git", "-c", "protocol.allow=never", "show", commit + ":" + name],
        cwd=repo,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    require(result.returncode == 0, "required local Git source unavailable: " + name)
    return result.stdout


def imports(data: bytes) -> list[str]:
    return [
        module
        for line in data.decode("utf-8").splitlines()
        if line.startswith("import ")
        for module in line[len("import ") :].split()
    ]


def main() -> None:
    require(len(sys.argv) == 1, "this verifier accepts no arguments")
    here = Path(__file__).resolve().parent
    repo = here.parents[3]
    manifest_bytes = (here / "ADOPTION_MANIFEST.json").read_bytes()
    manifest = json.loads(manifest_bytes)
    require(manifest["schema"] == "p15_existing_atlas_dependency_source_reuse_v1", "schema mismatch")
    require(manifest["base_commit"] == BASE_COMMIT, "base commit mismatch")
    require(manifest["accepted_publication_commit"] == ACCEPTED_COMMIT, "accepted commit mismatch")
    require(manifest["new_Lean_acceptance_claimed"] is False, "new acceptance claim")
    check_bytes(Path(__file__).read_bytes(), manifest["verifier"], "verifier")
    rows = manifest["modules"]
    require(tuple(row["module"] for row in rows) == EXPECTED_MODULES, "owner set or order mismatch")

    phase1_pin = manifest["phase1_exclusion"]["source_manifest"]
    phase1_bytes = git_bytes(repo, BASE_COMMIT, phase1_pin["repository_path"])
    check_bytes(phase1_bytes, phase1_pin, "pinned phase1 source closure")
    phase1 = json.loads(phase1_bytes)
    require(len(phase1["project_sources"]) == 316, "phase1 source count mismatch")
    require(not set(EXPECTED_MODULES).intersection(phase1["project_sources"]), "phase1 owner intersection")
    for module, pin in phase1["project_sources"].items():
        check_bytes(repository_path(repo, pin["path"]).read_bytes(), pin, "phase1 " + module)

    evidence = {}
    for key, pin in manifest["historical_evidence"].items():
        data = git_bytes(repo, ACCEPTED_COMMIT, pin["repository_path"])
        check_bytes(data, pin, "historical evidence " + key)
        require(repository_path(repo, pin["repository_path"]).read_bytes() == data, "historical evidence changed: " + key)
        evidence[key] = json.loads(data)
    api = evidence["verification/API_IDENTITY.json"]
    source_selection = {row["module"]: row for row in evidence["SOURCE_INSTALL.json"]["project_sources"]}
    proof_repairs = {row["module"]: row for row in api["dependency_proof_body_compatibility_repairs"]}
    kernel = evidence["verification/KERNEL_REPLAY_RECEIPT.json"]
    kernel_results = {row["module"]: row for row in kernel["results"]}
    public = evidence["verification/PUBLIC_AUDIT_RECEIPT.json"]
    coverage = evidence["verification/coverage/COVERAGE_ADDENDUM.json"]
    normal = evidence["verification/BUILD_RECEIPT.json"]
    require(normal["exit_code"] == public["exit_code"] == coverage["exit_code"] == 0, "old receipt failure")
    require(public["contains_sorryAx"] is False and not public["unexpected_axioms"] and not public["owned_axiom_declarations"], "old axiom audit mismatch")
    require(coverage["canonical_owner_bindings_equal"] is True and coverage["name_sets_equal"] is True, "old owner coverage mismatch")
    selection_sha = manifest["historical_acceptance_scope"]["source_selection_sha256"]
    require(normal["source_selection_sha256"] == public["source_selection_sha256"] == kernel["source_selection_sha256"] == selection_sha, "old source selection mismatch")

    snapshot_pin = manifest["saved_P1_reindex_observation"]
    snapshot_bytes = repository_path(repo, snapshot_pin["repository_path"]).read_bytes()
    check_bytes(snapshot_bytes, snapshot_pin, "saved P1 observation")
    snapshot = json.loads(snapshot_bytes)
    require(snapshot["job"] == snapshot_pin["job"], "saved observation job mismatch")
    observed = {row["module"]: row for row in snapshot["rows"] if "module" in row}
    require(len(observed) == 58, "saved observation owner count mismatch")
    receipt_pins = {row["receipt_path"]: row["binding"] for row in snapshot["rows"] if "receipt_path" in row}
    for expected in manifest["live_match_binding"]["receipt_and_guard_pins"]:
        require(receipt_pins.get(expected["path"]) == {"bytes": expected["bytes"], "sha256": expected["sha256"]}, "saved receipt/guard mismatch")
    config = snapshot["rows"][0]
    require(config["root"] == "/workspace/blue-reindex-build" and config["exists"] is True, "saved donor root mismatch")
    for expected in manifest["live_match_binding"]["project_configuration_pins"]:
        name = expected["path"].rsplit("/", 1)[1]
        require(config["configuration"][name] == {"bytes": expected["bytes"], "sha256": expected["sha256"]}, "saved project config mismatch")

    for row in rows:
        module = row["module"]
        canonical = module.replace(".", "/") + ".lean"
        require(row["canonical_path"] == canonical, "canonical path mismatch")
        old = git_bytes(repo, BASE_COMMIT, canonical)
        check_bytes(old, row["before"], module + " old source")
        snapshot_path = row["before"]["snapshot_path"]
        require(snapshot_path == str(here.relative_to(repo)) + "/preimages/" + canonical, "preimage snapshot path mismatch")
        require(repository_path(repo, snapshot_path).read_bytes() == old, "preimage snapshot changed")
        new = git_bytes(repo, ACCEPTED_COMMIT, row["after"]["source_repository_path"])
        check_bytes(new, row["after"], module + " accepted source")
        require(repository_path(repo, canonical).read_bytes() == new, "canonical source is not accepted bytes: " + module)
        require(repository_path(repo, row["after"]["source_repository_path"]).read_bytes() == new, "historical postimage changed")
        require(imports(old) == imports(new) == row["direct_imports"], "import change: " + module)
        require(source_selection[module]["sha256"] == row["after"]["sha256"], "selected source mismatch")

        repair = proof_repairs[module]
        require(repair["registered_preimage"]["sha256"] == row["before"]["sha256"], "repair preimage mismatch")
        blocks = list(repair["proof_blocks"])
        for key, block_key in (("declaration_syntax_compatibility_repairs", "syntax_blocks"), ("elaboration_context_compatibility_repairs", "context_blocks")):
            for exception in api[key]:
                if exception["module"] == module:
                    blocks.extend(exception[block_key])
        replay = old.decode("utf-8")
        occurrences = 0
        for block in blocks:
            count = replay.count(block["before"])
            require(count > 0, "recorded repair block absent: " + module)
            occurrences += count
            replay = replay.replace(block["before"], block["after"])
        require(replay.encode("utf-8") == new, "recorded repair replay differs: " + module)
        require(occurrences == row["repair_review"]["replayed_occurrence_count"], "repair occurrence mismatch")

        accepted = row["historical_acceptance"]
        require(kernel["target_objects"][module] == accepted["olean"], "accepted object mismatch")
        require(kernel_results[module] == accepted["named_kernel_result"] and kernel_results[module]["exit_code"] == 0, "named kernel result mismatch")
        require(public["per_module_public_export_counts"][module] == coverage["per_module_canonical_public_counts"][module] == accepted["canonical_public_owner_count"], "public owner count mismatch")
        live = observed[module]
        require(live["source"] == {"bytes": row["after"]["bytes"], "sha256": row["after"]["sha256"]}, "saved donor source mismatch")
        require(live["outputs"] == row["saved_live_outputs"], "saved donor outputs mismatch")
        require(live["outputs"][".olean"]["sha256"] == accepted["olean"]["sha256"], "saved accepted olean mismatch")

    closure = manifest["reused_source_subclosure"]["sources"]
    require(len(closure) == 68, "reused source closure count mismatch")
    for row in closure:
        name = row["module"].replace(".", "/") + ".lean"
        data = repository_path(repo, name).read_bytes()
        require(sha256(data) == row["accepted_selected_sha256"], "current reused closure source mismatch: " + row["module"])
        require(source_selection[row["module"]]["sha256"] == row["accepted_selected_sha256"], "old selected closure source mismatch")
        project_imports = [name for name in imports(data) if name.startswith("ImbalancedChen.")]
        require(project_imports == row["project_imports"], "reused closure import mismatch")

    print(json.dumps({
        "status": "PASS_EXISTING_SOURCE_REUSE_STATIC_CHECKS_ONLY",
        "manifest_sha256": sha256(manifest_bytes),
        "canonical_postimages": len(rows),
        "preserved_preimages": len(rows),
        "phase1_sources_unchanged": 316,
        "phase1_owner_intersection": 0,
        "exact_reused_source_subclosure": len(closure),
        "saved_named_kernel_object_matches": len(rows),
        "Lean_invocations": 0,
        "cloud_queries": 0,
        "cache_writes": 0,
        "new_Lean_acceptance": False,
    }, ensure_ascii=False, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (KeyError, ValueError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "HOLD", "reason": str(error)}, ensure_ascii=False), file=sys.stderr)
        raise SystemExit(1)
