#!/usr/bin/env python3
"""Negative consumer-control-flow checks, never actual GitHub/Lean evidence.

An isolated in-memory import uses impossible fixture run/job identities and a
non-Git fixture SHA. The production script and its fixed d0366ce constants are
unchanged. Every supplied CI metadata fixture is unsuccessful. No successful CI
artifact or PASS fixture is created. All subprocess execution is blocked here.
"""

from __future__ import annotations

import argparse
import contextlib
import copy
import hashlib
import io
import json
from pathlib import Path
import types


BASE = Path(__file__).resolve().parents[1]
SCRIPT = BASE / "consume_core_artifact.py"
CHECK_ROOT = BASE / "consumer-corrections" / "known-failure-state-fix"
FIXTURE_LABEL = "SYNTHETIC_CONSUMER_CONTROL_FLOW_FIXTURE_NOT_ACTUAL_CI_EVIDENCE"


def dump(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main() -> None:
    CHECK_ROOT.mkdir(parents=True, exist_ok=False)
    original_bytes = SCRIPT.read_bytes()
    script_sha256 = hashlib.sha256(original_bytes).hexdigest()
    compile(original_bytes, str(SCRIPT), "exec")
    fixture_module = types.ModuleType("consumer_negative_control_flow_fixture_only")
    fixture_module.__file__ = str(SCRIPT)
    exec(compile(original_bytes, str(SCRIPT), "exec"), fixture_module.__dict__)
    production_identity = {key: fixture_module.__dict__[key]
                           for key in ["EXPECTED_SHA", "EXPECTED_TREE", "EXPECTED_RUN", "EXPECTED_JOB"]}
    # Test-only runtime identity replacement prevents a synthetic failed record
    # from being mistaken for a claim about the actual d0366ce GitHub run.
    fixture_module.EXPECTED_SHA = "CONSUMER_FIXTURE_NOT_A_GIT_SHA"
    fixture_module.EXPECTED_TREE = "CONSUMER_FIXTURE_NOT_A_GIT_TREE"
    fixture_module.EXPECTED_RUN = -382
    fixture_module.EXPECTED_JOB = -114
    fixture_module.EXPECTED_REPOSITORY = "CONSUMER_FIXTURE/not-an-actual-repository"
    fixture_module.EXPECTED_BRANCH = "CONSUMER_FIXTURE/not-an-actual-branch"
    attempted_subprocesses = []

    def blocked_subprocess(*args, **kwargs):
        attempted_subprocesses.append({"args": repr(args), "kwargs": repr(kwargs)})
        raise RuntimeError("Consumer fixture forbids every subprocess, including Git/Lean/CI")

    fixture_module.subprocess = types.SimpleNamespace(PIPE=-1, run=blocked_subprocess)
    run = {
        "fixture_label": FIXTURE_LABEL,
        "id": fixture_module.EXPECTED_RUN,
        "head_sha": fixture_module.EXPECTED_SHA,
        "run_attempt": fixture_module.EXPECTED_ATTEMPT,
        "repository": {"full_name": fixture_module.EXPECTED_REPOSITORY},
        "head_branch": fixture_module.EXPECTED_BRANCH,
        "path": ".github/workflows/lean.yml",
        "status": "completed", "conclusion": "failure",
    }
    job = {
        "fixture_label": FIXTURE_LABEL,
        "id": fixture_module.EXPECTED_JOB,
        "run_id": fixture_module.EXPECTED_RUN,
        "head_sha": fixture_module.EXPECTED_SHA,
        "run_attempt": fixture_module.EXPECTED_ATTEMPT,
        "status": "completed", "conclusion": "failure",
        "steps": [
            {"name": name, "status": "completed", "conclusion": "failure" if i == 0 else "skipped",
             "started_at": "2000-01-01T00:00:00Z", "completed_at": "2000-01-01T00:00:01Z"}
            for i, name in enumerate(fixture_module.STAGE_NAMES.values())
        ],
    }
    artifact = {
        "fixture_label": FIXTURE_LABEL,
        "id": -117,
        "name": f"lean-verification-{fixture_module.EXPECTED_RUN}-{fixture_module.EXPECTED_ATTEMPT}",
        "workflow_run": {"id": fixture_module.EXPECTED_RUN, "head_sha": fixture_module.EXPECTED_SHA},
        "digest": "sha256:" + "0" * 64,
        "size_in_bytes": 0,
    }
    cases = [
        ("completed-failure-missing-zip", {"artifacts": [artifact]}, True,
         "The actual core artifact ZIP has not been supplied"),
        ("completed-failure-missing-artifact-item", {"artifacts": []}, True,
         "The expected core artifact is not listed in the supplied metadata"),
        ("completed-failure-missing-digest", {"artifacts": [{k: v for k, v in artifact.items() if k != "digest"}]}, True,
         "GitHub artifact SHA-256 metadata is missing"),
        ("completed-failed-run-only-other-evidence-missing", None, False,
         "The raw artifact metadata is missing"),
    ]
    results = []
    for name, artifacts, supply_jobs, expected_reason in cases:
        inputs = CHECK_ROOT / "fixture-inputs" / name
        dump(inputs / "run.json", run)
        if supply_jobs:
            dump(inputs / "jobs.json", {"fixture_label": FIXTURE_LABEL, "jobs": [job]})
        if artifacts is not None:
            dump(inputs / "artifacts.json", {"fixture_label": FIXTURE_LABEL, **copy.deepcopy(artifacts)})
        output = CHECK_ROOT / "fixture-results" / name
        args = argparse.Namespace(
            repo=CHECK_ROOT / "NO_REAL_GIT_REPOSITORY_FOR_THIS_FIXTURE",
            artifact_zip=None, run_json=inputs / "run.json",
            jobs_json=inputs / "jobs.json" if supply_jobs else None,
            artifacts_json=inputs / "artifacts.json" if artifacts is not None else None,
            output=output,
        )
        consumer = fixture_module.Consumer(args)
        consumer.report.update(
            verification_mode=FIXTURE_LABEL, synthetic_consumer_fixture=True,
            actual_github_run_observed=False, actual_lean_or_ci_executed=False,
            fixture_identity_is_intentionally_not_a_real_run=True,
        )
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            exit_code = consumer.run()
        (output / "fixture.stdout.log").write_text(stdout.getvalue(), encoding="utf-8")
        receipt = json.loads((output / "CORE_RECEIPT.json").read_text())
        success_payloads = [name for name in ["COMPLETE_TYPES_1005.json", "MODULE_LEDGER_VERIFIED.json",
                                             "ACTUAL_FINAL_BRIDGE.json"] if (output / name).exists()]
        checks = {
            "exit_is_failure_1": exit_code == 1,
            "ci_failure_and_incomplete_evidence_both_retained": receipt["status"] == "FAILED_CI_WITH_INCOMPLETE_EVIDENCE",
            "ci_axis_is_known_failure": receipt["ci_metadata_status"] == "KNOWN_FAILURE_FROM_SUPPLIED_METADATA",
            "evidence_axis_is_incomplete": receipt["evidence_status"] == "INCOMPLETE",
            "observed_failed_run_not_lost": receipt["observed"].get("run_conclusion") == "failure",
            "known_ci_failure_records_present": bool(receipt["known_ci_failures"]),
            "specific_missing_reason_retained": receipt["pending_reason"] == expected_reason,
            "raw_run_metadata_preserved_before_archive": (output / "original-metadata" / "run.json").is_file(),
            "not_mislabeled_as_a_lean_diagnostic": receipt["first_real_lean_diagnostics_preserved"] == 0,
            "not_mislabeled_as_a_consumer_parse_error": "error" not in receipt,
            "no_success_proof_payloads": not success_payloads,
            "not_an_actual_github_run_claim": receipt["synthetic_consumer_fixture"] is True
                and receipt["expected_run_id"] < 0 and receipt["expected_source_commit"] == fixture_module.EXPECTED_SHA,
        }
        result = {"case": name, "fixture_label": FIXTURE_LABEL, "checks": checks,
                  "actual_consumer_exit_code": exit_code, "actual_consumer_status": receipt["status"],
                  "known_metadata_failure_records": len(receipt["known_ci_failures"]),
                  "output": str(output), "pass": all(checks.values())}
        results.append(result)
        dump(CHECK_ROOT / "NEGATIVE_CONTROL_FLOW_CHECK.json", {
            "scope": FIXTURE_LABEL, "status": "RUNNING_NEGATIVE_CONSUMER_CHECKS",
            "production_script_sha256": script_sha256,
            "production_fixed_identity_unchanged": production_identity,
            "actual_core_run_failure_observed": False, "cases": results,
        })
        if not result["pass"]:
            raise RuntimeError("First consumer-only negative case failed: " + name)
    assert not attempted_subprocesses
    assert SCRIPT.read_bytes() == original_bytes
    report = {
        "scope": FIXTURE_LABEL,
        "status": "PASS_NEGATIVE_CONSUMER_CONTROL_FLOW_ONLY",
        "production_script_sha256": script_sha256,
        "production_fixed_identity_unchanged": production_identity,
        "actual_core_run_failure_observed": False,
        "actual_ci_artifact_read": False,
        "lean_ci_network_or_subprocess_executed": False,
        "successful_ci_artifact_or_pass_fixture_created": False,
        "cases": results,
    }
    dump(CHECK_ROOT / "NEGATIVE_CONTROL_FLOW_CHECK.json", report)
    print(json.dumps({"status": report["status"], "scope": FIXTURE_LABEL,
                      "cases": len(results), "checks": sum(len(r["checks"]) for r in results),
                      "script_sha256": script_sha256}, ensure_ascii=False))


if __name__ == "__main__":
    main()
