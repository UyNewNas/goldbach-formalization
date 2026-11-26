#!/usr/bin/env bash
set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PY'
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

root = Path.cwd()
pin = "909214bbfb5ca9caa74fcc1b6f95b469bf43e125"
fingerprint_expected = "c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
registry_expected = "0858a9bea92e7c436382ae96fcd63dc709b73f5b346d93e6980c0389d7718e5a"
manifest_expected = "43b5f8366283883a81766b6ccb16f9f2c12dc70d59f54bc5f26b9a18e42428c1"
summary_name = "p24-owned-symbolic-001-r01.json"
snapshot_path = Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
expected = {
    "verification/part2/run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "verification/part2/run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "verification/part2/winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    "verification/part2/export_winner9_private_evidence.py": "fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645",
}

def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()

def check_source():
    assert subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip() == pin
    assert not subprocess.check_output(["git", "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    for relative, wanted in expected.items():
        assert digest(root / relative) == wanted, relative

check_source()
assert os.statvfs(root).f_bavail * os.statvfs(root).f_frsize >= 256 * 1024 * 1024
sys.path.insert(0, str(root / "verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, PIN, project_nodes
from winner9_external_snapshot import ExternalSnapshot

roots = [
    "ImbalancedChen.P2OriginalCompactQ80CompleteSoundness",
    "ImbalancedChen.P2OriginalCompactCachedRun",
    "ImbalancedChen.P2OriginalCompactQ80FixedBindings",
    "ImbalancedChen.P4AOrdinaryRootFirstIntegral",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve",
]
full = list(project_nodes(root, "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"))
assert len(full) == 324 and len(set(full)) == 324
fingerprint = hashlib.sha256(("\n".join(full) + "\n").encode()).hexdigest()
assert fingerprint == fingerprint_expected
symbolic = set()
for name in roots:
    symbolic.update(project_nodes(root, name))
assert len(symbolic) == 321
assert set(full) - symbolic == {
    "ImbalancedChen.P2OriginalCompactArchivedTotalCandidate",
    "ImbalancedChen.P2OriginalCompactCachedEndpointCandidate",
    "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint",
}

manifest_path = root / ".lake/p24-audit-export/symbolic-preflight-001/manifest.json"
assert digest(manifest_path) == manifest_expected
manifest = json.loads(manifest_path.read_text())
selected = set(manifest["accepted_modules"])
unselected = set(manifest["unselected_modules"])
assert selected.isdisjoint(unselected) and selected | unselected == set(full)
assert not selected and len(unselected) == 324
assert manifest["duplicate_owned_declarations"] == {}
assert manifest["full_p2_complete"] is False
assert manifest["records_snapshot_sha256"] == registry_expected
eligible = [name for name in full if name in symbolic and name in unselected]
assert len(eligible) == 321
prior_path = root / ".lake/p2-private/audit/p24-owned-symbolic-000-r01.json"
assert digest(prior_path) == "bc84531d893051e4eae4a7ee90b0daa7c2172e83f48015ce548cb49f1c097598"
prior = json.loads(prior_path.read_text())
assert prior["all_accepted"] is True and prior["accepted"] == prior["requested"] == 10
assert set(prior["modules"]) == set(eligible[:10])
assert all(row["accepted"] is True for row in prior["modules"].values())
targets = eligible[10:50]
assert not set(targets).intersection(prior["modules"])
assert targets == [
    "ImbalancedChen.VariableEnvelopeRegularity",
    "ImbalancedChen.VariableEnvelopeBoxes",
    "ImbalancedChen.VariableEnvelopeScaled",
    "ImbalancedChen.VariableEnvelopeCertificates",
    "ImbalancedChen.BufferedFirstCubeGeometry",
    "ImbalancedChen.VariableEnvelopeTailFloor",
    "ImbalancedChen.ActualThirdPrefixTailIntegralCore",
    "ImbalancedChen.ActualExtendedThirdIdealCap",
    "ImbalancedChen.ActualExtendedThirdOrderedIntegral",
    "ImbalancedChen.ActualExtendedThirdLowerFactorRegularity",
    "ImbalancedChen.ActualThirdOriginalCoupledRecurrence",
    "ImbalancedChen.ActualThirdOriginalLocalCurvature",
    "ImbalancedChen.P2ContinuousSieveRational",
    "ImbalancedChen.ActualThirdOriginalSharpChord",
    "ImbalancedChen.ActualThirdOriginalWeights",
    "ImbalancedChen.ActualThirdOriginalWeightedCurvature",
    "ImbalancedChen.ActualThirdOriginalLiteralNodes",
    "ImbalancedChen.P2HistoricSieveTableSemantics",
    "ImbalancedChen.P2HistoricSieveTrapezoidError",
    "ImbalancedChen.ActualThirdOriginalRationalQuery",
    "ImbalancedChen.P2HistoricSieveStateInduction",
    "ImbalancedChen.P2OriginalCompactQ80Table",
    "ImbalancedChen.P2HistoricLogRangeReduction",
    "ImbalancedChen.P2HistoricLogPointInterpreter",
    "ImbalancedChen.P2HistoricI80DivisionSoundness",
    "ImbalancedChen.SymmetricTriangleIntegral",
    "ImbalancedChen.AffinePrimeGates",
    "ImbalancedChen.ActualExtendedThirdClosedIntegral",
    "ImbalancedChen.ActualExtendedThirdPhysicalCell",
    "ImbalancedChen.ActualExtendedThirdDyadicCoverage",
    "ImbalancedChen.ActualExtendedThirdGammaApproximation",
    "ImbalancedChen.ActualExtendedThirdFinitePhysicalKernel",
    "ImbalancedChen.ActualExtendedThirdStripIntegral",
    "ImbalancedChen.ActualExtendedThirdCompactKernelApproximation",
    "ImbalancedChen.Part4ActualThirdTailBound",
    "ImbalancedChen.ActualExtendedThirdFiniteTailIntegral",
    "ImbalancedChen.ActualExtendedThirdBoundaryLoss",
    "ImbalancedChen.ActualExtendedThirdKernelL1Convergence",
    "ImbalancedChen.ActualExtendedThirdFunctionalConvergence",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve"
]

registry = root / ".lake/p2-private/records.json"
assert digest(registry) == registry_expected
records = json.loads(registry.read_text())
assert all(records[name].get("exit_code") == 0 for name in symbolic)
summary_path = root / ".lake/p2-private/audit" / summary_name
assert not summary_path.exists(), "Preserve the existing batch summary; choose a new retry name"
assert digest(Path(LEAN)) == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
external = ExternalSnapshot(snapshot_path, lean=LEAN, mathlib_pin=PIN,
                            project_lib=root / ".lake/p2-private/lib")
native_before = external.verify()
registered_native = [records[name]["external_snapshot"] for name in symbolic
                     if "external_snapshot" in records[name]]
assert registered_native and all(binding == native_before for binding in registered_native)
assert Path(external.value["runtime"]["leanchecker"]).resolve() == Path(LEANCHECKER).resolve()
checker_before = digest(Path(LEANCHECKER))
assert checker_before == external.files[external.value["runtime"]["leanchecker"]]["sha256"]
helper = root / "verification/part2/winner9_external_snapshot.py"
assert digest(helper) == native_before["verification_helper_sha256"]
env = external.environment(dict(os.environ))
command = [sys.executable, "-B", "verification/part2/run_winner9_private_audit.py",
           *targets, "--external-snapshot", str(snapshot_path),
           "--memory-mb", "11264", "--summary-name", summary_name]
print(json.dumps({
    "phase": "owned_symbolic_batch_start", "source_pin": pin,
    "full_scope": 324, "symbolic_scope": 321, "ordered_fingerprint": fingerprint,
    "preflight_manifest": str(manifest_path), "preflight_manifest_sha256": manifest_expected,
    "preflight_selected_count": 0, "accepted_prior_batch_count": 10,
    "eligible_missing_symbolic_before": len(eligible) - 10,
    "batch_modules": targets, "batch_requested": len(targets),
    "summary": str(summary_path), "command": command,
    "registry_sha256_before": registry_expected,
    "native_snapshot_sha256": native_before["snapshot_sha256"],
    "native_context_signature": native_before["context_signature"],
    "leanchecker_sha256_before": checker_before,
    "finite_A_credit": False, "finite_B_credit": False,
    "whole_functional_credit": False, "full_scope_audit_complete": False,
    "full_p2_complete": False,
}), flush=True)
started = time.monotonic()
result = subprocess.run(command, cwd=root, env=env)
elapsed = time.monotonic() - started

# Run normal batch postchecks even if the unchanged runner reports a failed audit.
check_source()
assert digest(registry) == registry_expected, "The compile registry changed during an audit-only batch"
assert digest(manifest_path) == manifest_expected
native_after = external.verify()
assert native_after == native_before
assert digest(Path(LEANCHECKER)) == checker_before
assert digest(helper) == native_before["verification_helper_sha256"]
summary = json.loads(summary_path.read_text())
assert set(summary["modules"]) == set(targets)
assert summary["requested"] == len(targets)
assert summary["accepted"] == sum(row["accepted"] is True for row in summary["modules"].values())
assert summary["all_accepted"] == all(row["accepted"] is True for row in summary["modules"].values())
assert result.returncode == int(not summary["all_accepted"])
print(json.dumps({
    "phase": "owned_symbolic_batch_complete", "source_pin": pin,
    "full_scope": 324, "symbolic_scope": 321, "ordered_fingerprint": fingerprint,
    "runner_exit_code": result.returncode, "runner_elapsed_seconds": elapsed,
    "summary": str(summary_path), "summary_sha256": digest(summary_path),
    "batch_summary": summary, "batch_postcheck_passed": True,
    "registry_sha256_before": registry_expected, "registry_sha256_after": digest(registry),
    "native_binding_equal": native_before == native_after,
    "leanchecker_sha256_before": checker_before,
    "leanchecker_sha256_after": digest(Path(LEANCHECKER)),
    "finite_A_credit": False, "finite_B_credit": False,
    "whole_functional_credit": False, "full_scope_audit_complete": False,
    "full_p2_complete": False,
}), flush=True)
raise SystemExit(result.returncode)
PY

