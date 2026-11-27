#!/usr/bin/env python3
"""Verify the joint rounding against its original job and the accepted P3.6 joint marked archive."""
import argparse
import base64
from datetime import datetime
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tarfile
import uuid

sys.dont_write_bytecode = True


def sha(data):
    return hashlib.sha256(data).hexdigest()


COMPATIBILITY_OWNERS = []
PROOF_OWNERS = [
    "ImbalancedChen.P3OriginalU5JointCellCoefficient",
    "ImbalancedChen.P3OriginalU5JointBetaAttachment",
    "ImbalancedChen.P3OriginalU5PhysicalRawRank",
    "ImbalancedChen.P3OriginalU5JointPrimeWallPayment",
    "ImbalancedChen.P3OriginalU5JointRoughRoundingPayment"
]
MARKED_OVERLAY = Path("/workspace/p36-joint-marked-20261127")


def stdout_bytes(path):
    data = path.read_bytes()
    return gzip.decompress(data) if path.suffix == ".gz" else data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--job-id", required=True)
    parser.add_argument("--attempt", required=True)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--terminal", type=Path, required=True)
    parser.add_argument("--audit-stdout", type=Path, required=True)
    parser.add_argument("--export-terminal", type=Path, required=True)
    parser.add_argument("--export-stdout", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if sys.flags.optimize:
        raise RuntimeError("This verifier requires Python assertion checks enabled")
    if not args.attempt.isascii() or not args.attempt.isdigit():
        parser.error("--attempt must be a numeric attempt directory name")
    local_run = uuid.uuid4().hex
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"status": "RUNNING", "local_verification_id": local_run}) + "\n")
    here = Path(__file__).resolve().parent
    repo = here.parents[3]
    terminal = json.loads(args.terminal.read_text())
    assert terminal["status"] == "succeeded" and terminal["exit_code"] == 0
    assert terminal["task_id"] == args.job_id
    assert terminal["output_truncated"] is False
    original_stdout = stdout_bytes(args.audit_stdout)
    assert len(original_stdout) == terminal["output_bytes"]
    stdout_text = original_stdout.decode()
    decoder = json.JSONDecoder()
    original_reports = []
    offset = 0
    for line in stdout_text.splitlines(keepends=True):
        if line.startswith("{"):
            value, _ = decoder.raw_decode(stdout_text, offset)
            if isinstance(value, dict) and "verification_id" in value and "driver_sha256" in value:
                original_reports.append(value)
        offset += len(line)
    assert len(original_reports) == 1
    export_terminal = json.loads(args.export_terminal.read_text())
    assert export_terminal["task_id"] == args.job_id
    assert export_terminal["status"] == "succeeded" and export_terminal["exit_code"] == 0
    assert export_terminal["output_truncated"] is False
    export_stdout = stdout_bytes(args.export_stdout)
    assert len(export_stdout) == export_terminal["output_bytes"] and export_stdout == original_stdout
    exports = [json.loads(line) for line in export_stdout.decode().splitlines()
               if line.startswith('{"event": "OWNED_EVIDENCE_ARCHIVE"')]
    assert len(exports) == 1
    exported = exports[0]
    archive_bytes = args.archive.read_bytes()
    assert len(archive_bytes) == exported["bytes"] and sha(archive_bytes) == exported["sha256"]
    assert base64.b64decode(exported["base64"], validate=True) == archive_bytes
    with tarfile.open(args.archive, "r:xz") as archive:
        members = archive.getmembers()
        assert all(m.isfile() and not Path(m.name).is_absolute()
                   and ".." not in Path(m.name).parts for m in members)
        assert len({m.name for m in members}) == len(members)
        files = {m.name: archive.extractfile(m).read() for m in members}
    manifest = json.loads(files["EXPORT_MANIFEST.json"])
    assert set(files) == set(manifest) | {"EXPORT_MANIFEST.json"}
    for name, meta in manifest.items():
        assert sha(files[name]) == meta["sha256"] and len(files[name]) == meta["bytes"], name
    for filename in ("SOURCE_PINS_SEED.json", "EXPECTED_PREVIOUS_SOURCES.json", "export_owned.py",
                     "compile_candidate.py", "prepare_acceptance.py", "verify_owned.py",
                     "P36JointRoundingAudit.lean"):
        assert files[filename] == (here / filename).read_bytes(), filename
    pins = json.loads(files["SOURCE_PINS_SEED.json"])
    owners = list(pins["modules"])
    assert owners == COMPATIBILITY_OWNERS + PROOF_OWNERS
    compile_prefix = "JOINT_ROUNDING_COMPILE "
    compile_records = [json.loads(line[len(compile_prefix):]) for line in stdout_text.splitlines()
                       if line.startswith(compile_prefix)]
    assert [record["module"] for record in compile_records] == owners
    preflight = json.loads(files["PREFLIGHT.json"])
    overlay = Path(preflight["compile_overlay"])
    for record in compile_records:
        module = record["module"]
        pin = pins["modules"][module]
        assert set(pin) == {"source_sha256"}
        stem = module.replace(".", "/")
        prefix = f"attempts/{args.attempt}/{module}/"
        assert record == json.loads(files[prefix + "compile.json"])
        assert record["attempt"] == args.attempt and record["exit_code"] == 0
        assert record["whole_p36_closed"] is False
        assert record["source_sha256"] == pin["source_sha256"]
        assert sha(files[prefix + "compile.log"]) == record["log_sha256"]
        assert files[prefix + Path(stem).name + ".lean"] == files[stem + ".lean"]
        expected_command = [preflight["compiler"]["path"], "-t0", "-j1", "-DwarningAsError=true",
                            "-R", str(overlay), "-o", str(overlay / "objects" / (stem + ".olean")),
                            str(overlay / (stem + ".lean"))]
        assert record["command"] == expected_command
        pin["object_sha256"] = record["object_sha256"]
    assert json.loads(files["OWNED_SOURCE_PINS.json"]) == pins
    report = json.loads(files["acceptance/report.json"])
    assert report == original_reports[0]
    assert report["verification_id"] == exported["verification_id"]
    assert report["status"] == "VERIFIED_OWNED" and report["verification_id"]
    assert report["whole_p36_closed"] is False
    assert report["source_and_object_pins"] == pins["modules"]
    assert report["modules"] == list(pins["modules"])
    assert terminal["started_at"] - 1 <= datetime.fromisoformat(report["started_utc"]).timestamp()
    assert datetime.fromisoformat(report["finished_utc"]).timestamp() <= terminal["finished_at"] + 1
    assert sha(files["verify_owned.py"]) == sha((here / "verify_owned.py").read_bytes()) == report["driver_sha256"]
    assert sha(files["P36JointRoundingAudit.lean"]) == pins["audit_sha256"] == report["audit_sha256"]
    assert report["kernel_checker_sha256"] == pins["checker_sha256"]
    warm = json.loads(files["warm-pins.json"])
    marked = here.parent / "joint-marked"
    accepted = marked / "accepted"
    prior_receipt = json.loads((accepted / "LOCAL_VERIFICATION.json").read_bytes())
    prior_report_bytes = (accepted / "report.json").read_bytes()
    prior_report = json.loads(prior_report_bytes)
    prior_terminal = json.loads((accepted / "ORIGINAL_TERMINAL.json").read_bytes())
    assert prior_receipt["status"] == "COMPLETE_ARCHIVE_RETRIEVED_AND_LOCALLY_VERIFIED"
    assert prior_receipt["whole_p36_closed"] is prior_report["whole_p36_closed"] is False
    assert prior_receipt["validator_sha256"] == sha((marked / "verify_export_locally.py").read_bytes())
    assert prior_terminal["task_id"] == prior_receipt["audit_task_id"]
    assert prior_terminal["status"] == "succeeded" and prior_terminal["exit_code"] == prior_receipt["audit_exit_code"] == 0
    assert prior_terminal["output_truncated"] is False
    prior_stdout = stdout_bytes(accepted / "ORIGINAL_STDOUT.log.gz")
    assert len(prior_stdout) == prior_terminal["output_bytes"]
    assert sha(prior_stdout) == prior_receipt["original_audit_stdout_sha256"]
    assert prior_report["status"] == "VERIFIED_OWNED" and prior_report["verification_id"] == prior_receipt["verification_id"]
    prior_report_hash = sha(prior_report_bytes)
    assert prior_receipt["report_sha256"] == warm["joint_marked_report_sha256"] == prior_report_hash
    assert report["joint_marked_dependency_report_sha256"] == prior_report_hash
    prior_archive = accepted / "evidence.tar.xz"
    assert prior_archive.stat().st_size == prior_receipt["archive_bytes"]
    assert sha(prior_archive.read_bytes()) == prior_receipt["archive_sha256"]
    with tarfile.open(prior_archive, "r:xz") as archive:
        assert archive.extractfile("acceptance/report.json").read() == prior_report_bytes
        prior_pins = json.load(archive.extractfile("OWNED_SOURCE_PINS.json"))["modules"]
        expected_warm = json.load(archive.extractfile("warm-pins.json"))
        prior_preflight = json.load(archive.extractfile("PREFLIGHT.json"))
    assert prior_pins == prior_report["source_and_object_pins"] == prior_receipt["source_and_object_pins"]
    expected_prior_sources = json.loads(files["EXPECTED_PREVIOUS_SOURCES.json"])["modules"]
    assert len(expected_warm["sources"]) == len(expected_warm["warm"]["modules"]) == 333
    assert len(expected_prior_sources) == len(prior_pins) == 2
    assert list(expected_prior_sources) == prior_report["modules"] == list(prior_pins)
    for module, pin in prior_pins.items():
        assert expected_prior_sources[module] == {"source_sha256": pin["source_sha256"]}
        assert module not in expected_warm["sources"] and module not in expected_warm["warm"]["modules"]
        stem = module.replace(".", "/")
        expected_warm["sources"][module] = {
            "path": str(MARKED_OVERLAY / (stem + ".lean")), "sha256": pin["source_sha256"]}
        expected_warm["warm"]["modules"][module] = {"objects": {
            str(MARKED_OVERLAY / "objects" / (stem + ".olean")): pin["object_sha256"]}}
    expected_warm["joint_marked_report_sha256"] = prior_report_hash
    assert report["physical_classical_dependency_report_sha256"] == expected_warm["physical_classical_report_sha256"]
    assert report["three_frontier_dependency_report_sha256"] == expected_warm["three_frontier_report_sha256"]
    assert report["residual_payment_dependency_report_sha256"] == expected_warm["residual_payment_report_sha256"]
    assert report["historical_dependency_reports"] == expected_warm["historical_reports"]
    assert warm == expected_warm
    assert set(warm["sources"]) == set(warm["warm"]["modules"])
    assert len(warm["sources"]) == 335 and not (set(owners) & set(warm["sources"]))
    assert all(record["dependency_source_count"] == 335 for record in compile_records)
    assert preflight["project_source_count"] == preflight["object_file_count"] == 335
    assert report["additional_accepted_dependency_report_sha256"] == warm["additional_accepted_report_sha256"]
    assert report["warm_admission_dependency_report_sha256"] == warm["warm_admission_report_sha256"]
    expected_preflight = dict(prior_preflight, compile_overlay=str(overlay),
                              project_source_count=335, object_file_count=335)
    expected_preflight["lean_path"] = ":".join(
        [str(overlay / "objects")] + prior_preflight["lean_path"].split(":")[1:])
    assert preflight == expected_preflight
    assert report["lean_path"] == preflight["lean_path"]
    assert preflight["compiler"] == report["compiler"]
    assert report["accepted_dependency_report_sha256"] == warm["warm"]["accepted_report_sha256"]
    assert report["compiler"] == warm["warm"]["compiler"]
    for module, pin in warm["sources"].items():
        relative = module.replace(".", "/") + ".lean"
        assert sha((repo / relative).read_bytes()) == pin["sha256"]
    for name, digest in pins["validation_source_sha256"].items():
        assert sha((repo / name).read_bytes()) == digest
    for module, pin in pins["modules"].items():
        stem = module.replace(".", "/")
        assert sha(files[stem + ".lean"]) == pin["source_sha256"] == sha((repo / (stem + ".lean")).read_bytes())
        assert sha(files["objects/" + stem + ".olean"]) == pin["object_sha256"]
    expected = ["replay-" + m for m in pins["modules"]] + ["owned-inventory-audit"]
    assert [s["name"] for s in report["stages"]] == expected
    for stage in report["stages"]:
        assert stage["exit_code"] == 0
        body = files["acceptance/" + stage["log"]]
        assert sha(body) == stage["log_sha256"]
        if stage["name"].startswith("replay-"):
            module = stage["name"][len("replay-"):]
            checker = Path(preflight["compiler"]["path"]).with_name("leanchecker")
            assert stage["command"] == [str(checker), "--verbose", module]
            assert [s for s in body.decode().splitlines() if s.startswith("replaying ")] == ["replaying " + module]
        else:
            assert stage["command"] == [preflight["compiler"]["path"], "-t0", "-j1",
                                        "-DwarningAsError=true", "-R", str(overlay),
                                        str(overlay / "P36JointRoundingAudit.lean")]
    sys.path.insert(0, str(repo / "verification"))
    import verify_part3_continuation as helper
    assert files["P36JointRoundingAudit.lean"].decode() == helper.render_audit(tuple(pins["modules"]))
    declarations, counts = helper.baseline.validate_inventory(
        files["acceptance/owned-inventory-audit.log"].decode(), modules=tuple(pins["modules"]))
    assert declarations == json.loads(files["acceptance/declarations.json"])
    assert report["observed_transitive_axioms"] == sorted({a for d in declarations for a in d["axioms"]})
    assert len(declarations) == report["declaration_count"] and counts == report["module_counts"]
    for module in pins["modules"]:
        code = files[module.replace(".", "/") + ".lean"].decode()
        assert not helper.baseline.FORBIDDEN.search(helper.baseline.lean_code(code))
    result = {
        "status": "COMPLETE_ARCHIVE_RETRIEVED_AND_LOCALLY_VERIFIED",
        "local_verification_id": local_run,
        "whole_p36_closed": False, "verification_id": report["verification_id"],
        "audit_task_id": terminal["task_id"], "audit_exit_code": terminal["exit_code"],
        "original_audit_stdout_sha256": sha(original_stdout),
        "original_export_stdout_sha256": sha(export_stdout),
        "export_task_id": export_terminal["task_id"],
        "compile_attempt": args.attempt,
        "compile_log_sha256": {record["module"]: record["log_sha256"] for record in compile_records},
        "accepted_dependency_report_sha256": report["accepted_dependency_report_sha256"],
        "additional_accepted_dependency_report_sha256": report["additional_accepted_dependency_report_sha256"],
        "warm_admission_dependency_report_sha256": report["warm_admission_dependency_report_sha256"],
        "three_frontier_dependency_report_sha256": report["three_frontier_dependency_report_sha256"],
        "residual_payment_dependency_report_sha256": report["residual_payment_dependency_report_sha256"],
        "physical_classical_dependency_report_sha256": report["physical_classical_dependency_report_sha256"],
        "joint_marked_dependency_report_sha256": prior_report_hash,
        "historical_dependency_reports": report["historical_dependency_reports"],
        "joint_marked_dependency_task_id": prior_receipt["audit_task_id"],
        "archive_sha256": sha(args.archive.read_bytes()), "archive_bytes": args.archive.stat().st_size,
        "report_sha256": sha(files["acceptance/report.json"]),
        "declaration_count": len(declarations), "module_counts": counts,
        "compatibility_owners": COMPATIBILITY_OWNERS, "proof_owners": PROOF_OWNERS,
        "observed_transitive_axioms": report["observed_transitive_axioms"],
        "source_and_object_pins": pins["modules"],
        "validator_sha256": sha(Path(__file__).read_bytes()),
    }
    for name in ["report.json", "declarations.json", "owned-inventory-audit.log"]:
        (args.output.parent / name).write_bytes(files["acceptance/" + name])
    pending = args.output.with_name(args.output.name + ".tmp")
    pending.write_text(json.dumps(result, indent=2) + "\n")
    pending.replace(args.output)
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
