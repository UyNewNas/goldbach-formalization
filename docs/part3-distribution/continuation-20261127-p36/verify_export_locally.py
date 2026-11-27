#!/usr/bin/env python3
"""Check transported evidence against local sources and the original terminal."""
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, required=True)
    parser.add_argument("--terminal", type=Path, required=True)
    parser.add_argument("--audit-stdout", type=Path, required=True)
    parser.add_argument("--export-terminal", type=Path, required=True)
    parser.add_argument("--export-stdout", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if sys.flags.optimize:
        raise RuntimeError("This verifier requires Python assertion checks enabled")
    local_run = uuid.uuid4().hex
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"status": "RUNNING", "local_verification_id": local_run}) + "\n")
    here = Path(__file__).resolve().parent
    repo = here.parents[2]
    terminal = json.loads(args.terminal.read_text())
    assert terminal["status"] == "succeeded" and terminal["exit_code"] == 0
    assert terminal["task_id"] == "job_5f9c0d1eb4cc49348095b29f16fcd481"
    assert terminal["output_truncated"] is False
    original_stdout = args.audit_stdout.read_bytes()
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
    assert export_terminal["task_id"] == "job_e35dfe4561d14f04b908f7f3706d2030"
    assert export_terminal["output_truncated"] is False
    if args.export_stdout.suffix == ".gz":
        export_stdout = gzip.decompress(args.export_stdout.read_bytes())
    else:
        export_stdout = args.export_stdout.read_bytes()
    assert len(export_stdout) == export_terminal["output_bytes"]
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
    pins = json.loads((here / "OWNED_SOURCE_PINS.json").read_text())
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
    assert sha(files["P36RoundedCorrectionAudit.lean"]) == pins["audit_sha256"] == report["audit_sha256"]
    assert report["kernel_checker_sha256"] == pins["checker_sha256"]
    warm = json.loads(files["warm-pins.json"])
    assert warm["warm"] == json.loads((here / "WARM_OBJECT_PINS.json").read_text())
    assert warm["sources"] == json.loads((here / "DEPENDENCY_SOURCE_PINS.json").read_text())["sources"]
    assert report["accepted_dependency_report_sha256"] == warm["warm"]["accepted_report_sha256"]
    assert report["compiler"] == warm["warm"]["compiler"]
    for pin in warm["sources"].values():
        assert sha((repo / pin["path"]).read_bytes()) == pin["sha256"]
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
            assert [s for s in body.decode().splitlines() if s.startswith("replaying ")] == ["replaying " + module]
    sys.path.insert(0, str(repo / "verification"))
    import verify_part3_continuation as helper
    assert files["P36RoundedCorrectionAudit.lean"].decode() == helper.render_audit(tuple(pins["modules"]))
    declarations, counts = helper.baseline.validate_inventory(
        files["acceptance/owned-inventory-audit.log"].decode(), modules=tuple(pins["modules"]))
    assert declarations == json.loads(files["acceptance/declarations.json"])
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
        "archive_sha256": sha(args.archive.read_bytes()), "archive_bytes": args.archive.stat().st_size,
        "report_sha256": sha(files["acceptance/report.json"]),
        "declaration_count": len(declarations), "module_counts": counts,
        "observed_transitive_axioms": report["observed_transitive_axioms"],
        "source_and_object_pins": pins["modules"],
        "validator_sha256": sha(Path(__file__).read_bytes()),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")
    for name in ["report.json", "declarations.json", "owned-inventory-audit.log"]:
        (args.output.parent / name).write_bytes(files["acceptance/" + name])
    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
