#!/usr/bin/env python3
"""Export the accepted owners and receipts without copying old dependencies.

The caller must independently require the original audit job's terminal
success. This exporter checks the report, stage logs and pinned input bytes;
its output is a lossless xz archive encoded in one JSON stdout record.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import io
import json
from pathlib import Path
import tarfile


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--driver-sha256", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    pins = json.loads((root / "OWNED_SOURCE_PINS.json").read_text())
    report = json.loads((root / "acceptance/report.json").read_text())
    if report["status"] != "VERIFIED_OWNED" or not report.get("verification_id"):
        raise RuntimeError("No fresh completed verification report")
    if report["driver_sha256"] != args.driver_sha256:
        raise RuntimeError("Report belongs to a different driver")
    if report["source_and_object_pins"] != pins["modules"]:
        raise RuntimeError("Report and owner pins disagree")
    if report["whole_p36_closed"] is not False:
        raise RuntimeError("Unexpected whole-node closure claim")
    files: dict[str, bytes] = {}

    def add(relative: str, digest: str | None = None) -> None:
        data = (root / relative).read_bytes()
        if digest is not None and sha(data) != digest:
            raise RuntimeError("Changed export input: " + relative)
        files[relative] = data

    for module, pin in pins["modules"].items():
        stem = module.replace(".", "/")
        add(stem + ".lean", pin["source_sha256"])
        add("objects/" + stem + ".olean", pin["object_sha256"])
    add("verify_owned.py", args.driver_sha256)
    add("OWNED_SOURCE_PINS.json")
    add("P36JointMarkedAudit.lean", pins["audit_sha256"])
    for relative in ["PREFLIGHT.json", "warm-pins.json", "EXPECTED_PREVIOUS_SOURCES.json", "export_owned.py",
                     "SOURCE_PINS_SEED.json", "compile_candidate.py", "prepare_acceptance.py",
                     "acceptance/report.json", "acceptance/declarations.json"]:
        add(relative)
    for file in sorted((root / "attempts").rglob("*")):
        if file.is_file():
            add(str(file.relative_to(root)))
    for stage in report["stages"]:
        if stage["exit_code"] != 0 or Path(stage["log"]).name != stage["log"]:
            raise RuntimeError("Invalid stage record")
        add("acceptance/" + stage["log"], stage["log_sha256"])
    # Preserve the deliberately abandoned initial verification as history.
    prior = root / "acceptance-attempt-001-cancelled"
    if prior.exists():
        for file in sorted(prior.iterdir()):
            if file.is_file():
                add(str(file.relative_to(root)))
    manifest = {name: {"bytes": len(data), "sha256": sha(data)}
                for name, data in sorted(files.items())}
    files["EXPORT_MANIFEST.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
    stream = io.BytesIO()
    with tarfile.open(fileobj=stream, mode="w:xz") as archive:
        for name, data in sorted(files.items()):
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mode = 0o644
            archive.addfile(info, io.BytesIO(data))
    for name, data in files.items():
        if name != "EXPORT_MANIFEST.json" and (root / name).read_bytes() != data:
            raise RuntimeError("Input changed during export: " + name)
    payload = stream.getvalue()
    print(json.dumps({"event": "OWNED_EVIDENCE_ARCHIVE", "bytes": len(payload),
                      "sha256": sha(payload), "verification_id": report["verification_id"],
                      "base64": base64.b64encode(payload).decode()}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
