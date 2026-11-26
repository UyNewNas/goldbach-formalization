#!/usr/bin/env python3
"""Export exact completed geometry01 artifacts without rerunning Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import tarfile


def fingerprint(p):
    return {"bytes": p.stat().st_size, "sha256": hashlib.sha256(p.read_bytes()).hexdigest()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--stage", type=Path, required=True)
    args = ap.parse_args()
    root = args.stage.resolve()
    successes = sorted((root / "verification").glob("*/SUCCESS.json"))
    assert len(successes) == 1, successes
    result = json.loads(successes[0].read_text())
    assert result["status"] == "succeeded" and result["accepted_targets"] == 33
    verifier = json.loads((root / "tools/p26/Geometry01Decoding_VERIFIER.json").read_text())
    files = set(successes[0].parent.rglob("*"))
    files |= set((root / "tools/p26").rglob("*"))
    files |= set((root / "verifier-history").rglob("*"))
    files |= {root / "Geometry01Decoding_SUPPLIERS.json", root / "Geometry01Decoding_CONTINUATION.json"}
    for item in verifier["targets"]:
        suffix = item["module"].replace(".", "/")
        files.add(root / "project" / (suffix + ".lean"))
        files.add(root / "objects" / (suffix + ".olean"))
    files = sorted(p for p in files if p.is_file())
    records = []
    owned_count = 0
    peak = 0
    duration = 0
    for p in files:
        records.append({"path": str(p.relative_to(root)), **fingerprint(p)})
        if p.name.endswith("-result.json"):
            d = json.loads(p.read_text())
            assert d["status"] == "succeeded" and d["exit_code"] == 0
            peak = max(peak, d["peak_rss_bytes"])
            duration += d["elapsed_seconds"]
            owned_count += d.get("owned_declaration_count", 0)
    manifest = root / "ACCEPTED_EXPORT_MANIFEST.json"
    report = {"schema": "p26_geometry01_completed_export_v1", "status": "succeeded",
              "targets": 33, "normal": 32, "kernel": 33, "owned_audit": 33,
              "owned_declarations": owned_count, "peak_rss_bytes": peak,
              "summed_step_seconds": duration, "files": records}
    manifest.write_text(json.dumps(report, indent=2) + "\n")
    destination = root.parent / "geometry01-completed-evidence.tar.xz"
    assert not destination.exists(), "Refusing to overwrite a prior export"
    with tarfile.open(destination, "w:xz") as tf:
        for p in files + [manifest]:
            tf.add(p, arcname=str(p.relative_to(root)), recursive=False)
    print(json.dumps({"path": str(destination), **fingerprint(destination),
                      "targets": 33, "normal": 32, "kernel": 33, "owned": 33,
                      "owned_declarations": owned_count, "peak_rss_bytes": peak,
                      "summed_step_seconds": duration}), flush=True)


if __name__ == "__main__":
    main()
