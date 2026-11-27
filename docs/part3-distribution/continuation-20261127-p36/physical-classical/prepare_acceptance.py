#!/usr/bin/env python3
"""Bind successful strict compiles to exact authored source pins before replay."""
import argparse
import hashlib
import json
from pathlib import Path


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    pins = json.loads((root / "SOURCE_PINS_SEED.json").read_text())
    for module, pin in pins["modules"].items():
        record = json.loads((root / "attempts" / args.attempt / module / "compile.json").read_text())
        if record["exit_code"] != 0 or record["module"] != module or record["attempt"] != args.attempt:
            raise RuntimeError("Strict compilation has not succeeded for this owner and attempt")
        source = root / (module.replace(".", "/") + ".lean")
        obj = root / "objects" / (module.replace(".", "/") + ".olean")
        if sha(source) != pin["source_sha256"] or sha(source) != record["source_sha256"]:
            raise RuntimeError("Successful compile has different source bytes")
        if obj.is_symlink() or sha(obj) != record["object_sha256"]:
            raise RuntimeError("Successful compile has different object bytes")
        pin["object_sha256"] = sha(obj)
    if sha(root / "P36PhysicalClassicalAudit.lean") != pins["audit_sha256"]:
        raise RuntimeError("Different complete defining-module audit")
    (root / "OWNED_SOURCE_PINS.json").write_text(json.dumps(pins, indent=2) + "\n")
    print("PHYSICAL_CLASSICAL_ACCEPTANCE_INPUTS " + json.dumps(pins), flush=True)


if __name__ == "__main__":
    main()
