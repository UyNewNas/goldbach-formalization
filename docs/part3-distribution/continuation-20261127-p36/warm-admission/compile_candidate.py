#!/usr/bin/env python3
"""Strictly compile the separately authored finite warm/Rosser bridge."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    original = Path("/workspace/p36-rounded-correction-20261127")
    warm = json.loads((original / "warm-pins.json").read_text())
    pref = json.loads((original / "PREFLIGHT.json").read_text())
    extra = "ImbalancedChen.P3OriginalU5AllSourceSquares"
    warm["sources"][extra] = {
        "path": "ImbalancedChen/P3OriginalU5AllSourceSquares.lean",
        "sha256": "74532d7b0d2522e969613287888ca636fc2e4e7a188f1b211c71f8dcb414f698",
    }
    warm["warm"]["modules"][extra] = {"objects": {
        "/workspace/p36-original-u5-20261125/.lake/p36-build/lib/lean/ImbalancedChen/P3OriginalU5AllSourceSquares.olean":
        "1fad75b0ecf492ad607ab5cc95c5717250741870bd46cb340ca3113f9129e99c"}}
    warm["additional_accepted_report_sha256"] = \
        "dd61e7c35401d96c0cfbc22831411a3d2bc91f05e8e2918b16b1579711ad0529"
    base = Path(pref["source_base"])
    for module, pin in warm["sources"].items():
        if sha(base / pin["path"]) != pin["sha256"]:
            raise RuntimeError("Changed accepted source: " + module)
    for module, pin in warm["warm"]["modules"].items():
        for name, digest in pin["objects"].items():
            source = Path(name)
            if sha(source) != digest:
                raise RuntimeError("Changed accepted object: " + module)
            suffix = "".join(source.suffixes)
            target = root / "objects" / (module.replace(".", "/") + suffix)
            target.parent.mkdir(parents=True, exist_ok=True)
            if not target.exists():
                target.symlink_to(source)
            if sha(target) != digest:
                raise RuntimeError("Changed live object: " + module)
    pref["lean_path"] = ":".join([str(root / "objects")] + pref["lean_path"].split(":")[1:])
    pref["compile_overlay"] = str(root)
    pref["project_source_count"] = len(warm["sources"])
    pref["object_file_count"] = sum(len(p["objects"]) for p in warm["warm"]["modules"].values())
    (root / "PREFLIGHT.json").write_text(json.dumps(pref, indent=2) + "\n")
    (root / "warm-pins.json").write_text(json.dumps(warm, indent=2) + "\n")
    source = root / "ImbalancedChen/P3OriginalU5WarmRosserAdmission.lean"
    if sha(source) != args.source_sha256:
        raise RuntimeError("Candidate transfer mismatch")
    attempt = root / "attempts" / args.attempt
    attempt.mkdir(parents=True, exist_ok=False)
    (attempt / source.name).write_bytes(source.read_bytes())
    obj = root / "objects/ImbalancedChen/P3OriginalU5WarmRosserAdmission.olean"
    if obj.is_symlink():
        raise RuntimeError("Candidate object must not be a dependency symlink")
    if obj.exists():
        obj.unlink()
    env = os.environ.copy()
    env.update(LEAN_PATH=pref["lean_path"], LEAN_NUM_THREADS="1",
               LEAN_SYSROOT="/workspace/toolchains/lean-4.33.0-rc1-linux")
    lean = Path(pref["compiler"]["path"])
    if sha(lean) != pref["compiler"]["sha256"]:
        raise RuntimeError("Changed compiler")
    command = [str(lean), "-t0", "-j1", "-DwarningAsError=true", "-R", str(root),
               "-o", str(obj), str(source)]
    log = attempt / "compile.log"
    tick = time.monotonic()
    with log.open("w") as stream:
        proc = subprocess.run(command, cwd=root, env=env, stdout=stream,
                              stderr=subprocess.STDOUT, timeout=900)
    if sha(source) != args.source_sha256:
        raise RuntimeError("Source changed during compilation")
    report = {"attempt": args.attempt, "command": command, "exit_code": proc.returncode,
              "source_sha256": sha(source), "object_sha256": sha(obj) if proc.returncode == 0 else None,
              "log_sha256": sha(log), "elapsed_seconds": time.monotonic() - tick,
              "dependency_source_count": len(warm["sources"]), "whole_p36_closed": False}
    (attempt / "compile.json").write_text(json.dumps(report, indent=2) + "\n")
    print("WARM_ADMISSION_COMPILE " + json.dumps(report), flush=True)
    print(log.read_text(), flush=True)
    return proc.returncode


if __name__ == "__main__":
    raise SystemExit(main())
