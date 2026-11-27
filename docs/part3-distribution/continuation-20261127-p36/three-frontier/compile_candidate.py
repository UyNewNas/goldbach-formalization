#!/usr/bin/env python3
"""Strictly compile new U5 frontier owners against accepted dependency bytes."""
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
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    previous = Path("/workspace/p36-warm-bridge-20261127")
    warm = json.loads((previous / "warm-pins.json").read_text())
    pref = json.loads((previous / "PREFLIGHT.json").read_text())
    additions = json.loads((root / "DEPENDENCY_ADDITIONS.json").read_text())
    for module, item in additions["modules"].items():
        if module in warm["sources"] or module in warm["warm"]["modules"]:
            raise RuntimeError("Repeated dependency addition: " + module)
        warm["sources"][module] = item["source"]
        warm["warm"]["modules"][module] = {"objects": item["objects"]}
    warm["warm_admission_report_sha256"] = additions["warm_admission_report_sha256"]
    base = Path(pref["source_base"])

    def check_dependencies():
        for module, pin in warm["sources"].items():
            if sha(base / pin["path"]) != pin["sha256"]:
                raise RuntimeError("Changed accepted source: " + module)
        for module, pin in warm["warm"]["modules"].items():
            for name, digest in pin["objects"].items():
                source = Path(name)
                if sha(source) != digest:
                    raise RuntimeError("Changed accepted object: " + module)
                suffix = "".join(source.suffixes)
                if suffix not in (".olean", ".olean.private", ".olean.server"):
                    raise RuntimeError("Unexpected dependency object suffix")
                target = root / "objects" / (module.replace(".", "/") + suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                if not target.exists():
                    target.symlink_to(source)
                if sha(target) != digest:
                    raise RuntimeError("Changed live dependency object: " + module)

    check_dependencies()
    pref["lean_path"] = ":".join([str(root / "objects")] + pref["lean_path"].split(":")[1:])
    pref["compile_overlay"] = str(root)
    pref["project_source_count"] = len(warm["sources"])
    pref["object_file_count"] = sum(len(p["objects"]) for p in warm["warm"]["modules"].values())
    (root / "PREFLIGHT.json").write_text(json.dumps(pref, indent=2) + "\n")
    (root / "warm-pins.json").write_text(json.dumps(warm, indent=2) + "\n")
    seeds = json.loads((root / "SOURCE_PINS_SEED.json").read_text())
    attempt = root / "attempts" / args.attempt
    attempt.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env.update(LEAN_PATH=pref["lean_path"], LEAN_NUM_THREADS="1",
               LEAN_SYSROOT="/workspace/toolchains/lean-4.33.0-rc1-linux")
    lean = Path(pref["compiler"]["path"])
    if sha(lean) != pref["compiler"]["sha256"]:
        raise RuntimeError("Changed compiler")
    for module, pin in seeds["modules"].items():
        source = root / (module.replace(".", "/") + ".lean")
        if sha(source) != pin["source_sha256"]:
            raise RuntimeError("Candidate transfer mismatch: " + module)
        module_attempt = attempt / module
        module_attempt.mkdir()
        (module_attempt / source.name).write_bytes(source.read_bytes())
        obj = root / "objects" / (module.replace(".", "/") + ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        if obj.is_symlink():
            raise RuntimeError("Candidate object must not be a dependency symlink")
        if obj.exists():
            obj.unlink()
        command = [str(lean), "-t0", "-j1", "-DwarningAsError=true", "-R", str(root),
                   "-o", str(obj), str(source)]
        log = module_attempt / "compile.log"
        tick = time.monotonic()
        with log.open("w") as stream:
            proc = subprocess.run(command, cwd=root, env=env, stdout=stream,
                                  stderr=subprocess.STDOUT, timeout=900)
        if sha(source) != pin["source_sha256"]:
            raise RuntimeError("Source changed during compilation")
        check_dependencies()
        record = {"attempt": args.attempt, "module": module, "command": command,
                  "exit_code": proc.returncode, "source_sha256": sha(source),
                  "object_sha256": sha(obj) if proc.returncode == 0 else None,
                  "log_sha256": sha(log), "elapsed_seconds": time.monotonic() - tick,
                  "dependency_source_count": len(warm["sources"]), "whole_p36_closed": False}
        (module_attempt / "compile.json").write_text(json.dumps(record, indent=2) + "\n")
        print("THREE_FRONTIER_COMPILE " + json.dumps(record), flush=True)
        print(log.read_text(), flush=True)
        if proc.returncode:
            return proc.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
