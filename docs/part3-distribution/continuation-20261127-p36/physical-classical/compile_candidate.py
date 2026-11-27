#!/usr/bin/env python3
"""Strictly compile the physical classical candidates against the accepted P3.6 residual and historical pools."""
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
    previous = Path("/workspace/p36-residual-payment-20261127")
    if root == previous or previous in root.parents or root in previous.parents:
        raise RuntimeError("Physical classical candidates need an isolated overlay")
    warm = json.loads((previous / "warm-pins.json").read_text())
    pref = json.loads((previous / "PREFLIGHT.json").read_text())
    previous_pins = json.loads((previous / "OWNED_SOURCE_PINS.json").read_text())
    report_path = previous / "acceptance/report.json"
    report_hash = sha(report_path)
    report = json.loads(report_path.read_text())
    expected = json.loads((root / "EXPECTED_PREVIOUS_SOURCES.json").read_text())["modules"]
    if (len(warm["sources"]) != 315 or set(warm["sources"]) != set(warm["warm"]["modules"])
            or len(expected) != 8 or set(previous_pins["modules"]) != set(expected)):
        raise RuntimeError("Unexpected previous P3.6 dependency/owner scope")
    if (report["status"] != "VERIFIED_OWNED" or report["whole_p36_closed"] is not False
            or not report["verification_id"] or report["modules"] != list(expected)
            or report["source_and_object_pins"] != previous_pins["modules"]
            or report["compiler"] != pref["compiler"]):
        raise RuntimeError("The previous P3.6 group has no matching completed audit")
    for module, item in previous_pins["modules"].items():
        if module in warm["sources"] or module in warm["warm"]["modules"]:
            raise RuntimeError("Repeated previous owner: " + module)
        if expected[module] != {"source_sha256": item["source_sha256"]}:
            raise RuntimeError("Previous owner differs from the expected local source: " + module)
        stem = module.replace(".", "/")
        source = previous / (stem + ".lean")
        obj = previous / "objects" / (stem + ".olean")
        if obj.is_symlink():
            raise RuntimeError("Unexpected symlink for a previous defining owner: " + module)
        warm["sources"][module] = {"path": str(source), "sha256": item["source_sha256"]}
        warm["warm"]["modules"][module] = {"objects": {str(obj): item["object_sha256"]}}
    warm["residual_payment_report_sha256"] = report_hash
    additions = json.loads((root / "DEPENDENCY_ADDITIONS.json").read_text())
    if len(additions["modules"]) != 6 or set(additions["reports"]) != {"w_layer", "rounded"}:
        raise RuntimeError("Unexpected historical reuse scope")
    if additions["reports"]["w_layer"]["sha256"] != warm["additional_accepted_report_sha256"]:
        raise RuntimeError("W-layer identity differs from the previously accepted all-source owner")
    warm["historical_reports"] = additions["reports"]
    for module, pin in additions["modules"].items():
        if module in warm["sources"] or pin["donor"] not in additions["reports"]:
            raise RuntimeError("Ambiguous historical owner " + module)
        warm["sources"][module] = pin["source"]
        warm["warm"]["modules"][module] = {"objects": pin["objects"]}
    if len(warm["sources"]) != 329:
        raise RuntimeError("Unexpected full dependency count")
    base = Path(pref["source_base"])

    def check_dependencies():
        for ref in additions["reports"].values():
            if sha(Path(ref["path"])) != ref["sha256"]:
                raise RuntimeError("Changed historical acceptance report")
        if sha(report_path) != report_hash:
            raise RuntimeError("Previous completion report changed")
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
    if not seeds["modules"] or set(seeds["modules"]) & set(warm["sources"]):
        raise RuntimeError("The physical classical candidate owners must be new in this overlay")
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
        print("PHYSICAL_CLASSICAL_COMPILE " + json.dumps(record), flush=True)
        print(log.read_text(), flush=True)
        if proc.returncode:
            return proc.returncode
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
