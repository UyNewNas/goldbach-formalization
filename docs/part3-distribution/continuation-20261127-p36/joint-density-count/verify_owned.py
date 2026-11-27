#!/usr/bin/env python3
"""Replay and inventory the compiled owner against their frozen sources.

The original project audit and validator are reused without modification.
This driver never builds dependencies or modifies their checkouts or objects.
The compile overlay, source/object pins and prior accepted cache must exist.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import uuid

sys.dont_write_bytecode = True


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    report = {
        "status": "INITIALIZING", "whole_p36_closed": False,
        "verification_id": uuid.uuid4().hex,
        "scope": "Joint modulus cap, rectangle density, paid classical count and remaining high ranks",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "stages": [],
    }
    out = root / "acceptance"
    out.mkdir(exist_ok=True)

    def save() -> None:
        pending = out / "report.json.tmp"
        pending.write_text(json.dumps(report, indent=2) + "\n")
        pending.replace(out / "report.json")

    # Invalidate any previous success before reading even the first input pin.
    save()

    def check_inputs() -> None:
        previous = Path("/workspace/p36-joint-rounding-20261127/acceptance/report.json")
        if sha(previous) != warm["joint_rounding_report_sha256"]:
            raise RuntimeError("The previous verified joint rounding report changed")
        for module, pin in warm["additional_external"].items():
            if sha(Path(pin["source"]["path"])) != pin["source"]["sha256"]:
                raise RuntimeError("Changed external dependency source: " + module)
            for name, digest in pin["objects"].items():
                original = Path(name)
                relative = module.replace(".", "/") + "".join(original.suffixes)
                search = [root / "objects"] + [Path(p) for p in pref["lean_path"].split(":")[1:]]
                actual = next((p / relative for p in search if (p / relative).is_file()), None)
                if actual != original or sha(original) != digest:
                    raise RuntimeError("Changed external object or selected path: " + module)
        for ref in warm["historical_reports"].values():
            if sha(Path(ref["path"])) != ref["sha256"]:
                raise RuntimeError("Changed historical acceptance report")
        if Path(pref["lean_path"].split(":")[0]).resolve() != root / "objects":
            raise RuntimeError("Unexpected first Lean object search root")
        for module, item in warm["sources"].items():
            if sha(base / item["path"]) != item["sha256"]:
                raise RuntimeError("Changed dependency source: " + module)
        for module, item in warm["warm"]["modules"].items():
            for path, digest in item["objects"].items():
                if sha(Path(path)) != digest:
                    raise RuntimeError("Changed accepted dependency object: " + module)
                suffix = "".join(Path(path).suffixes)
                if suffix not in (".olean", ".olean.private", ".olean.server"):
                    raise RuntimeError("Unexpected dependency object suffix: " + path)
                live = root / "objects" / (module.replace(".", "/") + suffix)
                if not live.is_file() or sha(live) != digest:
                    raise RuntimeError("Changed live dependency object: " + module)
        for module, item in pins["modules"].items():
            relative = Path(module.replace(".", "/"))
            if sha(root / relative.with_suffix(".lean")) != item["source_sha256"]:
                raise RuntimeError("Changed owned source: " + module)
            obj = root / "objects" / relative.with_suffix(".olean")
            if obj.is_symlink() or sha(obj) != item["object_sha256"]:
                raise RuntimeError("Changed or non-owned object: " + module)
        for relative, digest in pins["validation_source_sha256"].items():
            if sha(base / relative) != digest:
                raise RuntimeError("Changed original audit helper: " + relative)
        if sha(root / "P36JointDensityCountAudit.lean") != pins["audit_sha256"]:
            raise RuntimeError("Changed generated defining-module audit")
        if sha(Path(pref["compiler"]["path"])) != pref["compiler"]["sha256"]:
            raise RuntimeError("Changed pinned compiler")
        if sha(checker) != pins["checker_sha256"]:
            raise RuntimeError("Changed pinned kernel checker")

    def run(name: str, command: list[str], timeout: int) -> str:
        path = out / (name + ".log")
        tick = time.monotonic()
        print("START " + name, flush=True)
        with path.open("w") as handle:
            result = subprocess.run(command, cwd=root, env=env, stdout=handle,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        record = {"name": name, "command": command, "exit_code": result.returncode,
                  "elapsed_seconds": round(time.monotonic() - tick, 3),
                  "log": path.name, "log_sha256": sha(path)}
        report["stages"].append(record)
        save()
        body = path.read_text()
        if result.returncode:
            raise RuntimeError(name + " failed: " + body[-4000:])
        print("PASS " + json.dumps(record), flush=True)
        return body

    try:
        pins = json.loads((root / "OWNED_SOURCE_PINS.json").read_text())
        warm = json.loads((root / "warm-pins.json").read_text())
        pref = json.loads((root / "PREFLIGHT.json").read_text())
        base = Path(pref["source_base"])
        modules = tuple(pins["modules"])
        env = os.environ.copy()
        env.update(LEAN_PATH=pref["lean_path"], LEAN_NUM_THREADS="1",
                   LEAN_SYSROOT="/workspace/toolchains/lean-4.33.0-rc1-linux")
        lean = Path(pref["compiler"]["path"])
        checker = lean.with_name("leanchecker")
        report.update(
            status="RUNNING", modules=modules,
            source_and_object_pins=pins["modules"],
            accepted_dependency_report_sha256=warm["warm"]["accepted_report_sha256"],
            additional_accepted_dependency_report_sha256=warm["additional_accepted_report_sha256"],
            warm_admission_dependency_report_sha256=warm["warm_admission_report_sha256"],
            three_frontier_dependency_report_sha256=warm["three_frontier_report_sha256"],
            residual_payment_dependency_report_sha256=warm["residual_payment_report_sha256"],
            physical_classical_dependency_report_sha256=warm["physical_classical_report_sha256"],
            joint_marked_dependency_report_sha256=warm["joint_marked_report_sha256"],
            joint_rounding_dependency_report_sha256=warm["joint_rounding_report_sha256"],
            added_external_cache=warm["additional_external"],
            historical_dependency_reports=warm["historical_reports"],
            compiler=pref["compiler"], kernel_checker_sha256=sha(checker),
            driver_sha256=sha(Path(__file__)), audit_sha256=pins["audit_sha256"],
            lean_path=pref["lean_path"],
        )
        save()
        check_inputs()
        sys.path.insert(0, str(base / "verification"))
        import verify_part3_continuation as helper
        expected_audit = helper.render_audit(modules)
        if (root / "P36JointDensityCountAudit.lean").read_text() != expected_audit:
            raise RuntimeError("Audit differs from the original renderer")
        for module in modules:
            source = root / (module.replace(".", "/") + ".lean")
            if helper.baseline.FORBIDDEN.search(helper.baseline.lean_code(source.read_text())):
                raise RuntimeError("Forbidden proof escape in " + module)
            body = run("replay-" + module, [str(checker), "--verbose", module], 600)
            replays = [line for line in body.splitlines() if line.startswith("replaying ")]
            if replays != ["replaying " + module]:
                raise RuntimeError("Unexpected kernel replay scope: " + repr(replays))
        body = run("owned-inventory-audit", [str(lean), "-t0", "-j1",
                   "-DwarningAsError=true", "-R", str(root),
                   str(root / "P36JointDensityCountAudit.lean")], 1800)
        declarations, counts = helper.baseline.validate_inventory(body, modules=modules)
        (out / "declarations.json").write_text(json.dumps(declarations, indent=2) + "\n")
        check_inputs()
        if sha(checker) != report["kernel_checker_sha256"]:
            raise RuntimeError("Kernel checker changed during verification")
        report.update(status="VERIFIED_OWNED", declaration_count=len(declarations),
                      module_counts=counts,
                      observed_transitive_axioms=sorted({a for d in declarations for a in d["axioms"]}))
        return 0
    except Exception as error:
        report.update(status="FAILED", error=str(error))
        return 1
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        save()
        print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    raise SystemExit(main())
