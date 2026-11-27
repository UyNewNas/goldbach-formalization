#!/usr/bin/env python3
"""Compile, independently replay, and inventory the Cell05 interface join.

Uses existing pinned dependencies. Never runs lake update. Receipts describe
this new dependency context, not a transfer of historical acceptance.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / "docs/verification/20261127-p26-cell05"
SYSROOT = Path(os.environ.get("P26_LEAN_SYSROOT", "/workspace/toolchains/lean-4.33.0-rc1-linux"))
MATHLIB = Path(os.environ.get("P26_MATHLIB_ROOT", "/workspace/compile-deps/mathlib"))
OBJECTS = ROOT / ".lake/build/lib/lean"
NAMES = [
    "P2PositiveAffineSimplexLogJensen",
    "P2DegreeSixLogGapSoundness",
    "P2OriginalLogMomentQ96Checker",
    "P2OriginalLogMomentQ96ArithmeticBridge",
    "P2OriginalSaving19RowNumerics",
    "P2OriginalSaving19RowNumericsPureBridge",
    "P2OriginalSaving19Cell05GeometryCertificate",
    "P2OriginalSaving19Cell05OriginalRowChecks",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_PATH = "tools/p26/cell05-geometry-certificate/JoinedOwnedAudit.lean"
SCOPE = "Cell05 original parse/shape/vertex fields/56 geometry rows and original RowNumerics join; no moment refinement, ownership or integral endpoint"


def pin(path):
    data = path.read_bytes()
    return {"path": str(path), "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    (OBJECTS / "ImbalancedChen").mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["PATH"] = str(SYSROOT / "bin") + ":" + env.get("PATH", "")
    ext = sorted((MATHLIB / ".lake/packages").glob("*/.lake/build/lib/lean"))
    env["LEAN_PATH"] = ":".join(map(str, [OBJECTS, *ext, MATHLIB / ".lake/build/lib/lean"]))
    env["LEAN_NUM_THREADS"] = "1"
    flags = ["--trust=0", "-DwarningAsError=true", "-j1", "-M12288",
             "-DmaxRecDepth=1000000", "-DmaxHeartbeats=0"]
    pending = ["ImbalancedChen." + name for name in NAMES]
    closure = {}
    while pending:
        module = pending.pop()
        if module in closure:
            continue
        source = ROOT / (module.replace(".", "/") + ".lean")
        closure[module] = {"source": pin(source)}
        pending.extend(re.findall(r"^(?:public )?import (ImbalancedChen\.[\w.]+)",
                                  source.read_text(), re.M))
    for module in closure:
        if module.rsplit(".", 1)[1] not in NAMES:
            closure[module]["reused_object"] = pin(OBJECTS / (module.replace(".", "/") + ".olean"))
    state = {"schema": "p26_cell05_join_verification_v1", "status": "running",
             "P2_6_complete": False, "cwd": str(ROOT), "project_closure": closure,
             "lean_path": env["LEAN_PATH"], "commands": [],
             "runtime": {name: pin(SYSROOT / "bin" / name) for name in ("lean", "leanchecker")},
             "mathlib_commit": subprocess.check_output(["git", "-C", str(MATHLIB), "rev-parse", "HEAD"], text=True).strip(),
             "scope": SCOPE, "audit_source": pin(ROOT / AUDIT_PATH),
             "verifier_source": pin(Path(__file__))}

    def save():
        (OUT / "RUN.json").write_text(json.dumps(state, indent=2) + "\n")

    def run(label, argv):
        log = OUT / (label + ".log")
        record = {"label": label, "argv": list(map(str, argv)), "cwd": str(ROOT)}
        state["commands"].append(record)
        save()
        started = time.monotonic()
        with log.open("wb") as stream:
            process = subprocess.run(argv, cwd=ROOT, env=env, stdout=stream,
                                     stderr=subprocess.STDOUT, timeout=900)
        record.update(exit_code=process.returncode, elapsed_seconds=time.monotonic() - started,
                      log=pin(log))
        save()
        print(label, "exit=" + str(process.returncode), flush=True)
        if process.returncode or "sorryAx" in log.read_text():
            print(log.read_text()[-6000:], flush=True)
            state["status"] = "failed"
            save()
            raise SystemExit(1)

    for name in NAMES:
        target = OBJECTS / "ImbalancedChen" / (name + ".olean")
        run(name + "-normal", [str(SYSROOT / "bin/lean"), *flags, "-o", str(target),
                               "ImbalancedChen/" + name + ".lean"])
        state["project_closure"]["ImbalancedChen." + name]["new_object"] = pin(target)
        run(name + "-kernel", [str(SYSROOT / "bin/leanchecker"), "--verbose", "ImbalancedChen." + name])
        assert pin(target) == state["project_closure"]["ImbalancedChen." + name]["new_object"]
    run("joined-owned", [str(SYSROOT / "bin/lean"), *flags, AUDIT_PATH])
    declarations, completed = [], {}
    for line in (OUT / "joined-owned.log").read_text().splitlines():
        if line.startswith("P26_GEOMETRY01_AUDIT_DECL "):
            item = json.loads(line.split(" ", 1)[1])
            assert not (item["unsafe"] or item["partial"] or item["axiom"])
            assert set(item["axioms"]) <= ALLOWED
            declarations.append(item)
        if line.startswith("P26_GEOMETRY01_AUDIT_COMPLETE "):
            item = json.loads(line.split(" ", 1)[1])
            assert item["module"] not in completed
            completed[item["module"]] = item["count"]
    assert set(completed) == {"ImbalancedChen." + name for name in NAMES}
    for module, count in completed.items():
        assert count == sum(item["module"] == module for item in declarations)
    for module, info in closure.items():
        assert pin(ROOT / (module.replace(".", "/") + ".lean")) == info["source"]
        if "reused_object" in info:
            assert pin(OBJECTS / (module.replace(".", "/") + ".olean")) == info["reused_object"]
    (OUT / "owned-declarations.json").write_text(json.dumps(declarations, indent=2) + "\n")
    state.update(status="succeeded", owned_counts=completed, owned_declarations=len(declarations),
                 allowed_axioms=sorted(ALLOWED))
    save()
    print(json.dumps({"status": state["status"], "modules": len(NAMES),
                      "owned_declarations": len(declarations), "P2_6_complete": False}))


if __name__ == "__main__":
    main()
