#!/usr/bin/env python3
"""Independent pinned strict/replay/axiom acceptance of the Part 3 prime-AP leaf."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
MODULE = "ImbalancedChen.Part3PrimeAPDistribution"
AUDIT = "verification.parts.p3.Part3PrimeAPDistributionAudit"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--expected-head", required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    receipt = {"status": "RUNNING", "expected_head": args.expected_head,
               "module": MODULE, "steps": [], "allowed_axioms": sorted(ALLOWED)}

    def save():
        (out / "receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")

    def run(name, command, cwd=ROOT):
        tick = time.monotonic()
        log = out / (name + ".log")
        with log.open("w") as f:
            f.write("command=" + json.dumps(command) + "\n")
            f.flush()
            res = subprocess.run(command, cwd=cwd, text=True,
                                 stdout=f, stderr=subprocess.STDOUT)
        receipt["steps"].append({"step": name, "command": command,
                                  "exit_code": res.returncode,
                                  "elapsed_seconds": round(time.monotonic() - tick, 3)})
        save()
        if res.returncode:
            raise RuntimeError(name + " exit " + str(res.returncode) + "\n" +
                               log.read_text(errors="replace")[-16000:])
        return log.read_text(errors="replace").split("\n", 1)[1]

    save()
    try:
        head = run("head", ["git", "rev-parse", "HEAD"]).strip()
        if head != args.expected_head:
            raise RuntimeError("HEAD differs from expected")
        run("baseline", ["git", "merge-base", "--is-ancestor",
                         "1a80c1bcce67886f699d097fc37fd245cd3620bf", "HEAD"])
        if run("clean", ["git", "status", "--porcelain", "--untracked-files=all"]).strip():
            raise RuntimeError("Working tree dirty")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        revs = {p["name"]: p["rev"] for p in manifest["packages"]}
        required = {"goldbach": "09b97db5764ade1246bfb77206baa1b124760958",
                    "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"}
        if any(revs.get(k) != v for k, v in required.items()):
            raise RuntimeError("Frozen dependency revision changed")
        for k, v in required.items():
            actual = run("pin-" + k, ["git", "rev-parse", "HEAD"],
                         ROOT / ".lake/packages" / k).strip()
            if actual != v:
                raise RuntimeError("Actual dependency checkout differs: " + k)
        if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.0-rc1":
            raise RuntimeError("Frozen Lean version changed")
        source = ROOT / "ImbalancedChen/Part3PrimeAPDistribution.lean"
        audit_source = ROOT / "verification/parts/p3/Part3PrimeAPDistributionAudit.lean"
        receipt["sources"] = {str(p.relative_to(ROOT)): sha256(p) for p in
                              (source, audit_source, Path(__file__).resolve())}
        run("build", ["lake", "build", MODULE])
        production = ROOT / ".lake/build/lib/lean/ImbalancedChen/Part3PrimeAPDistribution.olean"
        setup = ROOT / ".lake/build/ir/ImbalancedChen/Part3PrimeAPDistribution.setup.json"
        if not setup.is_file():
            raise RuntimeError("Lake target setup missing")
        for suffix in ("", ".private", ".server"):
            Path(str(production) + suffix).unlink(missing_ok=True)
        run("strict", ["lake", "env", "lean", "-t0", "-DwarningAsError=true",
                       "-o", str(production), "--setup", str(setup), str(source)])
        target_hash = sha256(production)
        receipt["target_olean_sha256"] = target_hash
        shutil.copy2(production, out / "target.olean")
        version = run("version", ["lake", "env", "lean", "--version"]).strip()
        if "4.33.0-rc1" not in version:
            raise RuntimeError("Unexpected Lean version " + version)
        tool = run("stock-checker-path",
                   ["lake", "env", "bash", "-c", "command -v leanchecker"]).strip()
        receipt["stock_checker"] = {"path": tool, "sha256": sha256(tool)}
        if ("replaying " + MODULE) not in run(
                "production-replay", ["lake", "env", tool, "--verbose", MODULE]).splitlines():
            raise RuntimeError("No original-checker replay marker")
        if sha256(production) != target_hash:
            raise RuntimeError("Production target changed after replay")
        audit_obj = ROOT / ".lake/build/lib/lean/verification/parts/p3/Part3PrimeAPDistributionAudit.olean"
        audit_obj.parent.mkdir(parents=True, exist_ok=True)
        for suffix in ("", ".private", ".server"):
            Path(str(audit_obj) + suffix).unlink(missing_ok=True)
        audit_log = run("audit-strict",
                        ["lake", "env", "lean", "-t0", "-DwarningAsError=true",
                         "-o", str(audit_obj), str(audit_source)])
        audit_hash = sha256(audit_obj)
        if ("replaying " + AUDIT) not in run(
                "audit-replay", ["lake", "env", tool, "--verbose", AUDIT]).splitlines():
            raise RuntimeError("No original-checker audit replay marker")
        if sha256(production) != target_hash or sha256(audit_obj) != audit_hash:
            raise RuntimeError("Proof object changed between strict compile, audit and replay")
        shutil.copy2(audit_obj, out / "audit.olean")

        def records(prefix):
            return [json.loads(l[len(prefix):]) for l in audit_log.splitlines()
                    if l.startswith(prefix)]

        decl = records("PART3_AP_DECL ")
        summary = records("PART3_AP_MODULE ")
        serialized = records("PART3_AP_SERIALIZED ")
        imports = records("PART3_AP_IMPORT ")
        if not decl or summary != [{"module": MODULE, "count": len(decl)}]:
            raise RuntimeError("Incomplete defining-module compiler census")
        if len(serialized) != 1 or serialized[0]["serialized_constant_count"] != len(decl):
            raise RuntimeError("Serialized and compiler declaration counts differ")
        if len({d["name"] for d in decl}) != len(decl):
            raise RuntimeError("Duplicate owned declaration")
        for d in decl:
            if (d["module"] != MODULE or not d["type"] or d["kind"] == "axiom"
                    or set(d["axioms"]) - ALLOWED or "⋯" in d["type"]):
                raise RuntimeError("Forbidden owned declaration or transitive axiom")
        if not imports or len({r["module"] for r in imports}) != len(imports):
            raise RuntimeError("Missing/duplicated import modules")
        for item in imports:
            file = Path(item["olean"]).resolve()
            if not file.is_file():
                raise RuntimeError("Missing imported object " + str(file))
            item.update(olean=str(file), size=file.stat().st_size, sha256=sha256(file))
        if len({r["olean"] for r in imports}) != len(imports):
            raise RuntimeError("Non-injective import object resolution")
        if sha256(production) != target_hash or sha256(audit_obj) != audit_hash:
            raise RuntimeError("Object mutated during import provenance audit")
        if any(sha256(ROOT / path) != h for path, h in receipt["sources"].items()):
            raise RuntimeError("Proof or verification source changed")
        (out / "compiler-declarations.json").write_text(json.dumps(decl, indent=2) + "\n")
        (out / "actual-import-objects.json").write_text(json.dumps(imports, indent=2) + "\n")
        if run("final-clean", ["git", "status", "--porcelain", "--untracked-files=all"]).strip():
            raise RuntimeError("Checkout became dirty")
        receipt.update(status="PASSED", head_commit=head, lean_version=version,
                       owned_declarations=len(decl),
                       owned_theorems=sum(d["kind"] == "theorem" for d in decl),
                       actual_import_objects=len(imports),
                       audit_olean_sha256=audit_hash,
                       serial=serialized[0])
        save()
    except BaseException as error:
        receipt.update(status="FAILED", error=str(error))
        save()
        raise


if __name__ == "__main__":
    main()
