"""Verify only the new P3 continuation modules against the unchanged c509267 baseline.

The complete Lean inventory/axiom gate and Python validator are reused from the
original Part 3 verifier. The owned-module selector is the only change to the
Lean audit body. Missing dependencies are built with Lake; the old 80 modules
are never erased or subjected to another full strict/replay pass.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode = True
import verify_part3_distribution as baseline

ROOT = Path(__file__).resolve().parents[1]
BASELINE_HEAD = "c509267dc630d91df33033abde1c484ec86b96ae"
LEAN_COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
PROPER_POWER_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3SignedModulusPayment",
    "Part3ProperPowerResidualPayment",
    "Part3ProperPowerDyadicBudget",
    "Part3ProperPowerOriginalChart",
    "Part3ProperPowerLogSaving",
    "Part3ProperPowerChartSum",
    "FiniteUpperCarrierCore",
    "Part3ProperPowerActualPair",
))
SPECTRAL_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3ExceptionalWeightExtension",
    "Part3ExceptionalWeightGeometry",
))
MODULES = PROPER_POWER_MODULES + SPECTRAL_MODULES
GROUPS = {"all": MODULES, "proper-power": PROPER_POWER_MODULES,
          "spectral": SPECTRAL_MODULES,
          "chart-sum": ("ImbalancedChen.Part3ProperPowerLogSaving",
                        "ImbalancedChen.Part3ProperPowerChartSum"),
          "actual-pair": ("ImbalancedChen.FiniteUpperCarrierCore",
                          "ImbalancedChen.Part3ProperPowerActualPair")}
PROFILE_REUSE_MANIFEST = (
    "docs/part3-distribution/continuation-20261124/actual-pair-reuse/SOURCE_MANIFEST.json"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def render_audit(modules: tuple[str, ...]) -> str:
    """Reuse the entire serialized-inventory and transitive-axiom audit body."""
    source = (ROOT / baseline.AUDIT).read_text()
    body = source[source.index("\n/-!"):]
    selector = "  let modules := #[" + ",\n    ".join(chr(96) + m for m in modules) + "]\n"
    body, count = re.subn(
        r"  let modules := #\[.*?\]\n(?=  let allowed :=)",
        lambda _: selector, body, flags=re.S)
    if count != 1:
        raise RuntimeError("Could not identify the original audit's single module selector")
    return "\n".join("import " + m for m in modules) + "\nimport Lean.Util.CollectAxioms\n" + body


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--group", choices=tuple(GROUPS), default="all")
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / ".lake/p3-continuation-verification")
    parser.add_argument("--expected-head")
    args = parser.parse_args()
    modules = GROUPS[args.group]
    out = args.output_dir.resolve()
    out.mkdir(parents=True, exist_ok=True)
    for name in ("declarations.json", "theorem-types.txt"):
        (out / name).unlink(missing_ok=True)
    report = {
        "status": "RUNNING", "baseline_commit": BASELINE_HEAD,
        "baseline_validation": {
            "basis": "User-supplied successful strict/kernel/axiom receipt; not rerun here",
            "modules": 80, "declarations": 1774,
            "reported_receipt": "/workspace/goldbach-p3/.lake/p3-fourth-verification/report.json",
        },
        "scope": "New P3 manuscript derivations only; not a certificate of the whole P3 target",
        "group": args.group, "modules": list(modules),
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "allowed_transitive_axioms": sorted(baseline.ALLOWED),
        "stages": [],
    }

    def save() -> None:
        (out / "report.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(command: list[str], name: str) -> str:
        print("START " + name, flush=True)
        tick = time.monotonic()
        logfile = out / (name + ".log")
        with logfile.open("w") as handle:
            handle.write("command=" + json.dumps(command) + "\n")
            handle.flush()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=handle,
                                    stderr=subprocess.STDOUT)
        log = logfile.read_text(errors="replace").split("\n", 1)[1]
        report["stages"].append({"name": name, "command": command,
                                 "exit_code": result.returncode,
                                 "elapsed_seconds": round(time.monotonic() - tick, 3),
                                 "log_sha256": sha256(logfile)})
        save()
        if result.returncode:
            raise RuntimeError(f"{name}: exit {result.returncode}\n{log}")
        print("PASS " + name, flush=True)
        return log

    save()
    try:
        for relative, expected in baseline.CONFIG_SHA256.items():
            if sha256(ROOT / relative) != expected:
                raise RuntimeError("Pinned configuration changed: " + relative)
        if (ROOT / "lean-toolchain").read_text().strip() != baseline.TOOLCHAIN:
            raise RuntimeError("Toolchain pin changed")
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        actual = {p["name"]: p["rev"] for p in manifest["packages"]}
        if any(actual.get(k) != v for k, v in baseline.PINS.items()):
            raise RuntimeError("Dependency pin changed")
        audit = out / "Part3ContinuationAudit.lean"
        audit.write_text(render_audit(modules))
        paths = [ROOT / (m.replace(".", "/") + ".lean") for m in MODULES]
        reuse = json.loads((ROOT / PROFILE_REUSE_MANIFEST).read_text())
        for item in reuse["donor_sources"]:
            relative = item["path"]
            if relative != item["module"].replace(".", "/") + ".lean":
                raise RuntimeError("Invalid reused profile source path: " + relative)
            path = ROOT / relative
            if sha256(path) != item["staged_sha256"]:
                raise RuntimeError("Reused profile source changed: " + relative)
            paths.append(path)
        paths.append(ROOT / PROFILE_REUSE_MANIFEST)
        paths += [Path(__file__).resolve(), ROOT / "verification/verify_part3_distribution.py",
                  ROOT / baseline.AUDIT, ROOT / baseline.LEXER,
                  ROOT / ".github/workflows/part3-continuation.yml",
                  *(ROOT / p for p in baseline.CONFIG_SHA256)]
        hashes = {p.relative_to(ROOT).as_posix(): sha256(p) for p in paths}
        report["source_sha256"] = hashes
        report["generated_audit_sha256"] = sha256(audit)
        for path in paths:
            if path.suffix == ".lean" and baseline.FORBIDDEN.search(baseline.lean_code(path.read_text())):
                raise RuntimeError("Forbidden proof escape: " + str(path))
        if args.source_only:
            report["status"] = "SOURCE_ONLY_NOT_COMPILED"
            save()
            print("Source and pin checks passed; no proof verification was performed.")
            return
        head = run(["git", "rev-parse", "HEAD"], "head").strip()
        report["head_commit"] = head
        if args.expected_head and args.expected_head != head:
            raise RuntimeError("The checked-out head differs from --expected-head")
        run(["git", "merge-base", "--is-ancestor", BASELINE_HEAD, head], "baseline-ancestor")
        if run(["git", "status", "--porcelain", "--untracked-files=all"], "working-tree").strip():
            raise RuntimeError("Commit the exact proof sources before final verification")
        baseline_paths = [m.replace(".", "/") + ".lean" for m in baseline.MODULES]
        changed = run(["git", "diff", "--name-only", BASELINE_HEAD, "--", *baseline_paths],
                      "baseline-proof-preservation").strip()
        if changed:
            raise RuntimeError("This incremental verifier expects unchanged baseline proofs: " + changed)
        version = run(["lake", "env", "lean", "--version"], "lean-version").strip()
        if not re.search(r"\bversion 4\.33\.0-rc1(?:,|\))", version) or LEAN_COMMIT not in version:
            raise RuntimeError("Unexpected compiler version/commit: " + version)
        report["lean_version"] = version
        tools = json.loads(run(["lake", "env", sys.executable, "-c",
            "import json,os,shutil; print(json.dumps({"
            "'sysroot':os.environ.get('LEAN_SYSROOT'),"
            "'lean':shutil.which('lean'),'leanchecker':shutil.which('leanchecker'),"
            "'lean_path':os.environ.get('LEAN_PATH')}))"], "bundled-tools"))
        if not all(tools.get(k) for k in ("sysroot", "lean", "leanchecker", "lean_path")):
            raise RuntimeError("Could not identify the original bundled Lean/checker environment")
        tool_hashes = {}
        for name in ("lean", "leanchecker"):
            path = Path(tools[name]).resolve()
            expected = (Path(tools["sysroot"]) / "bin" / name).resolve()
            if path != expected or not expected.is_file():
                raise RuntimeError("Tool is not from the pinned installation: " + name)
            tool_hashes[str(path)] = sha256(path)
        report["tool_paths"] = tools
        report["tool_sha256"] = tool_hashes
        for package in manifest["packages"]:
            repo = str(ROOT / ".lake/packages" / package["name"])
            revision = run(["git", "-C", repo, "rev-parse", "HEAD"],
                           "pin-" + package["name"]).strip()
            if revision != package["rev"]:
                raise RuntimeError("Actual dependency checkout revision changed: " + package["name"])
            if run(["git", "-C", repo, "status", "--porcelain", "--untracked-files=all"],
                   "clean-" + package["name"]).strip():
                raise RuntimeError("Dependency checkout has uncommitted changes: " + package["name"])
        run(["lake", "build", *modules], "build-new-targets")
        objdir = ROOT / ".lake/build/lib/lean"
        # Bind the actual Lake import resolution for all owned modules to this tree.
        roots = [Path(p).resolve() for p in tools["lean_path"].split(":") if p]
        for module in modules:
            relative = module.replace(".", "/") + ".olean"
            resolved = next((p / relative for p in roots if (p / relative).is_file()), None)
            if resolved is None or resolved.resolve() != (objdir / relative).resolve():
                raise RuntimeError("Lake resolves an owned module outside the verified object tree: " + module)
        objects = {}
        for module in modules:
            relative = module.replace(".", "/")
            obj = objdir / (relative + ".olean")
            parts = [Path(str(obj) + s) for s in ("", ".server", ".private")]
            for part in parts:
                part.unlink(missing_ok=True)
            run(["lake", "env", tools["lean"], "-t0", "-j1", "-DwarningAsError=true",
                 "-o", str(obj), relative + ".lean"], module.rsplit(".", 1)[1] + "-strict")
            if not obj.is_file():
                raise RuntimeError("Strict compilation produced no object: " + module)
            objects.update({p.relative_to(ROOT).as_posix(): sha256(p)
                            for p in parts if p.is_file()})
        report["olean_sha256"] = objects
        for module in modules:
            replay = run(["lake", "env", tools["leanchecker"], "--verbose", module],
                         module.rsplit(".", 1)[1] + "-replay")
            if "replaying " + module not in replay.splitlines():
                raise RuntimeError("Missing module replay evidence: " + module)
        log = run(["lake", "env", tools["lean"], "-t0", "-j1", "-DwarningAsError=true",
                   str(audit)], "axioms")
        records, counts = baseline.validate_inventory(log, modules=modules)
        for path, expected in {**hashes, **objects}.items():
            if sha256(ROOT / path) != expected:
                raise RuntimeError("Source/object changed during verification: " + path)
        if sha256(audit) != report["generated_audit_sha256"]:
            raise RuntimeError("Generated audit changed during verification")
        if run(["git", "status", "--porcelain", "--untracked-files=all"],
               "final-working-tree").strip():
            raise RuntimeError("Working tree changed during verification")
        (out / "declarations.json").write_text(json.dumps(records, indent=2) + "\n")
        (out / "theorem-types.txt").write_text(
            "head_commit=" + head + "\n\n" + "\n\n".join(
                r["name"] + " :\n" + r["type"] + "\naxioms=" + ",".join(r["axioms"])
                for r in records if r["kind"] == "theorem") + "\n")
        report.update(status="PASSED", declaration_count=len(records), module_counts=counts,
                      finished_utc=datetime.now(timezone.utc).isoformat())
        save()
        print(f"PASS: {len(records)} declarations across {len(modules)} new modules.")
    except BaseException as error:
        report.update(status="FAILED", error=str(error))
        save()
        raise


if __name__ == "__main__":
    main()
