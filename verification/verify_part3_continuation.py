"""Verify only the new P3 continuation modules against the unchanged c509267 baseline.

The complete Lean inventory/axiom gate and Python validator are reused from the
original Part 3 verifier. The owned-module selector is the only change to the
Lean audit body. Missing dependencies are built with Lake; the old 80 modules
are never erased or subjected to another full strict/replay pass.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import difflib
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
    "Part3ProperPowerActualPairFamily",
))
SPECTRAL_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3ExceptionalWeightExtension",
    "Part3ExceptionalWeightGeometry",
))
CONTINUOUS_L2_MODULES = ("ImbalancedChen.Part3ContinuousTraceCauchy",)
CONTINUOUS_HEIGHT_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3RegularCumulativeShellPayment",
    "Part3RegularPositiveMeasureExhaustion",
    "Part3ContinuousTraceExhaustion",
))
TEST_SEMINORM_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3ActualSpectralTestJets",
    "Part3ActualSpectralTestSeminorm",
))
MODULES = (PROPER_POWER_MODULES + SPECTRAL_MODULES + CONTINUOUS_L2_MODULES
           + CONTINUOUS_HEIGHT_MODULES + TEST_SEMINORM_MODULES)
GROUPS = {"all": MODULES, "proper-power": PROPER_POWER_MODULES,
          "spectral": SPECTRAL_MODULES,
          "p35-continuous-l2": CONTINUOUS_L2_MODULES,
          "p35-continuous-height": CONTINUOUS_HEIGHT_MODULES,
          "p35-test-seminorm": TEST_SEMINORM_MODULES,
          "chart-sum": ("ImbalancedChen.Part3ProperPowerLogSaving",
                        "ImbalancedChen.Part3ProperPowerChartSum"),
          "actual-pair": ("ImbalancedChen.FiniteUpperCarrierCore",
                          "ImbalancedChen.Part3ProperPowerActualPair"),
          "actual-pair-family": ("ImbalancedChen.Part3ProperPowerActualPairFamily",)}
PROFILE_REUSE_MANIFEST = (
    "docs/part3-distribution/continuation-20261124/actual-pair-reuse/SOURCE_MANIFEST.json"
)
HEIGHT_REUSE_MANIFEST = (
    "docs/part3-distribution/continuation-20261125/continuous-height/SOURCE_REUSE.json"
)
HEIGHT_HISTORY_MANIFEST = (
    "docs/part3-distribution/continuation-20261125/continuous-height/HISTORICAL_REUSE.json"
)
TEST_REUSE_MANIFEST = (
    "docs/part3-distribution/continuation-20261126/test-seminorm/SOURCE_REUSE.json"
)
ACCEPTED_CONTINUOUS_CORE_SHA256 = (
    "4c6a664915885c31f2d0f8960b2650daa5b7ae44bc31f697a08bbf9a52974c3c"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_seminorm_reuse() -> tuple[list[Path], dict]:
    """Bind selected historical proofs and unchanged imported dependencies."""
    manifest_path = ROOT / TEST_REUSE_MANIFEST
    reuse = json.loads(manifest_path.read_text())
    if reuse["owned_modules"] != list(TEST_SEMINORM_MODULES):
        raise RuntimeError("Test-seminorm ownership differs from the selected group")
    artifact_paths = []
    for item in reuse["artifacts"]:
        path = ROOT / item["path"]
        if sha256(path) != item["sha256"]:
            raise RuntimeError("Test-seminorm provenance/source changed: " + item["path"])
        artifact_paths.append(path)
    paths = [manifest_path, *artifact_paths]
    closure = json.loads((ROOT / reuse["dependency_closure_path"]).read_text())
    pending = list(closure["roots"])
    seen = set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        item = closure["modules"][name]
        relative = "ImbalancedChen/" + name + ".lean"
        if item["path"] != relative or sha256(ROOT / relative) != item["sha256"]:
            raise RuntimeError("Reused test-supplier dependency changed: " + name)
        imports = re.findall(r"^import ImbalancedChen\.(\w+)\s*$",
                             (ROOT / relative).read_text(), re.M)
        if imports != item["project_imports"]:
            raise RuntimeError("Reused test-supplier import graph changed: " + name)
        pending.extend(imports)
        paths.append(ROOT / relative)
    if seen != set(closure["modules"]) or len(seen) != closure["closure_count"]:
        raise RuntimeError("Incomplete test-supplier dependency closure")
    supplier = reuse["selected_supplier"]
    supplier_path, consumer_path = (m.replace(".", "/") + ".lean" for m in TEST_SEMINORM_MODULES)
    if supplier["candidate_path"] != supplier_path:
        raise RuntimeError("Unexpected selected supplier candidate path: " + supplier["candidate_path"])
    excerpts_path = ROOT / supplier["donor_excerpts_path"]
    original_path = ROOT / supplier["extraction_baseline_path"]
    for path in (excerpts_path, original_path, ROOT / supplier_path, ROOT / consumer_path):
        if path not in artifact_paths:
            raise RuntimeError("Test-seminorm source is not a hash-bound artifact: " + str(path))

    original = original_path.read_bytes()
    extraction_sources = {supplier_path: original, consumer_path: (ROOT / consumer_path).read_bytes()}
    verified_excerpts = {relative: set() for relative in extraction_sources}
    for source in json.loads(excerpts_path.read_bytes())["sources"]:
        relative = source["candidate_path"]
        if relative not in extraction_sources:
            raise RuntimeError("Unexpected donor candidate path: " + relative)
        extracted = extraction_sources[relative]
        for excerpt in source["excerpts"]:
            label = f"{source['source_path']}:{excerpt['line_start']}-{excerpt['line_end']}"
            text = excerpt["text"].encode("utf-8")
            if not text:
                raise RuntimeError("Empty donor excerpt: " + label)
            if hashlib.sha256(text).hexdigest() != excerpt["sha256"]:
                raise RuntimeError("Donor excerpt SHA-256 mismatch: " + label)
            start = extracted.find(text)
            if start == -1 or extracted.find(text, start + 1) != -1:
                raise RuntimeError(f"Donor excerpt does not occur exactly once in {relative}: {label}")
            if text in verified_excerpts[relative]:
                raise RuntimeError("Duplicate donor excerpt: " + label)
            verified_excerpts[relative].add(text)
    if (len(verified_excerpts[supplier_path]), len(verified_excerpts[consumer_path])) != (5, 1):
        raise RuntimeError("Expected five supplier excerpts and one consumer excerpt")

    candidate = (ROOT / supplier_path).read_bytes().decode("utf-8")
    patch = "".join(difflib.unified_diff(
        original.decode("utf-8").splitlines(keepends=True), candidate.splitlines(keepends=True),
        fromfile="selected-historical-declarations", tofile=supplier["candidate_path"]))
    if (ROOT / supplier["repair_patch_path"]).read_bytes() != patch.encode("utf-8"):
        raise RuntimeError("Supplier repair patch does not reproduce the accepted candidate")
    return paths, {
        "manifest": TEST_REUSE_MANIFEST,
        "unchanged_project_dependencies": len(seen),
        "acceptance_repeated": False,
        "trust_mode": "NORMAL_IMPORTED_ENVIRONMENT_TRUST",
        "selected_historical_declarations_owned_here": True,
        "whole_historical_modules_promoted": False,
    }


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
        height_reuse = json.loads((ROOT / HEIGHT_REUSE_MANIFEST).read_text())
        for item in height_reuse["donor_sources"]:
            relative = item["candidate_path"]
            if relative != item["module"].replace(".", "/") + ".lean":
                raise RuntimeError("Invalid reused height source path: " + relative)
            if sha256(ROOT / relative) != item["candidate_sha256"]:
                raise RuntimeError("Reused height source changed: " + relative)
            paths.append(ROOT / relative)
        paths.append(ROOT / HEIGHT_REUSE_MANIFEST)
        height_history = json.loads((ROOT / HEIGHT_HISTORY_MANIFEST).read_text())
        for item in height_history["modules"].values():
            if sha256(ROOT / item["path"]) != item["source_sha256"]:
                raise RuntimeError("Historically accepted height dependency changed: " + item["path"])
        paths.append(ROOT / HEIGHT_HISTORY_MANIFEST)
        if args.group in ("all", "p35-test-seminorm"):
            test_paths, test_reuse = test_seminorm_reuse()
            paths.extend(test_paths)
            report["test_supplier_reuse"] = test_reuse
        if args.group == "p35-continuous-height":
            core = ROOT / "ImbalancedChen/Part3ContinuousTraceCauchy.lean"
            if sha256(core) != ACCEPTED_CONTINUOUS_CORE_SHA256:
                raise RuntimeError("Previously accepted continuous Cauchy core changed")
            report["accepted_continuous_core_reuse"] = {
                "commit": "de24ecddb6f5bdb0c8173c788ace734207c457a0",
                "source_sha256": ACCEPTED_CONTINUOUS_CORE_SHA256,
                "acceptance_repeated": False,
            }
            report["historically_accepted_height_dependencies"] = {
                "modules": sorted(height_history["modules"]),
                "declarations": height_history["historical_declaration_count"],
                "acceptance_repeated": False,
                "trust_mode": "NORMAL_IMPORTED_ENVIRONMENT_TRUST",
            }
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
