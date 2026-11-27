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
    "Part3ProperPowerActualPairFamily",
))
SPECTRAL_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3ExceptionalWeightExtension",
    "Part3ExceptionalWeightGeometry",
))
INTERFACE_MODULES = ("ImbalancedChen.Part3CommonCompletedInterface",)
ACTUAL_INTERFACE_MODULES = ("ImbalancedChen.Part3ActualCommonCompletedInterface",)
ACTUAL_INTERFACE_ENTRY = ("ImbalancedChen.Part3Node31",)
ACTUAL_INTERFACE_DOCS = "docs/part3-distribution/p31-actual-interface-20261126"
POISSON_LANES_MODULES = ("ImbalancedChen.Part3OriginalCommonPoissonLanesCore",)
POISSON_LANES_DOCS = "docs/part3-distribution/p31-poisson-lanes-20261126"
SHIU_WINDOWS_MODULES = ("ImbalancedChen.Part3MediumPrimitiveShiuFiniteCover",
                        "ImbalancedChen.Part3MediumPrimitiveShiuWindowGate")
SHIU_WINDOWS_DOCS = "docs/part3-distribution/p31-shiu-windows-20261126"
KERNEL_LANES_MODULES = ("ImbalancedChen.Part3OriginalCommonPoissonKernelLanesCore",)
KERNEL_LANES_DOCS = "docs/part3-distribution/p31-kernel-lanes-20261126"
ACTUAL_SOURCE_LANES_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3PrimaryPrimeSupport",
    "Part3LiteralReciprocalSource",
    "Part3FixedRhoPrimaryFiniteCore",
    "Part3PrimaryDyadicShortEndpoint",
    "Part3PrimaryDyadicAssembly",
    "Part3ActualNonzeroSourceCore",
    "Part3PrimaryDyadicActualMode",
    "Part3PrimaryDyadicCommonAssembly",
    "Part3ActualCompletedSourceLanes",
    "Part3ActualModeCommonPoissonLanes",
))
ACTUAL_SOURCE_LANES_DOCS = "docs/part3-distribution/p31-actual-source-lanes-20261126"
SMOOTH_MASS_LANES_MODULES = tuple("ImbalancedChen." + name for name in (
    "Part3ActualPositiveLatticeSmoothCore",
    "Part3ActualSmoothMassCompletion",
    "Part3ActualSmoothMassCommonLanes",
))
SMOOTH_MASS_LANES_DOCS = "docs/part3-distribution/p31-smooth-mass-lanes-20261127"
MODULES = PROPER_POWER_MODULES + SPECTRAL_MODULES + INTERFACE_MODULES
GROUPS = {"all": MODULES, "proper-power": PROPER_POWER_MODULES,
          "spectral": SPECTRAL_MODULES,
          "interface": INTERFACE_MODULES,
          "actual-interface": ACTUAL_INTERFACE_MODULES,
          "poisson-lanes": POISSON_LANES_MODULES,
          "shiu-windows": SHIU_WINDOWS_MODULES,
          "poisson-kernel-lanes": KERNEL_LANES_MODULES,
          "actual-source-lanes": ACTUAL_SOURCE_LANES_MODULES,
          "smooth-mass-lanes": SMOOTH_MASS_LANES_MODULES,
          "chart-sum": ("ImbalancedChen.Part3ProperPowerLogSaving",
                        "ImbalancedChen.Part3ProperPowerChartSum"),
          "actual-pair": ("ImbalancedChen.FiniteUpperCarrierCore",
                          "ImbalancedChen.Part3ProperPowerActualPair"),
          "actual-pair-family": ("ImbalancedChen.Part3ProperPowerActualPairFamily",)}
PROFILE_REUSE_MANIFEST = (
    "docs/part3-distribution/continuation-20261124/actual-pair-reuse/SOURCE_MANIFEST.json"
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


# Reused source/object closure gates from accepted P3.2 commit 30e2a96b.
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def source_imports(text: str, source: str) -> tuple[str, ...]:
    """Read the closure's ordinary import headers with the existing Lean lexer.

    Unsupported header syntax fails closed instead of silently dropping an edge.
    Comments and string contents are removed by the same lexer as the source gate.
    """
    imports: list[str] = []
    for line in baseline.lean_code(text).splitlines():
        words = line.split()
        if not words:
            continue
        if words[0] != "import":
            if (words[0] in {"prelude", "module", "public", "private", "meta", "all"}
                    or (len(words) == 1 and MODULE_NAME.fullmatch(words[0])
                        and words[0] not in {"section", "noncomputable", "mutual"})):
                raise RuntimeError("Unsupported Lean import header: " + source)
            break
        names = words[1:]
        if not names or any(not MODULE_NAME.fullmatch(name)
                            or name in {"import", "all", "public", "meta", "prelude", "module"}
                            for name in names):
            raise RuntimeError("Unsupported Lean import header: " + source)
        imports.extend(names)
    if len(imports) != len(set(imports)):
        raise RuntimeError("Duplicate Lean import: " + source)
    return tuple(imports)


def validate_project_closure(root: Path, closure: dict,
                             targets: tuple[str, ...]) -> tuple[str, ...]:
    """Recompute reachable local sources independently of the claimed inventory."""
    if closure.get("targets") != list(targets):
        raise RuntimeError("P3.1 closure targets differ from the selected terminal gate")
    if closure.get("full_external_kernel_replay_claimed") is not False:
        raise RuntimeError("P3.1 closure must not claim full external kernel replay")
    listed = {}
    entries = closure.get("project_sources")
    if not isinstance(entries, list):
        raise RuntimeError("Invalid P3.1 project source inventory")
    for item in entries:
        if not isinstance(item, dict):
            raise RuntimeError("Invalid P3.1 project source record")
        module = item.get("module")
        if not isinstance(module, str) or not MODULE_NAME.fullmatch(module):
            raise RuntimeError("Invalid P3.1 project module: " + repr(module))
        if module in listed:
            raise RuntimeError("Duplicate P3.1 project source: " + module)
        relative = module.replace(".", "/") + ".lean"
        if item.get("path") != relative:
            raise RuntimeError("Invalid P3.1 source path: " + repr(item.get("path")))
        imports = item.get("imports")
        if (not isinstance(imports, list)
                or any(not isinstance(name, str) or not MODULE_NAME.fullmatch(name)
                       for name in imports)
                or len(imports) != len(set(imports))):
            raise RuntimeError("Invalid or duplicate P3.1 imports: " + module)
        listed[module] = item

    actual = {}
    external: set[str] = set()
    pending = list(targets)
    while pending:
        module = pending.pop()
        if module in actual:
            continue
        relative = module.replace(".", "/") + ".lean"
        path = root / relative
        if not path.is_file():
            raise RuntimeError("Missing P3.1 project source: " + relative)
        data = path.read_bytes()
        imports = source_imports(data.decode("utf-8"), relative)
        actual[module] = {"path": relative, "imports": list(imports),
                          "sha256": hashlib.sha256(data).hexdigest()}
        for imported in imports:
            local = root / (imported.replace(".", "/") + ".lean")
            if local.is_file() or imported == "ImbalancedChen" or imported.startswith("ImbalancedChen."):
                pending.append(imported)
            else:
                external.add(imported)

    if actual.keys() != listed.keys():
        raise RuntimeError("P3.1 project closure differs: missing="
                           + repr(sorted(actual.keys() - listed.keys()))
                           + "; extra=" + repr(sorted(listed.keys() - actual.keys())))
    if (type(closure.get("project_module_count")) is not int
            or closure["project_module_count"] != len(actual)):
        raise RuntimeError("P3.1 project module count differs from the recomputed closure")
    for module, observed in actual.items():
        if listed[module]["imports"] != observed["imports"]:
            raise RuntimeError("P3.1 source imports differ: " + module)
        if listed[module].get("sha256") != observed["sha256"]:
            raise RuntimeError("P3.1 import source changed: " + observed["path"])
    claimed_external = closure.get("external_imports")
    if (not isinstance(claimed_external, list)
            or any(not isinstance(name, str) or not MODULE_NAME.fullmatch(name)
                   for name in claimed_external)
            or len(claimed_external) != len(set(claimed_external))
            or set(claimed_external) != external):
        raise RuntimeError("P3.1 external import inventory differs from the recomputed closure")
    return tuple(sorted(actual))


def snapshot_project_objects(root: Path, roots: list[Path],
                             modules: tuple[str, ...]) -> dict:
    """Bind actual import resolution and the complete existing object-part set."""
    root = root.resolve()
    objdir = (root / ".lake/build/lib/lean").resolve()
    if not objdir.is_relative_to(root):
        raise RuntimeError("P3.1 project object directory resolves outside this checkout")
    bindings = {}
    for module in modules:
        relative = module.replace(".", "/") + ".olean"
        obj = objdir / relative
        resolved = next((directory / relative for directory in roots
                         if (directory / relative).is_file()), None)
        if resolved is None or resolved.resolve() != obj:
            raise RuntimeError("Lake resolves a P3.1 project module outside the verified object tree: " + module)
        parts = {}
        for suffix in ("", ".server", ".private"):
            part = Path(str(obj) + suffix)
            if not part.exists() and not part.is_symlink():
                continue
            if not part.is_file() or part.resolve() != part:
                raise RuntimeError("Invalid P3.1 project object part: " + str(part))
            parts[part.relative_to(root).as_posix()] = sha256(part)
        bindings[module] = {"resolved_olean": str(obj), "parts": parts}
    return bindings


def require_frozen_project_objects(before: dict, after: dict,
                                   mutable_modules: tuple[str, ...] = ()) -> None:
    """Allow strict recompilation only for selected terminals, never providers."""
    if before.keys() != after.keys():
        raise RuntimeError("P3.1 project object snapshot module set changed")
    mutable = set(mutable_modules)
    changed = sorted(module for module in before
                     if module not in mutable and before[module] != after[module])
    if changed:
        raise RuntimeError("P3.1 project object resolution, parts or hashes changed: " + repr(changed))


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
        paths = [ROOT / (m.replace(".", "/") + ".lean")
                 for m in dict.fromkeys(MODULES + modules)]
        closure_modules: tuple[str, ...] = ()
        if args.group == "actual-interface":
            closure_manifest = ROOT / ACTUAL_INTERFACE_DOCS / "CLOSURE.json"
            closure = json.loads(closure_manifest.read_text())
            closure_modules = validate_project_closure(ROOT, closure, ACTUAL_INTERFACE_ENTRY)
            paths += [ROOT / (m.replace(".", "/") + ".lean") for m in closure_modules]
            paths += [closure_manifest, ROOT / ACTUAL_INTERFACE_DOCS / "REUSE_SOURCES.json",
                      ROOT / ACTUAL_INTERFACE_DOCS / "HISTORICAL_REUSE.json",
                      ROOT / "verification/test_part3_source_object_gate.py"]
            actual_reuse = json.loads((ROOT / ACTUAL_INTERFACE_DOCS / "REUSE_SOURCES.json").read_text())
            for item in actual_reuse["restored_exact_sources"]:
                if item["path"] != item["module"].replace(".", "/") + ".lean":
                    raise RuntimeError("Invalid actual packet donor source path")
                if sha256(ROOT / item["path"]) != item["sha256"]:
                    raise RuntimeError("Actual packet donor source changed: " + item["path"])
            report["project_import_closure"] = closure
            report["exact_source_reuse"] = actual_reuse
        elif args.group == "poisson-lanes":
            closure_manifest = ROOT / POISSON_LANES_DOCS / "CLOSURE.json"
            intake_manifest = ROOT / POISSON_LANES_DOCS / "SOURCE_INTAKE.json"
            closure = json.loads(closure_manifest.read_text())
            closure_modules = validate_project_closure(ROOT, closure, POISSON_LANES_MODULES)
            intake = json.loads(intake_manifest.read_text())
            relative = POISSON_LANES_MODULES[0].replace(".", "/") + ".lean"
            if intake.get("path") != relative or intake.get("module") != POISSON_LANES_MODULES[0]:
                raise RuntimeError("Recovered Poisson source identity changed")
            source = ROOT / relative
            if sha256(source) != intake.get("source_sha256"):
                raise RuntimeError("Recovered Poisson source changed")
            text = source.read_text()
            for segment in intake["segments"]:
                label = segment["label"]
                begin, end = "-- BEGIN recovered " + label + "\n", "-- END recovered " + label + "\n"
                if text.count(begin) != 1 or text.count(end) != 1:
                    raise RuntimeError("Recovered Poisson source segment is not unique: " + label)
                body = text.split(begin, 1)[1].split(end, 1)[0]
                if hashlib.sha256(body.encode()).hexdigest() != segment["staged_sha256"]:
                    raise RuntimeError("Recovered Poisson source segment changed: " + label)
                if not segment["mechanical_repairs"] and segment["staged_sha256"] != segment["original_sha256"]:
                    raise RuntimeError("Unrecorded Poisson source repair: " + label)
            supplier = intake["physical_supplier"]
            if sha256(ROOT / supplier["path"]) != supplier["sha256"]:
                raise RuntimeError("Accepted Physical Poisson supplier changed")
            paths += [ROOT / (m.replace(".", "/") + ".lean") for m in closure_modules]
            paths += [closure_manifest, intake_manifest,
                      ROOT / "verification/test_part3_source_object_gate.py"]
            report["project_import_closure"] = closure
            report["source_intake"] = intake
        elif args.group == "actual-source-lanes":
            closure_manifest = ROOT / ACTUAL_SOURCE_LANES_DOCS / "PROJECT_IMPORT_CLOSURE.json"
            intake_manifest = ROOT / ACTUAL_SOURCE_LANES_DOCS / "SOURCE_INTAKE.json"
            closure = json.loads(closure_manifest.read_text())
            closure_modules = validate_project_closure(ROOT, closure, ACTUAL_SOURCE_LANES_MODULES)
            intake = json.loads(intake_manifest.read_text())
            if [item.get("module") for item in intake.get("sources", [])] != list(ACTUAL_SOURCE_LANES_MODULES):
                raise RuntimeError("Actual source lane identities differ from selected modules")
            for item in intake["sources"]:
                relative = item["module"].replace(".", "/") + ".lean"
                if item.get("path") != relative or sha256(ROOT / relative) != item.get("sha256"):
                    raise RuntimeError("Actual source lane changed: " + relative)
            recovered_module = "ImbalancedChen.Part3ActualCompletedSourceLanes"
            labels = ("completed_piece", "signed_y_sources", "zero_nonzero_source_split",
                      "positive_negative_source_split", "completed_source_bridges")
            if [(item.get("module"), item.get("label")) for item in intake.get("segments", [])] != [
                    (recovered_module, label) for label in labels]:
                raise RuntimeError("Actual source lane recovered segment identities changed")
            text = (ROOT / (recovered_module.replace(".", "/") + ".lean")).read_text()
            for segment in intake["segments"]:
                label = segment["label"]
                begin, end = "-- BEGIN recovered " + label + "\n", "-- END recovered " + label + "\n"
                if text.count(begin) != 1 or text.count(end) != 1:
                    raise RuntimeError("Actual source lane segment is not unique: " + label)
                body = text.split(begin, 1)[1].split(end, 1)[0]
                if hashlib.sha256(body.encode()).hexdigest() != segment["staged_sha256"]:
                    raise RuntimeError("Actual source lane segment changed: " + label)
                if not segment["mechanical_repairs"] and segment["staged_sha256"] != segment["original_sha256"]:
                    raise RuntimeError("Unrecorded actual source lane repair: " + label)
            providers = intake["provider_sources"]
            provider_modules = [item.get("module") for item in providers]
            required_providers = {"ImbalancedChen.Part3ActualReciprocalSquarePoissonCore",
                                  "ImbalancedChen.Part3OriginalCommonPoissonKernelLanesCore"}
            if (len(provider_modules) != len(set(provider_modules))
                    or not required_providers.issubset(provider_modules)):
                raise RuntimeError("Actual source lane accepted provider identities changed")
            for supplier in providers:
                module = supplier["module"]
                if module not in closure_modules or module in ACTUAL_SOURCE_LANES_MODULES:
                    raise RuntimeError("Invalid actual source lane accepted provider: " + str(module))
                relative = module.replace(".", "/") + ".lean"
                if supplier.get("path") != relative or sha256(ROOT / relative) != supplier.get("sha256"):
                    raise RuntimeError("Accepted actual source lane provider changed: " + relative)
            paths += [ROOT / (m.replace(".", "/") + ".lean") for m in closure_modules]
            paths += [closure_manifest, intake_manifest,
                      ROOT / "verification/test_part3_source_object_gate.py"]
            report["scope"] = ("Actual finite-source common-J integration, including reused suppliers; "
                               "not a certificate of OriginalData, sixSmoothMass or the whole P3.1 target")
            report["reused_supplier_modules"] = list(ACTUAL_SOURCE_LANES_MODULES[:-2])
            report["new_consumer_modules"] = list(ACTUAL_SOURCE_LANES_MODULES[-2:])
            report["project_import_closure"] = closure
            report["source_intake"] = intake
        elif args.group == "smooth-mass-lanes":
            closure_manifest = ROOT / SMOOTH_MASS_LANES_DOCS / "PROJECT_IMPORT_CLOSURE.json"
            intake_manifest = ROOT / SMOOTH_MASS_LANES_DOCS / "SOURCE_INTAKE.json"
            fragment_manifest = ROOT / SMOOTH_MASS_LANES_DOCS / "SOURCE_FRAGMENTS.json"
            closure = json.loads(closure_manifest.read_text())
            closure_modules = validate_project_closure(ROOT, closure, SMOOTH_MASS_LANES_MODULES)
            intake = json.loads(intake_manifest.read_text())
            fragments = json.loads(fragment_manifest.read_text())
            if [item.get("module") for item in intake.get("sources", [])] != list(SMOOTH_MASS_LANES_MODULES):
                raise RuntimeError("Smooth mass lane identities differ from selected modules")
            source_bytes = {}
            for item in intake["sources"]:
                relative = item["module"].replace(".", "/") + ".lean"
                if item.get("path") != relative or sha256(ROOT / relative) != item.get("sha256"):
                    raise RuntimeError("Smooth mass lane source changed: " + relative)
                source_bytes[item["module"]] = (ROOT / relative).read_bytes()
            original_pins = {
                "cover": ("Part3ActualPositiveLatticeSmoothCover.lean.txt", 24631,
                          "6e4dbe90aa13cdd346bb93589733d6469a96d60cdf50c6df33a5c46971821da9",
                          "a094a3dcd2b43124f42e8219e2b1b6ef9ac26cb4"),
                "square": ("Part3ActualReciprocalSquarePoisson.lean.txt", 21826,
                           "4dd4d1487658283645a8c7857864df5448deb665828ac7c4a6cade294872b60e",
                           "58e9a86e0bd60aee30ebc7a15c781f2dd96a49c9"),
                "matcher": ("Part3ActualSeparatedRowFiniteMatcher.lean.txt", 116891,
                            "c668788542424f65003dec6586af9aee814b4e9f4fd7246714eec7815b1f1fe0",
                            "c90d4709b3dde3704006ddb8b959c5dc85bcb60a"),
            }
            originals = intake.get("original_sources", [])
            original_ids = [item.get("id") for item in originals]
            if (len(original_ids) != len(original_pins)
                    or len(original_ids) != len(set(original_ids))
                    or set(original_ids) != set(original_pins)):
                raise RuntimeError("Smooth mass lane original source identities changed")
            original_bytes = {}
            archive_paths = []
            for item in originals:
                name, size, digest, blob = original_pins[item["id"]]
                relative = SMOOTH_MASS_LANES_DOCS + "/upstream/" + name
                if (item.get("archive_path") != relative or item.get("bytes") != size
                        or item.get("sha256") != digest or item.get("git_blob") != blob):
                    raise RuntimeError("Smooth mass lane original source pin changed: " + item["id"])
                path = ROOT / relative
                data = path.read_bytes()
                observed_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
                if (len(data) != size or hashlib.sha256(data).hexdigest() != digest
                        or observed_blob != blob):
                    raise RuntimeError("Smooth mass lane original archive changed: " + relative)
                original_bytes[item["id"]] = data
                archive_paths.append(path)
            expected_segments = [
                (SMOOTH_MASS_LANES_MODULES[0], label, source_id) for label, source_id in (
                    ("tight_real_support", "cover"),
                    ("tight_schwartz_support", "cover"),
                    ("tight_nonzero_support", "cover"),
                    ("nonpositive_argument_zero", "cover"),
                    ("physical_nonzero_bounds", "cover"),
                    ("physical_nonpositive_scale", "cover"),
                    ("physical_nonzero_nonnegative_modulus", "cover"),
                    ("physical_nonzero_natural_modulus", "cover"),
                    ("original_packet_alias", "matcher"),
                    ("original_packet_box", "cover"),
                    ("original_smooth_mass", "cover"),
                    ("original_six_smooth_mass", "cover"),
                    ("original_smooth_mass_lattice", "cover"),
                )
            ] + [
                (SMOOTH_MASS_LANES_MODULES[1], label, "square") for label in (
                    "original_inner_gate", "original_finite_row", "original_row_atoms",
                    "original_full_b_support", "original_smooth_mass_gated_squares",
                    "original_smooth_mass_completed_pairs", "original_six_smooth_mass_completed",
                )
            ]
            segments = intake.get("segments", [])
            if [(item.get("module"), item.get("label"), item.get("source_id"))
                    for item in segments] != expected_segments:
                raise RuntimeError("Smooth mass lane recovered segment identities changed")
            if fragments.get("fragments") != segments:
                raise RuntimeError("Smooth mass lane fragment manifest differs from the intake")
            for module, data in source_bytes.items():
                labels = [label.encode() for owner, label, _ in expected_segments if owner == module]
                for marker in (b"BEGIN", b"END"):
                    observed = re.findall(rb"(?m)^-- " + marker + rb" recovered ([a-z0-9_]+)\n", data)
                    if observed != labels:
                        raise RuntimeError("Smooth mass lane marker inventory changed: " + module)
            adapter_label = "original_smooth_mass_completed_pairs"
            adapter_note = (
                "Replace only the old specialized b-Poisson invocation with the already-owned generic "
                "theorem at the original finite b carrier, supplying full_b_support and rewriting "
                "reciprocalRow via finiteRow_eq_atoms. The original theorem statement is unchanged."
            )
            old_call = (
                "  · rw [if_pos hfn, if_pos hfn, reciprocal_square_b_poisson (c := c) hM hMB]\n"
            ).encode()
            new_call = (
                "  · rw [if_pos hfn, if_pos hfn]\n"
                "    apply congrArg (fun z : ℂ => (scaledDyadicCutoff N c : ℂ) * z)\n"
                "    simpa only [reciprocalRow, ← finiteRow_eq_atoms] using\n"
                "      reciprocal_square_b_poisson (c := c) hM\n"
                "        (Ioc 0 (Nat.floor (5*B))) (full_b_support hM hMB)\n"
                "        A a (finiteInnerCarrier T H) lambda omega f\n"
            ).encode()
            exact_count = adapted_count = 0
            for segment in segments:
                label, module, source_id = segment["label"], segment["module"], segment["source_id"]
                data = source_bytes[module]
                begin = ("-- BEGIN recovered " + label + "\n").encode()
                end = ("-- END recovered " + label + "\n").encode()
                if (data.count(begin) != 1 or data.count(end) != 1
                        or data.index(begin) + len(begin) >= data.index(end)):
                    raise RuntimeError("Smooth mass lane segment is not uniquely delimited: " + label)
                body = data.split(begin, 1)[1].split(end, 1)[0]
                if hashlib.sha256(body).hexdigest() != segment.get("staged_sha256"):
                    raise RuntimeError("Smooth mass lane recovered segment changed: " + label)
                offset, size = segment.get("original_byte_offset"), segment.get("original_bytes")
                original = original_bytes[source_id]
                if (type(offset) is not int or type(size) is not int or offset < 0 or size <= 0
                        or offset + size > len(original)):
                    raise RuntimeError("Smooth mass lane original byte range is invalid: " + label)
                original = original[offset:offset + size]
                if (hashlib.sha256(original).hexdigest() != segment.get("original_sha256")
                        or segment.get("original_blob") != original_pins[source_id][3]):
                    raise RuntimeError("Smooth mass lane original fragment changed: " + label)
                if label == adapter_label:
                    if (segment.get("mechanical_repairs") != [adapter_note]
                            or segment.get("byte_exact") is not False
                            or original.count(old_call) != 1
                            or body != original.replace(old_call, new_call, 1)):
                        raise RuntimeError("Smooth mass lane adapter exceeds the recorded invocation: " + label)
                    adapted_count += 1
                else:
                    if (segment.get("mechanical_repairs") != []
                            or segment.get("byte_exact") is not True or body != original):
                        raise RuntimeError("Unrecorded smooth mass lane source repair: " + label)
                    exact_count += 1
            if (exact_count, adapted_count) != (19, 1):
                raise RuntimeError("Smooth mass lane recovered/adapted accounting changed")
            providers = intake.get("provider_sources", [])
            provider_modules = [item.get("module") for item in providers]
            required_providers = {"ImbalancedChen.Part3ActualCompletedSourceLanes",
                                  "ImbalancedChen.Part3ActualModeCommonPoissonLanes"}
            if (len(provider_modules) != len(set(provider_modules))
                    or not required_providers.issubset(provider_modules)):
                raise RuntimeError("Smooth mass lane accepted provider identities changed")
            for supplier in providers:
                module = supplier["module"]
                if module not in closure_modules or module in SMOOTH_MASS_LANES_MODULES:
                    raise RuntimeError("Invalid smooth mass lane accepted provider: " + str(module))
                relative = module.replace(".", "/") + ".lean"
                if supplier.get("path") != relative or sha256(ROOT / relative) != supplier.get("sha256"):
                    raise RuntimeError("Accepted smooth mass lane provider changed: " + relative)
            paths += [ROOT / (m.replace(".", "/") + ".lean") for m in closure_modules]
            paths += [closure_manifest, intake_manifest, fragment_manifest, *archive_paths,
                      ROOT / "verification/test_part3_source_object_gate.py"]
            report["scope"] = ("Actual smoothMass/sixSmoothMass finite common-J integration: "
                               "two recovered supplier modules and one new composition consumer; "
                               "not OriginalData/FixedBlock, a global cutoff or zero/tail estimate, "
                               "external spectral J/A, or the whole P3.1 target")
            report["recovered_supplier_modules"] = list(SMOOTH_MASS_LANES_MODULES[:2])
            report["new_consumer_modules"] = list(SMOOTH_MASS_LANES_MODULES[2:])
            report["recovered_fragment_accounting"] = {"byte_exact": exact_count, "adapted_invocation": adapted_count}
            report["project_import_closure"] = closure
            report["source_intake"] = intake
            report["source_fragments"] = fragments
        elif args.group == "shiu-windows":
            closure_manifest = ROOT / SHIU_WINDOWS_DOCS / "CLOSURE.json"
            intake_manifest = ROOT / SHIU_WINDOWS_DOCS / "SOURCE_INTAKE.json"
            closure = json.loads(closure_manifest.read_text())
            closure_modules = validate_project_closure(ROOT, closure, SHIU_WINDOWS_MODULES)
            intake = json.loads(intake_manifest.read_text())
            if [item.get("module") for item in intake.get("sources", [])] != list(SHIU_WINDOWS_MODULES):
                raise RuntimeError("Shiu window source identities differ from selected modules")
            for item in intake["sources"]:
                relative = item["module"].replace(".", "/") + ".lean"
                if item.get("path") != relative or sha256(ROOT / relative) != item.get("sha256"):
                    raise RuntimeError("Shiu window source changed: " + relative)
            paths += [ROOT / (m.replace(".", "/") + ".lean") for m in closure_modules]
            paths += [closure_manifest, intake_manifest,
                      ROOT / "verification/test_part3_source_object_gate.py"]
            report["project_import_closure"] = closure
            report["source_intake"] = intake
        elif args.group == "poisson-kernel-lanes":
            closure_manifest = ROOT / KERNEL_LANES_DOCS / "CLOSURE.json"
            intake_manifest = ROOT / KERNEL_LANES_DOCS / "SOURCE_INTAKE.json"
            closure = json.loads(closure_manifest.read_text())
            closure_modules = validate_project_closure(ROOT, closure, KERNEL_LANES_MODULES)
            intake = json.loads(intake_manifest.read_text())
            relative = KERNEL_LANES_MODULES[0].replace(".", "/") + ".lean"
            if intake.get("path") != relative or intake.get("module") != KERNEL_LANES_MODULES[0]:
                raise RuntimeError("Physical kernel lane source identity changed")
            source = ROOT / relative
            if sha256(source) != intake.get("source_sha256"):
                raise RuntimeError("Physical kernel lane source changed")
            text = source.read_text()
            for segment in intake["segments"]:
                label = segment["label"]
                begin, end = "-- BEGIN recovered " + label + "\n", "-- END recovered " + label + "\n"
                if text.count(begin) != 1 or text.count(end) != 1:
                    raise RuntimeError("Physical kernel source segment is not unique: " + label)
                body = text.split(begin, 1)[1].split(end, 1)[0]
                if hashlib.sha256(body.encode()).hexdigest() != segment["staged_sha256"]:
                    raise RuntimeError("Physical kernel source segment changed: " + label)
                if not segment["mechanical_repairs"] and segment["staged_sha256"] != segment["original_sha256"]:
                    raise RuntimeError("Unrecorded physical kernel source repair: " + label)
            for supplier in intake["provider_sources"]:
                if sha256(ROOT / supplier["path"]) != supplier["sha256"]:
                    raise RuntimeError("Accepted physical kernel supplier changed: " + supplier["path"])
            paths += [ROOT / (m.replace(".", "/") + ".lean") for m in closure_modules]
            paths += [closure_manifest, intake_manifest,
                      ROOT / "verification/test_part3_source_object_gate.py"]
            report["project_import_closure"] = closure
            report["source_intake"] = intake
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
        if args.group == "interface":
            paths.append(ROOT / ".github/workflows/p3-1-interface.yml")
        hashes = {p.relative_to(ROOT).as_posix(): sha256(p) for p in paths}
        if closure_modules and any(hashes[item["path"]] != item["sha256"]
                                   for item in closure["project_sources"]):
            raise RuntimeError("P3.1 sources changed after import closure validation")
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
        if closure_modules:
            run([sys.executable, "-B", "verification/test_part3_source_object_gate.py"],
                "source-object-gate-regressions")
        run(["lake", "build", *modules], "build-new-targets")
        if args.group == "actual-interface":
            run(["lake", "build", *ACTUAL_INTERFACE_ENTRY], "build-node31-composition")
        objdir = ROOT / ".lake/build/lib/lean"
        roots = [(ROOT / p).resolve() for p in tools["lean_path"].split(":") if p]
        if closure_modules:
            initial_bindings = snapshot_project_objects(ROOT, roots, closure_modules)
            report["project_object_binding"] = {
                "scope": "Full project source and resolved object binding; only new consumer replayed",
                "project_module_count": len(closure_modules),
                "strict_recompile_targets": list(modules),
                "kernel_replay_targets": list(modules),
                "all_historical_providers_kernel_replayed": False,
                "after_build": initial_bindings,
            }
            save()
        else:
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
        if closure_modules:
            strict_bindings = snapshot_project_objects(ROOT, roots, closure_modules)
            require_frozen_project_objects(initial_bindings, strict_bindings, mutable_modules=modules)
            report["project_object_binding"].update(
                after_strict=strict_bindings, providers_unchanged_during_strict=True)
            save()
        for module in modules:
            replay = run(["lake", "env", tools["leanchecker"], "--verbose", module],
                         module.rsplit(".", 1)[1] + "-replay")
            if "replaying " + module not in replay.splitlines():
                raise RuntimeError("Missing module replay evidence: " + module)
        log = run(["lake", "env", tools["lean"], "-t0", "-j1", "-DwarningAsError=true",
                   str(audit)], "axioms")
        records, counts = baseline.validate_inventory(log, modules=modules)
        if closure_modules:
            final_bindings = snapshot_project_objects(ROOT, roots, closure_modules)
            require_frozen_project_objects(strict_bindings, final_bindings)
            report["project_object_binding"]["all_project_objects_unchanged_after_audit"] = True
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
