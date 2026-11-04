#!/usr/bin/env python3
"""Export exact Round 3 types from existing objects after a successful full build.

This compiles only Round3Audit.lean. It does not build dependencies, bootstrap a
toolchain, rebuild production modules, or invoke a kernel checker. The existing
full-build, kernel-replay, and axiom gates must remain required in the caller.
"""

from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parents[3]
AUDIT = "verification/parts/p0/Round3Audit.lean"
FINAL_BRIDGE = "ImbalancedChen.current_theorem_1_1_of_manuscript_bounds"
FINAL_MODULE = "ImbalancedChen.CurrentMainTheorem"
MODULES = (
    "ImbalancedChen.ActualSelectedPrefixLowerCellSum",
    "ImbalancedChen.ActualSelectedPrefixLowerOwnCubeIntegral",
    "ImbalancedChen.HistoricalPrefixCertificate",
    "ImbalancedChen.OrdinaryLowerFourFrontier",
    "ImbalancedChen.Certificates.PairedV2Geometry",
    "ImbalancedChen.Certificates.PairedV2Prefix4Data",
    "ImbalancedChen.Certificates.PairedV2Prefix4",
    "ImbalancedChen.Part3LongSlotNormalization",
    "ImbalancedChen.FinitePrimeGeometryCore",
)
HISTORICAL_BASELINE = "verification/parts/p0/round3-declaration-baseline.json"
HISTORICAL_BASELINE_SHA256 = "a5188b7cb17767f1b0d5e40d08d5a2078e08ca89a19b750f1c605bc823eef299"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FROZEN = {
    "ImbalancedChen/ActualSelectedPrefixLowerCellSum.lean": "48b9b1b50d1fec780378e61a5250971cf0f5222b12fcf04706ad357f90040714",
    "ImbalancedChen/ActualSelectedPrefixLowerOwnCubeIntegral.lean": "c98fd3407d59f27cd140689de36f888cfd804130dc9787e3e60ea451b4e1dcd1",
    "ImbalancedChen/HistoricalPrefixCertificate.lean": "b66bb9aae758648095779c507a20172e8ef9eee3f9647bf8c0b847c8a28ccfa9",
    "ImbalancedChen/OrdinaryLowerFourFrontier.lean": "97f5e3390d9c90a9598a7fa5fa1ede84c174da9497f23c88be6ea04ffb0bc9e8",
    "ImbalancedChen/Certificates/PairedV2Geometry.lean": "68b17d29089e7a761428ff92957a7f8fbe9a4b3bff8105846717162867359238",
    "ImbalancedChen/Certificates/PairedV2Prefix4Data.lean": "25ffbba57b5fdff9ce23290ade00fbeaa2b38c2e44ffe9e8637404c8287aab2c",
    "ImbalancedChen/Certificates/PairedV2Prefix4.lean": "dc57cd323ba3cad0ca4b0d29d2c0839b4c0d90a87d7f27b497eac51587295395",
    "ImbalancedChen/Part3LongSlotNormalization.lean": "ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc",
    "ImbalancedChen/FinitePrimeGeometryCore.lean": "becd322d719aa8ae9f0cc7b3bedbc19b87edd347bbc79788ce8f6ca7e5694d85",
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
    "verification/parts/p0/round3-declaration-baseline.json": "a5188b7cb17767f1b0d5e40d08d5a2078e08ca89a19b750f1c605bc823eef299",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def historical_baseline() -> dict[str, dict]:
    path = ROOT / HISTORICAL_BASELINE
    require(digest(path) == HISTORICAL_BASELINE_SHA256,
            "Historical declaration baseline changed")
    baseline = json.loads(path.read_text(encoding="utf-8"))
    require(baseline.get("schema") == "p0-round3-historical-declarations-v1",
            "Wrong historical declaration baseline schema")
    rows = baseline.get("declarations")
    require(isinstance(rows, list) and len(rows) == 198,
            "Incomplete historical declaration baseline")
    require(len({row["name"] for row in rows}) == 198,
            "Duplicate historical declaration baseline name")
    require(sum(row["historical_module"] != row["expected_module"] for row in rows) == 39,
            "Wrong historical declaration migration count")
    return {row["name"]: row for row in rows}


def verify_frozen_inputs() -> None:
    for relative, expected in FROZEN.items():
        require(digest(ROOT / relative) == expected, f"Frozen input changed: {relative}")


def write_json(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def source_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def object_parts(main: Path) -> dict[str, str]:
    require(main.is_file() and main.stat().st_size > 0, f"Missing compiled object: {main}")
    parts = [main, *main.parent.glob(main.name + ".*")]
    return {str(path.relative_to(ROOT)): digest(path)
            for path in sorted(parts) if path.is_file()}


def input_snapshot() -> dict:
    # Reuse the established comment/string masker for direct project imports.
    sys.path.insert(0, str(ROOT))
    from verification.verify_variable_envelope_boxes import lean_code

    modules = set(MODULES) | {"ImbalancedChen", FINAL_MODULE}
    for module in sorted(modules.copy()):
        text = lean_code(source_path(module).read_text())
        for line in text.splitlines():
            if line.strip().startswith("import "):
                for imported in line.strip().split()[1:]:
                    if imported == "ImbalancedChen" or imported.startswith("ImbalancedChen."):
                        modules.add(imported)
    sources = {source_path(module).relative_to(ROOT).as_posix() for module in modules}
    sources.update(FROZEN)
    sources.update({AUDIT, "verification/parts/p0/check_round3_types.py",
                    "verification/parts/p0/check_pins.py",
                    "verification/verify_variable_envelope_boxes.py"})
    git("ls-files", "--error-unmatch", "--", *sorted(sources))
    require(not git("status", "--porcelain", "--", *sorted(sources)),
            "An audited input is edited, staged, or untracked")
    return {
        "source_sha256": {relative: digest(ROOT / relative) for relative in sorted(sources)},
        "production_olean_parts": {
            module: object_parts(ROOT / ".lake/build/lib/lean" /
                                 (module.replace(".", "/") + ".olean"))
            for module in sorted(modules)
        },
    }


def parse_types(stdout: str) -> tuple[list[dict], dict, list[dict]]:
    lines = stdout.splitlines()

    def records(prefix: str) -> list[dict]:
        found = [json.loads(line.removeprefix(prefix))
                 for line in lines if line.startswith(prefix)]
        require(all(isinstance(record, dict) for record in found),
                f"Malformed JSON record: {prefix.strip()}")
        return found

    def unique_module_records(records_: list[dict], label: str) -> dict[str, dict]:
        require(len(records_) == len(MODULES), f"Missing or duplicate {label} module record")
        names = [record.get("module") for record in records_]
        require(all(isinstance(name, str) for name in names), f"Malformed {label} module name")
        require(len(set(names)) == len(MODULES) and set(names) == set(MODULES),
                f"Missing, duplicate, or unexpected {label} module")
        return {record["module"]: record for record in records_}

    declarations = records("P0_ROUND3_DECL ")
    modules = unique_module_records(records("P0_ROUND3_MODULE "), "census")
    serialized = records("P0_ROUND3_SERIALIZED ")
    inventories = unique_module_records(serialized, "serialized")
    bridges = records("P0_ROUND3_FINAL_BRIDGE ")
    totals = [int(line.removeprefix("P0_ROUND3_COUNT ")) for line in lines
              if line.startswith("P0_ROUND3_COUNT ")]
    require(len(totals) == 1 and totals[0] > 0 and totals[0] == len(declarations),
            "Missing, duplicate, or inconsistent total census marker")
    require(all(isinstance(d.get("name"), str) and d["name"] for d in declarations),
            "Missing or malformed declaration name")
    names = [d["name"] for d in declarations]
    require(len(set(names)) == len(names), "Duplicate declaration name")
    require(all(d.get("module") in MODULES for d in declarations),
            "Declaration belongs to an unexpected defining module")
    by_name = {d["name"]: d for d in declarations}
    actual_counts = Counter(d["module"] for d in declarations)
    require(set(actual_counts) == set(MODULES), "An audited module has no declarations")
    owned_union: set[str] = set()
    expected_occurrences: dict[tuple[str, str], bool] = {}

    def name_list(value: object, label: str, *, allow_empty: bool = False) -> list[str]:
        require(isinstance(value, list) and (allow_empty or bool(value))
                and all(isinstance(name, str) and name for name in value),
                f"Missing or malformed {label}")
        require(len(set(value)) == len(value), f"Duplicate {label}")
        return value

    for module in MODULES:
        inventory = inventories[module]
        require(inventory.get("is_module") is False
                and inventory.get("import_all") is True and inventory.get("has_data") is True,
                f"Incomplete legacy serialized module data: {module}")
        serialized_names = name_list(inventory.get("serialized_constant_names"),
                                     f"serialized declaration inventory: {module}")
        environment_names = name_list(inventory.get("environment_constant_names"),
                                      f"environment declaration inventory: {module}")
        owned_names = name_list(inventory.get("owned_constant_names"),
                               f"owned declaration inventory: {module}")
        shared_names = name_list(inventory.get("shared_constant_names"),
                                f"shared declaration inventory: {module}", allow_empty=True)
        owned_set, shared_set = set(owned_names), set(shared_names)
        require(not (owned_set & shared_set)
                and set(serialized_names) == owned_set | shared_set,
                f"Serialized owned/shared partition differs: {module}")
        expected_names = {d["name"] for d in declarations if d["module"] == module}
        require(owned_set == set(environment_names) == expected_names,
                f"Owned serialized, environment, and exported declaration sets differ: {module}")
        require(not (owned_union & owned_set),
                f"A declaration has multiple audited owners: {module}")
        owned_union.update(owned_names)
        for name in serialized_names:
            expected_occurrences[module, name] = name in shared_set
        for label, count, expected_count in [
                ("serialized", inventory.get("serialized_constant_count"), len(serialized_names)),
                ("owned", inventory.get("owned_constant_count"), len(owned_names)),
                ("shared", inventory.get("shared_constant_count"), len(shared_names)),
                ("census", modules[module].get("count"), actual_counts[module])]:
            require(type(count) is int and count == expected_count,
                    f"Incorrect {label} declaration count: {module}")
        extra_count = inventory.get("extra_codegen_name_count")
        require(type(extra_count) is int and extra_count >= 0,
                f"Missing or malformed extra codegen count: {module}")
    require(owned_union == set(names) and len(owned_union) == totals[0],
            "Owned serialized union differs from the complete exported census")

    occurrences = records("P0_ROUND3_OCCURRENCE ")
    by_occurrence: dict[tuple[str, str], dict] = {}
    occurrence_identity: dict[str, tuple[str, str]] = {}
    allowed_kinds = {"theorem", "definition", "opaque", "quotient", "inductive", "constructor", "recursor"}
    identity_flags = ("type_matches_environment", "level_params_match_environment",
                      "kind_matches_environment", "all_dependencies_present")
    shared_flags = ("owner_precedes_serialized", "owner_has_serialized_theorem",
                    "type_matches_owner", "level_params_match_owner",
                    "theorem_all_matches_owner_and_environment")
    for occurrence in occurrences:
        module, name = occurrence.get("serialized_module"), occurrence.get("name")
        require(isinstance(module, str) and isinstance(name, str) and name,
                "Missing or malformed serialized occurrence identity")
        key = module, name
        require(key not in by_occurrence, f"Duplicate serialized occurrence: {module}: {name}")
        require(key in expected_occurrences, f"Unexpected serialized occurrence: {module}: {name}")
        by_occurrence[key] = occurrence
        label = f"{module}: {name}"
        owner = occurrence.get("owner_module")
        require(isinstance(owner, str) and owner, f"Missing or malformed occurrence owner: {label}")
        shared = expected_occurrences[key]
        require(occurrence.get("shared") is shared, f"Wrong occurrence shared flag: {label}")
        require((owner != module) if shared else (owner == module),
                f"Wrong serialized occurrence owner: {label}")
        if owner in MODULES:
            require(name in by_name and by_name[name]["module"] == owner,
                    f"Occurrence owner differs from exported census: {label}")
        if name in by_name:
            require(owner == by_name[name]["module"],
                    f"Occurrence owner differs from exported census: {label}")
        kind = occurrence.get("kind")
        require(isinstance(kind, str) and kind in allowed_kinds,
                f"Forbidden or missing serialized occurrence kind: {label}")
        if name in by_name:
            require(kind == by_name[name].get("kind"),
                    f"Serialized occurrence kind differs from exported declaration: {label}")
        require(name not in occurrence_identity or occurrence_identity[name] == (owner, kind),
                f"Serialized occurrences disagree on defining owner or kind: {label}")
        occurrence_identity[name] = owner, kind
        for flag in ["is_unsafe", "is_partial", "is_axiom"]:
            require(occurrence.get(flag) is False,
                    f"Unsafe, partial, axiom, or missing occurrence safety flag {flag}: {label}")
        for flag in identity_flags:
            require(occurrence.get(flag) is True,
                    f"Failed or missing occurrence validation {flag}: {label}")
        dependencies = name_list(occurrence.get("raw_dependency_names"),
                                 f"raw dependency names: {label}", allow_empty=True)
        axioms = name_list(occurrence.get("raw_dependency_axioms"),
                          f"raw dependency axioms: {label}", allow_empty=True)
        require(set(axioms) <= ALLOWED and "sorryAx" not in dependencies,
                f"Forbidden raw axiom dependency: {label}")
        require(kind != "theorem" or name not in dependencies,
                f"Direct serialized theorem self-dependency: {label}")
        expression_count = occurrence.get("raw_expression_count")
        require(type(expression_count) is int
                and expression_count == (2 if kind in {"theorem", "definition", "opaque"} else 1),
                f"Incorrect raw expression count: {label}")
        require("shared_validation" in occurrence,
                f"Missing shared validation field: {label}")
        validation = occurrence["shared_validation"]
        if shared:
            require(kind == "theorem", f"Shared serialized occurrence is not a theorem: {label}")
            require(isinstance(validation, dict), f"Missing shared theorem validation: {label}")
            for flag in shared_flags:
                require(validation.get(flag) is True,
                        f"Failed or missing shared theorem validation {flag}: {label}")
        else:
            require(validation is None, f"Owned occurrence has shared validation: {label}")
    require(set(by_occurrence) == set(expected_occurrences),
            "Missing serialized occurrence; exact serialized occurrence coverage failed")
    # Preserve the checked occurrence evidence with its module inventory in the artifact.
    for module in MODULES:
        inventories[module]["occurrences"] = [by_occurrence[module, name]
            for name in inventories[module]["serialized_constant_names"]]
    baseline = historical_baseline()
    for name, expected in baseline.items():
        require(name in by_name, f"Missing historical declaration: {name}")
        record = by_name[name]
        require(record.get("module") == expected["expected_module"]
                and record.get("kind") == expected["kind"],
                f"Wrong historical declaration owner or kind: {name}")
        type_text = record.get("type")
        require(isinstance(type_text, str)
                and hashlib.sha256(type_text.encode("utf-8")).hexdigest() == expected["type_sha256"],
                f"Historical complete type changed: {name}")
    require(len(bridges) == 1, "Expected exactly one final-bridge type record")
    bridge = bridges[0]
    require(bridge.get("name") == FINAL_BRIDGE and bridge.get("module") == FINAL_MODULE
            and bridge.get("kind") == "theorem", "Wrong final bridge")
    require(FINAL_BRIDGE not in by_name, "Final bridge counted in the owned-module census")
    allowed_kinds = {"theorem", "definition", "opaque", "quotient", "inductive", "constructor", "recursor"}
    for record in declarations + bridges:
        name = record["name"]
        require(record.get("kind") in allowed_kinds, f"Forbidden or missing declaration kind: {name}")
        for key in ["is_unsafe", "is_partial", "is_axiom"]:
            require(record.get(key) is False, f"Unsafe, partial, axiom, or missing safety flag {key}: {name}")
        axioms = record.get("axioms")
        require(isinstance(axioms, list) and all(isinstance(ax, str) for ax in axioms)
                and set(axioms) <= ALLOWED, f"Forbidden axiom dependency: {name}")
        for key in ["type", "readable_type"]:
            value = record.get(key)
            require(isinstance(value, str) and value.strip()
                    and "⋯" not in value and "…" not in value, f"Missing or truncated {key}: {name}")
    require(re.search(r"\bhLower\b", bridge["type"]) is not None
            and re.search(r"\bhUpper\b", bridge["type"]) is not None,
            "Final bridge type does not retain both hLower and hUpper hypotheses")
    return declarations, bridge, [inventories[module] for module in MODULES]


def first_diagnostic(text: str) -> dict | None:
    lines = text.splitlines()
    marker = re.compile(r"(?:^.+:\d+:\d+: error(?:\([^)]+\))?:|^error(?:\([^)]+\))?:)")
    for index, line in enumerate(lines):
        if marker.search(line):
            end = next((i for i in range(index + 1, len(lines))
                        if marker.search(lines[i])), len(lines))
            return {"line": index + 1, "text": "\n".join(lines[index:end])}
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout-seconds", type=int, default=1800)
    args = parser.parse_args()
    require(args.timeout_seconds > 0, "Timeout must be positive")
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    output = ROOT / ".lake/part0-round3-types" / stamp
    output.mkdir(parents=True, exist_ok=False)
    audit_object = output / "Round3Audit.olean"
    stdout_path, stderr_path = output / "stdout.log", output / "stderr.log"
    stdout_path.touch()
    stderr_path.touch()
    report = {
        "schema": "p0-round3-types-export-v3", "status": "RUNNING",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Supplemental type export after successful full lake build; existing proof gates remain required",
        "expected_defining_modules": list(MODULES), "required_historical_declarations": 198,
        "historical_baseline": HISTORICAL_BASELINE,
        "historical_baseline_sha256": HISTORICAL_BASELINE_SHA256,
        "migration_commit": "81b63cafb6ee00590cad194975cc140f465d68b5",
        "census_basis": "Exact serialized owned/shared partition; owned names = defining-module environment = exported declarations; every serialized occurrence audited",
        "final_bridge_name": FINAL_BRIDGE, "final_bridge_is_conditional": True,
        "hLower_hUpper_discharged": False, "production_modules_recompiled": False,
        "production_modules_replayed": False, "dependencies_built": False,
        "toolchain_bootstrapped": False, "lean_invocation_started": False,
        "lean_exit_code": None, "failures": [], "output_directory": str(output.relative_to(ROOT)),
    }
    exit_code = 1
    try:
        head = git("rev-parse", "HEAD")
        require(re.fullmatch(r"[0-9a-f]{40}", head) is not None, "HEAD is not a full commit SHA")
        report["source_commit"] = head
        verify_frozen_inputs()
        report["inputs_before"] = input_snapshot()
        with (output / "pins.stdout.log").open("wb") as out, (output / "pins.stderr.log").open("wb") as err:
            pin_result = subprocess.run([sys.executable, "verification/parts/p0/check_pins.py"],
                                        cwd=ROOT, stdout=out, stderr=err, check=False)
        report["pin_check_exit_code"] = pin_result.returncode
        require(pin_result.returncode == 0, "Existing frozen-pin check failed")
        lake = shutil.which("lake")
        require(lake is not None, "Pinned normal Lake is not on PATH")
        command = [lake, "env", "lean", "-DwarningAsError=true", "-o", str(audit_object), AUDIT]
        environment = os.environ.copy()
        for key in ["LEAN_PATH", "LEAN_SRC_PATH"]:
            environment.pop(key, None)
        report.update(command=command, cwd=str(ROOT), timeout_seconds=args.timeout_seconds,
                      inherited_lean_search_paths_cleared=True, lean_invocation_started=True,
                      audit_object_before={})
        write_json(output / "receipt.json", report)
        started = time.monotonic()
        try:
            with stdout_path.open("wb") as out, stderr_path.open("wb") as err:
                result = subprocess.run(command, cwd=ROOT, env=environment, stdout=out, stderr=err,
                                        timeout=args.timeout_seconds, check=False)
            report["lean_exit_code"] = result.returncode
        finally:
            report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        require(result.returncode == 0, f"Audit Lean exited with {result.returncode}")
        declarations, bridge, inventories = parse_types(stdout_path.read_text(encoding="utf-8", errors="replace"))
        report["audit_object_after"] = object_parts(audit_object)
        write_json(output / "declarations.json", declarations)
        write_json(output / "serialized-inventory.json", inventories)
        write_json(output / "final-bridge.json", bridge)
        (output / "final-bridge-type.txt").write_text(
            FINAL_BRIDGE + "\n\nComplete pp.all type:\n" + bridge["type"] +
            "\n\nComplete readable type:\n" + bridge["readable_type"] +
            "\n\nThis existing theorem remains conditional on hLower and hUpper.\n")
        report.update(declaration_count=len(declarations), bridge_count=1,
                      full_types_untruncated=True, unsafe_partial_and_new_axiom_checks="PASS_IN_LEAN",
                      actual_defining_module_counts=dict(Counter(d["module"] for d in declarations)),
                      serialized_inventory_exact_match=True, owned_inventory_exact_match=True,
                      serialized_occurrence_coverage_exact_match=True,
                      serialized_occurrence_count=sum(i["serialized_constant_count"] for i in inventories),
                      shared_occurrence_count=sum(i["shared_constant_count"] for i in inventories),
                      serialized_raw_dependency_axiom_union=sorted({a for i in inventories
                          for occurrence in i["occurrences"] for a in occurrence["raw_dependency_axioms"]}),
                      required_historical_declarations_found=198, historical_complete_types_unchanged=True,
                      final_bridge_hypotheses_retained=["hLower", "hUpper"],
                      transitive_axiom_union=sorted({a for d in declarations + [bridge] for a in d["axioms"]}))
        report["compiler_output_files_sha256"] = {
            name: digest(output / name)
            for name in ["declarations.json", "serialized-inventory.json", "final-bridge.json", "final-bridge-type.txt"]
        }
        exit_code = 0
    except KeyboardInterrupt:
        report["failures"].append("Audit interrupted; no successful verification receipt")
        exit_code = 130
    except Exception as error:
        report["failures"].append(f"{type(error).__name__}: {error}")
    finally:
        if "inputs_before" in report:
            try:
                report["inputs_after"] = input_snapshot()
                require(report["inputs_after"] == report["inputs_before"],
                        "Source or existing production object part set/hash changed during export")
                report["source_commit_after"] = git("rev-parse", "HEAD")
                require(report["source_commit_after"] == report["source_commit"], "HEAD changed during export")
            except Exception as error:
                report["failures"].append(f"Postcheck: {type(error).__name__}: {error}")
                exit_code = 1
        for name, path in [("stdout", stdout_path), ("stderr", stderr_path)]:
            report[name + "_path"] = str(path.relative_to(ROOT))
            report[name + "_sha256"] = digest(path)
            report[name + "_first_lean_diagnostic"] = first_diagnostic(path.read_text(errors="replace"))
        if audit_object.is_file():
            try:
                current_output = object_parts(audit_object)
                if "audit_object_after" in report:
                    require(current_output == report["audit_object_after"],
                            "Audit output part set/hash changed during postcheck")
                report["audit_object_after"] = current_output
            except Exception as error:
                report["failures"].append(f"Audit output snapshot: {type(error).__name__}: {error}")
                exit_code = 1
        report["diagnostic_order"] = "First real Lean diagnostic retained separately in each raw stream; cross-stream order is not asserted"
        report["status"] = "PASS" if exit_code == 0 and not report["failures"] else "FAILED"
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(output / "receipt.json", report)
        sys.stdout.buffer.write(stdout_path.read_bytes())
        sys.stdout.flush()
        sys.stderr.buffer.write(stderr_path.read_bytes())
        sys.stderr.flush()
        if (output / "final-bridge-type.txt").exists():
            print((output / "final-bridge-type.txt").read_text())
        print(json.dumps({"status": report["status"], "receipt": str(output / "receipt.json"),
                          "failures": report["failures"]}, ensure_ascii=False))
    return 0 if report["status"] == "PASS" else (exit_code or 1)


if __name__ == "__main__":
    raise SystemExit(main())
