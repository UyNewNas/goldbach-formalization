#!/usr/bin/env python3
"""Export exact Round 6 types from existing objects after a successful full build.

This compiles only Round6Audit.lean. It does not build dependencies, bootstrap a
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
AUDIT = "verification/parts/p0/Round6Audit.lean"
FINAL_BRIDGE = "ImbalancedChen.current_theorem_1_1_of_manuscript_bounds"
FINAL_MODULE = "ImbalancedChen.CurrentMainTheorem"
MODULES = (
    "ImbalancedChen.HistoricalUpperFiveCellGeometry",
    "ImbalancedChen.ActualHistoricalFifthCellIntegral",
    "ImbalancedChen.ActualHistoricalFifthSavingIntegral",
    "ImbalancedChen.HistoricalFifthCutoffInvariance",
)
# All 46 public declarations in the four frozen source modules. Generated and
# private declarations are additionally required by exact serialized coverage.
REQUIRED_PUBLIC = {
    MODULES[0]: (
        "ImbalancedChen.HistoricalPrefixCapData.fifthParentGateBounds",
        "ImbalancedChen.HistoricalPrefixCapData.mem_fifthParentGateRegion",
        "ImbalancedChen.HistoricalPrefixCapData.level3_on_fifth_cell",
        "ImbalancedChen.HistoricalPrefixCapData.level4_on_fifth_cell",
        "ImbalancedChen.HistoricalPrefixCapData.level5_on_fifth_cell",
        "ImbalancedChen.HistoricalPrefixCapData.level5_on_selected_fifth_cell",
        "ImbalancedChen.HistoricalPrefixCapData.level3_tuple_on_fifth_cell",
        "ImbalancedChen.historicalUpperFive_cube_tests_iff_log",
        "ImbalancedChen.mem_historicalUpperFiveFrontierTuples_iff_log_on_cell",
        "ImbalancedChen.historicalUpperFiveFrontierTuples_cell_filter",
    ),
    MODULES[1]: (
        "ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection",
        "ImbalancedChen.HistoricalPrefixCapData.fifthPrimeCorrection",
        "ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_on_cell",
        "ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_on_unselected_cell",
        "ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_outside",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection_eq_zero_of_not_mem",
        "ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_eq_cell_indicators",
        "ImbalancedChen.HistoricalPrefixCapData.fifthPrimeCorrection_eq_cells",
        "ImbalancedChen.HistoricalPrefixCapData.fifthFrontier_cell_weighted_sum",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection_eq_residual_sums",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCellIntegral",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCorrectionIntegral",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCellIntegral_eq_integral",
        "ImbalancedChen.HistoricalPrefixCapData.fifthCorrectionIntegral_eq_integrals",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthCellPrimeCorrection",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection_ceil",
    ),
    MODULES[2]: (
        "ImbalancedChen.HistoricalPrefixCapData.level5_ownCube_normalized_history",
        "ImbalancedChen.HistoricalPrefixCapData.level4_ancestor_ownCube_normalized_history",
        "ImbalancedChen.HistoricalPrefixCapData.actualHistoricalFifthSaving_eq_tupleSum_at_cutoff",
        "ImbalancedChen.HistoricalPrefixCapData.actualHistoricalFifthSaving_eq_fifthPrimeCorrection",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_actualHistoricalFifthSaving",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_actualHistoricalFifthSaving_ceil",
        "ImbalancedChen.HistoricalPrefixCapData.upperFourthToFifthSaving_eq",
        "ImbalancedChen.HistoricalPrefixCapData.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_upperFourthToFifthSaving",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_upperFourthToFifthSaving_ceil",
    ),
    MODULES[3]: (
        "ImbalancedChen.actualPrimeFrontierTuples_ownedCell_cutoff_invariant",
        "ImbalancedChen.HistoricalPrefixCapData.fifthOwnCubeDifference_outside",
        "ImbalancedChen.HistoricalPrefixCapData.fifthOwnCubeDifference_normalized_outside",
        "ImbalancedChen.HistoricalPrefixCapData.fifthTupleSum_cutoff_invariant",
        "ImbalancedChen.HistoricalPrefixCapData.actualHistoricalFifthSaving_eq_fifthPrimeCorrection_of_cutoff_ge",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_actualHistoricalFifthSaving_of_cutoff_ge",
        "ImbalancedChen.HistoricalPrefixCapData.upperFourthToFifthSaving_normalized_eq_fifthPrimeCorrection_of_cutoff_ge",
        "ImbalancedChen.HistoricalPrefixCapData.tendsto_upperFourthToFifthSaving_of_cutoff_ge",
    ),
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FROZEN = {
    "ImbalancedChen/HistoricalUpperFiveCellGeometry.lean": "a131b783d59540ea98cc11574f31489e2f75d519927445b49a2e4c688ab74cbe",
    "ImbalancedChen/ActualHistoricalFifthCellIntegral.lean": "550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de",
    "ImbalancedChen/ActualHistoricalFifthSavingIntegral.lean": "bcd7075649dcc6f374ea2318f77a45eb0c260f301a00045bb7ba60f6355da74e",
    "ImbalancedChen/HistoricalFifthCutoffInvariance.lean": "abe06826e099ec0beb73329c1c887fc5aeca0583efe1ff46c3b92ec91d9cdb3d",
    "lean-toolchain": "62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef",
    "lakefile.toml": "b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254",
    "lake-manifest.json": "35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849",
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def digest(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


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
    sources.update({AUDIT, "verification/parts/p0/check_round6_types.py",
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

    declarations = records("P0_ROUND6_DECL ")
    modules = unique_module_records(records("P0_ROUND6_MODULE "), "census")
    serialized = records("P0_ROUND6_SERIALIZED ")
    inventories = unique_module_records(serialized, "serialized")
    bridges = records("P0_ROUND6_FINAL_BRIDGE ")
    totals = [int(line.removeprefix("P0_ROUND6_COUNT ")) for line in lines
              if line.startswith("P0_ROUND6_COUNT ")]
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
    serialized_union: set[str] = set()
    for module in MODULES:
        inventory = inventories[module]
        require(inventory.get("is_module") is False
                and inventory.get("import_all") is True and inventory.get("has_data") is True,
                f"Incomplete legacy serialized module data: {module}")
        serialized_names = inventory.get("serialized_constant_names")
        environment_names = inventory.get("environment_constant_names")
        for label, values in [("serialized", serialized_names), ("environment", environment_names)]:
            require(isinstance(values, list) and values
                    and all(isinstance(name, str) and name for name in values),
                    f"Missing or malformed {label} declaration inventory: {module}")
            require(len(set(values)) == len(values), f"Duplicate {label} declaration: {module}")
        expected_names = {d["name"] for d in declarations if d["module"] == module}
        require(set(serialized_names) == set(environment_names) == expected_names,
                f"Serialized, environment, and exported declaration sets differ: {module}")
        require(not (serialized_union & set(serialized_names)),
                f"A declaration is serialized under multiple audited modules: {module}")
        serialized_union.update(serialized_names)
        for label, count in [("serialized", inventory.get("serialized_constant_count")),
                             ("census", modules[module].get("count"))]:
            require(type(count) is int and count > 0 and count == actual_counts[module],
                    f"Incorrect {label} declaration count: {module}")
        extra_count = inventory.get("extra_codegen_name_count")
        require(type(extra_count) is int and extra_count >= 0,
                f"Missing or malformed extra codegen count: {module}")
    require(serialized_union == set(names) and len(serialized_union) == totals[0],
            "Serialized union differs from the complete exported census")
    required_names = [name for names_ in REQUIRED_PUBLIC.values() for name in names_]
    require(set(REQUIRED_PUBLIC) == set(MODULES)
            and len(required_names) == len(set(required_names)) == 46,
            "Malformed frozen public declaration checklist")
    for module, required in REQUIRED_PUBLIC.items():
        for name in required:
            require(name in by_name and by_name[name]["module"] == module,
                    f"Missing public declaration or wrong defining module: {name}")
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
    output = ROOT / ".lake/part0-round6-types" / stamp
    output.mkdir(parents=True, exist_ok=False)
    audit_object = output / "Round6Audit.olean"
    stdout_path, stderr_path = output / "stdout.log", output / "stderr.log"
    stdout_path.touch()
    stderr_path.touch()
    report = {
        "schema": "p0-round6-types-export-v2", "status": "RUNNING",
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Supplemental type export after successful full lake build; existing proof gates remain required",
        "expected_defining_modules": list(MODULES), "required_public_declarations": 46,
        "census_basis": "Exact serialized constNames = defining-module environment = exported declarations",
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
        for relative, expected in FROZEN.items():
            require(digest(ROOT / relative) == expected, f"Frozen input changed: {relative}")
        report["inputs_before"] = input_snapshot()
        with (output / "pins.stdout.log").open("wb") as out, (output / "pins.stderr.log").open("wb") as err:
            pin_result = subprocess.run([sys.executable, "verification/parts/p0/check_pins.py"],
                                        cwd=ROOT, stdout=out, stderr=err, check=False)
        report["pin_check_exit_code"] = pin_result.returncode
        require(pin_result.returncode == 0, "Existing frozen-pin check failed")
        lake = shutil.which("lake")
        require(lake is not None, "Pinned normal Lake is not on PATH")
        command = [lake, "env", "lean", "-j2", "-M4096", "-DwarningAsError=true",
                   "-o", str(audit_object), AUDIT]
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
                      serialized_inventory_exact_match=True, required_public_declarations_found=46,
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
