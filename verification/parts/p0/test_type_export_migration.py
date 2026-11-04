#!/usr/bin/env python3
"""Lightweight parser/preflight regressions. No Lean, Lake, or network is used.

Run from the repository root:
    python3 -m unittest discover -s verification/parts/p0 -p 'test_type_export_migration.py' -v

The accepted parser fixtures are synthetic. They test fail-closed validation,
not elaboration, kernel replay, or a successful production type export.
"""

from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


HERE = Path(__file__).resolve().parent


def load_exporter(round_number):
    name = f"check_round{round_number}_types"
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EXPORTERS = {number: load_exporter(number) for number in [3, 6]}


def declaration(name, module, kind="theorem"):
    return dict(name=name, module=module, kind=kind, is_unsafe=False,
                is_partial=False, is_axiom=False, axioms=["propext"],
                type="fixture type for " + name, readable_type="complete fixture type")


def fixture(number):
    exporter = EXPORTERS[number]
    baseline = None
    if number == 3:
        baseline = deepcopy(exporter.historical_baseline())
        declarations = []
        for name, expected in baseline.items():
            record = declaration(name, expected["expected_module"], expected["kind"])
            expected["type_sha256"] = hashlib.sha256(record["type"].encode()).hexdigest()
            declarations.append(record)
    else:
        declarations = [declaration(name, module)
                        for module, names in exporter.REQUIRED_PUBLIC.items() for name in names]
    # Extra generated declarations must be retained by complete serialized coverage.
    declarations.append(declaration("_private.migration_fixture.generated", exporter.MODULES[-1], "definition"))
    bridge = declaration(exporter.FINAL_BRIDGE, exporter.FINAL_MODULE)
    bridge["type"] = "(hLower : Prop) (hUpper : Prop) : Prop"
    return declarations, bridge, baseline


def serialize(number, declarations, bridge, inventory_declarations=None):
    exporter = EXPORTERS[number]
    inventory_declarations = declarations if inventory_declarations is None else inventory_declarations
    lines = [f"P0_ROUND{number}_DECL " + json.dumps(d) for d in declarations]
    lines.append(f"P0_ROUND{number}_FINAL_BRIDGE " + json.dumps(bridge))
    counts = Counter(d["module"] for d in declarations)
    for module in exporter.MODULES:
        names = [d["name"] for d in inventory_declarations if d["module"] == module]
        lines.append(f"P0_ROUND{number}_MODULE " + json.dumps(dict(module=module, count=counts[module])))
        lines.append(f"P0_ROUND{number}_SERIALIZED " + json.dumps(dict(
            module=module, is_module=False, import_all=True, has_data=True,
            serialized_constant_names=names, environment_constant_names=names,
            serialized_constant_count=len(names), extra_codegen_name_count=0)))
    lines.append(f"P0_ROUND{number}_COUNT {len(declarations)}")
    return "\n".join(lines)


class MigrationTests(unittest.TestCase):
    def parse(self, number, declarations, bridge, baseline, **kwargs):
        exporter = EXPORTERS[number]
        stdout = serialize(number, declarations, bridge, **kwargs)
        if number == 3:
            with patch.object(exporter, "historical_baseline", return_value=baseline):
                return exporter.parse_types(stdout)
        return exporter.parse_types(stdout)

    def test_checked_in_baseline_has_all_198_and_exactly_39_migrations(self):
        baseline = EXPORTERS[3].historical_baseline()
        self.assertEqual(len(baseline), 198)
        moved = [r for r in baseline.values() if r["historical_module"] != r["expected_module"]]
        self.assertEqual(len(moved), 39)
        self.assertEqual({r["expected_module"] for r in moved}, {EXPORTERS[3].MODULES[-1]})
        self.assertIn("ImbalancedChen.HistoricalPrefixCapData.mk.sizeOf_spec", baseline)

    def test_round6_retains_all_46_public_names_and_three_moved_owners(self):
        exporter = EXPORTERS[6]
        self.assertEqual(sum(map(len, exporter.REQUIRED_PUBLIC.values())), 46)
        self.assertEqual(len(exporter.REQUIRED_PUBLIC[exporter.MODULES[-1]]), 3)

    def test_complete_fixtures_pass_and_include_generated_core_declaration(self):
        for number in EXPORTERS:
            with self.subTest(round=number):
                declarations, bridge, baseline = fixture(number)
                result, _, inventories = self.parse(number, declarations, bridge, baseline)
                self.assertEqual(len(result), len(declarations))
                self.assertEqual(len(inventories), len(EXPORTERS[number].MODULES))

    def test_missing_historical_declaration_fails_even_with_self_consistent_census(self):
        for number in EXPORTERS:
            with self.subTest(round=number):
                declarations, bridge, baseline = fixture(number)
                moved_name = ("ImbalancedChen.HistoricalPrefixCapData.mk.sizeOf_spec" if number == 3
                              else "ImbalancedChen.HistoricalPrefixCapData.level3_on_fifth_cell")
                declarations = [r for r in declarations if r["name"] != moved_name]
                with self.assertRaisesRegex(RuntimeError, "Missing historical|Missing public"):
                    self.parse(number, declarations, bridge, baseline)

    def test_wrong_historical_owner_fails_even_with_self_consistent_census(self):
        for number in EXPORTERS:
            with self.subTest(round=number):
                declarations, bridge, baseline = fixture(number)
                record = next(r for r in declarations if r["module"] == EXPORTERS[number].MODULES[-1])
                record["module"] = EXPORTERS[number].MODULES[0]
                with self.assertRaisesRegex(RuntimeError, "historical declaration owner|wrong defining module"):
                    self.parse(number, declarations, bridge, baseline)

    def test_historical_complete_type_change_fails(self):
        declarations, bridge, baseline = fixture(3)
        declarations[0]["type"] += " changed"
        with self.assertRaisesRegex(RuntimeError, "Historical complete type changed"):
            self.parse(3, declarations, bridge, baseline)

    def test_omitted_generated_declaration_fails_exact_serialized_coverage(self):
        for number in EXPORTERS:
            with self.subTest(round=number):
                declarations, bridge, baseline = fixture(number)
                with self.assertRaisesRegex(RuntimeError, "declaration sets differ"):
                    self.parse(number, declarations[:-1], bridge, baseline, inventory_declarations=declarations)

    def test_duplicate_declaration_fails(self):
        for number in EXPORTERS:
            with self.subTest(round=number):
                declarations, bridge, baseline = fixture(number)
                declarations.append(deepcopy(declarations[0]))
                with self.assertRaisesRegex(RuntimeError, "Duplicate declaration"):
                    self.parse(number, declarations, bridge, baseline)

    def test_missing_or_duplicate_module_record_fails(self):
        for number in EXPORTERS:
            for duplicate in [False, True]:
                with self.subTest(round=number, duplicate=duplicate):
                    declarations, bridge, baseline = fixture(number)
                    stdout = serialize(number, declarations, bridge)
                    line = next(line for line in stdout.splitlines() if f"ROUND{number}_MODULE " in line)
                    stdout = stdout + "\n" + line if duplicate else stdout.replace(line + "\n", "", 1)
                    with self.assertRaisesRegex(RuntimeError, "Missing or duplicate census module record"):
                        EXPORTERS[number].parse_types(stdout)

    def test_bad_safety_flags_and_axioms_fail(self):
        for number in EXPORTERS:
            for key in ["is_unsafe", "is_partial", "is_axiom", "axioms"]:
                with self.subTest(round=number, flag=key):
                    declarations, bridge, baseline = fixture(number)
                    declarations[-1][key] = ["sorryAx"] if key == "axioms" else True
                    with self.assertRaisesRegex(RuntimeError, "Unsafe, partial, axiom|Forbidden axiom"):
                        self.parse(number, declarations, bridge, baseline)

    def test_truncated_type_fails(self):
        for number in EXPORTERS:
            for ellipsis in ["⋯", "…"]:
                with self.subTest(round=number, ellipsis=ellipsis):
                    declarations, bridge, baseline = fixture(number)
                    declarations[-1]["type"] += ellipsis
                    with self.assertRaisesRegex(RuntimeError, "truncated type"):
                        self.parse(number, declarations, bridge, baseline)

    def test_final_bridge_must_retain_both_hypotheses(self):
        for number in EXPORTERS:
            with self.subTest(round=number):
                declarations, bridge, baseline = fixture(number)
                bridge["type"] = "hLower : Prop"
                with self.assertRaisesRegex(RuntimeError, "both hLower and hUpper"):
                    self.parse(number, declarations, bridge, baseline)

    def test_frozen_inputs_and_modified_core_failure_without_starting_lean(self):
        for number, exporter in EXPORTERS.items():
            with self.subTest(round=number):
                exporter.verify_frozen_inputs()
                with tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    for relative in exporter.FROZEN:
                        destination = root / relative
                        destination.parent.mkdir(parents=True, exist_ok=True)
                        destination.write_bytes((exporter.ROOT / relative).read_bytes())
                    path = root / "ImbalancedChen/FinitePrimeGeometryCore.lean"
                    path.write_bytes(path.read_bytes() + b"\n-- changed\n")
                    with patch.object(exporter, "ROOT", root):
                        with self.assertRaisesRegex(RuntimeError, "Frozen input changed: ImbalancedChen/FinitePrimeGeometryCore"):
                            exporter.verify_frozen_inputs()

    def test_modified_baseline_is_rejected(self):
        exporter = EXPORTERS[3]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            path = root / exporter.HISTORICAL_BASELINE
            path.parent.mkdir(parents=True)
            path.write_bytes((exporter.ROOT / exporter.HISTORICAL_BASELINE).read_bytes() + b" ")
            with patch.object(exporter, "ROOT", root):
                with self.assertRaisesRegex(RuntimeError, "Historical declaration baseline changed"):
                    exporter.historical_baseline()

    def test_lean_and_python_target_module_lists_match(self):
        for number, exporter in EXPORTERS.items():
            with self.subTest(round=number):
                source = (HERE / f"Round{number}Audit.lean").read_text()
                target_section = source.split("  let modules := #[", 1)[1].split("]", 1)[0]
                names = tuple(part.strip().removeprefix("`") for part in target_section.split(","))
                self.assertEqual(names, exporter.MODULES)
                self.assertIn("owned.qsort Name.lt == data.constNames.qsort Name.lt", source)
                self.assertIn("if info.isPartial then", source)


if __name__ == "__main__":
    unittest.main()
