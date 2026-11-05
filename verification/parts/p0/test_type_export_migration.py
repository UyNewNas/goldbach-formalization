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


def occurrence(record, serialized_module=None):
    module = record["module"] if serialized_module is None else serialized_module
    shared = module != record["module"]
    return dict(
        serialized_module=module, name=record["name"], owner_module=record["module"],
        kind=record["kind"], is_unsafe=False, is_partial=False, is_axiom=False,
        type_matches_environment=True, level_params_match_environment=True,
        kind_matches_environment=True, all_dependencies_present=True,
        raw_dependency_names=["propext"], raw_dependency_axioms=["propext"],
        raw_expression_count=2 if record["kind"] in {"theorem", "definition", "opaque"} else 1,
        shared=shared, shared_validation=dict(
            owner_precedes_serialized=True, owner_has_serialized_theorem=True,
            type_matches_owner=True, level_params_match_owner=True,
            theorem_all_matches_owner_and_environment=True) if shared else None)


def serialize(number, declarations, bridge, inventory_declarations=None, shared_declarations=()):
    exporter = EXPORTERS[number]
    inventory_declarations = declarations if inventory_declarations is None else inventory_declarations
    lines = [f"P0_ROUND{number}_DECL " + json.dumps(d) for d in declarations]
    lines.append(f"P0_ROUND{number}_FINAL_BRIDGE " + json.dumps(bridge))
    counts = Counter(d["module"] for d in declarations)
    for module in exporter.MODULES:
        names = [d["name"] for d in inventory_declarations if d["module"] == module]
        lines.append(f"P0_ROUND{number}_MODULE " + json.dumps(dict(module=module, count=counts[module])))
        inventory = dict(module=module, is_module=False, import_all=True, has_data=True,
            serialized_constant_names=names, environment_constant_names=names,
            serialized_constant_count=len(names), extra_codegen_name_count=0)
        if number == 3:
            shared = [d["name"] for source, d in shared_declarations if source == module]
            inventory.update(owned_constant_names=names, shared_constant_names=shared,
                serialized_constant_names=names + shared,
                serialized_constant_count=len(names) + len(shared),
                owned_constant_count=len(names), shared_constant_count=len(shared))
        lines.append(f"P0_ROUND{number}_SERIALIZED " + json.dumps(inventory))
    if number == 3:
        for record in inventory_declarations:
            lines.append("P0_ROUND3_OCCURRENCE " + json.dumps(occurrence(record)))
        for module, record in shared_declarations:
            lines.append("P0_ROUND3_OCCURRENCE " + json.dumps(occurrence(record, module)))
    lines.append(f"P0_ROUND{number}_COUNT {len(declarations)}")
    return "\n".join(lines)


def edit_records(stdout, prefix, edit, predicate=lambda record: True):
    lines = []
    for line in stdout.splitlines():
        if line.startswith(prefix):
            record = json.loads(line.removeprefix(prefix))
            if predicate(record):
                edit(record)
                line = prefix + json.dumps(record)
        lines.append(line)
    return "\n".join(lines)


class MigrationTests(unittest.TestCase):
    def parse(self, number, declarations, bridge, baseline, **kwargs):
        exporter = EXPORTERS[number]
        stdout = serialize(number, declarations, bridge, **kwargs)
        return self.parse_stdout(number, stdout, baseline)

    def parse_stdout(self, number, stdout, baseline):
        exporter = EXPORTERS[number]
        if number == 3:
            with patch.object(exporter, "historical_baseline", return_value=baseline):
                return exporter.parse_types(stdout)
        return exporter.parse_types(stdout)

    def shared_fixture(self, external_owner=False):
        declarations, bridge, baseline = fixture(3)
        shared = (declaration("External.generated_equation", "External.ImportedModule")
                  if external_owner else next(d for d in declarations if d["kind"] == "theorem"))
        module = next(module for module in EXPORTERS[3].MODULES if module != shared["module"])
        stdout = serialize(3, declarations, bridge, shared_declarations=[(module, shared)])
        return stdout, baseline, (module, shared["name"])

    def test_round3_same_name_shared_occurrence_passes_without_losing_owned_census(self):
        stdout, baseline, key = self.shared_fixture()
        declarations, _, inventories = self.parse_stdout(3, stdout, baseline)
        occurrences = [record for inventory in inventories for record in inventory["occurrences"]]
        self.assertEqual(len(occurrences), len(declarations) + 1)
        self.assertEqual(sum(record["shared"] for record in occurrences), 1)
        self.assertEqual(sum(i["owned_constant_count"] for i in inventories), len(declarations))
        copies = [record for record in occurrences if record["name"] == key[1]]
        self.assertEqual(len(copies), 2)
        self.assertEqual({record["shared"] for record in copies}, {False, True})

    def test_round3_external_owner_shared_theorem_passes_with_full_validation(self):
        stdout, baseline, _ = self.shared_fixture(external_owner=True)
        declarations, _, inventories = self.parse_stdout(3, stdout, baseline)
        self.assertNotIn("External.generated_equation", {d["name"] for d in declarations})
        self.assertEqual(sum(i["shared_constant_count"] for i in inventories), 1)

    def test_round3_external_shared_copies_must_agree_on_owner(self):
        declarations, bridge, baseline = fixture(3)
        record = declaration("External.generated_equation", "External.ImportedModule")
        sources = EXPORTERS[3].MODULES[:2]
        stdout = serialize(3, declarations, bridge,
            shared_declarations=[(source, record) for source in sources])
        self.parse_stdout(3, stdout, baseline)
        changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
            lambda r: r.__setitem__("owner_module", "External.DifferentModule"),
            lambda r: r["shared"] and r["serialized_module"] == sources[1])
        with self.assertRaisesRegex(RuntimeError, "disagree on defining owner or kind"):
            self.parse_stdout(3, changed, baseline)

    def test_round3_missing_extra_duplicate_and_wrong_module_occurrences_fail(self):
        stdout, baseline, key = self.shared_fixture()
        prefix = "P0_ROUND3_OCCURRENCE "
        line = next(line for line in stdout.splitlines() if line.startswith(prefix)
                    and json.loads(line.removeprefix(prefix))["shared"])
        record = json.loads(line.removeprefix(prefix))
        extra = dict(record, name="not_in_serialized_inventory")
        wrong_module = dict(record, serialized_module="Unexpected.Module")
        variants = [
            (stdout.replace(line + "\n", "", 1), "Missing serialized occurrence"),
            (stdout + "\n" + prefix + json.dumps(extra), "Unexpected serialized occurrence"),
            (stdout + "\n" + line, "Duplicate serialized occurrence"),
            (stdout.replace(line, prefix + json.dumps(wrong_module)), "Unexpected serialized occurrence"),
        ]
        for changed, message in variants:
            with self.subTest(message=message):
                with self.assertRaisesRegex(RuntimeError, message):
                    self.parse_stdout(3, changed, baseline)

    def test_round3_bad_serialized_partitions_fail(self):
        stdout, baseline, key = self.shared_fixture()
        prefix = "P0_ROUND3_SERIALIZED "
        variants = [
            lambda r: r["owned_constant_names"].append(key[1]),
            lambda r: r["shared_constant_names"].clear(),
            lambda r: r["serialized_constant_names"].remove(key[1]),
            lambda r: r["shared_constant_names"].append("unserialized.extra"),
            lambda r: r["shared_constant_names"].append(key[1]),
            lambda r: r.pop("owned_constant_names"),
            lambda r: r.pop("shared_constant_names"),
            lambda r: r["environment_constant_names"].append(key[1]),
        ]
        for index, edit in enumerate(variants):
            with self.subTest(variant=index):
                changed = edit_records(stdout, prefix, edit, lambda r: r["module"] == key[0])
                with self.assertRaisesRegex(RuntimeError, "partition|Duplicate|inventory|declaration sets differ"):
                    self.parse_stdout(3, changed, baseline)

    def test_round3_owned_shared_and_serialized_counts_are_independent_and_exact(self):
        stdout, baseline, key = self.shared_fixture()
        for field in ["serialized_constant_count", "owned_constant_count", "shared_constant_count"]:
            for bad in [None, -1, True, 10000]:
                with self.subTest(field=field, bad=bad):
                    changed = edit_records(stdout, "P0_ROUND3_SERIALIZED ",
                        lambda r: r.__setitem__(field, bad), lambda r: r["module"] == key[0])
                    with self.assertRaisesRegex(RuntimeError, "Incorrect .* declaration count"):
                        self.parse_stdout(3, changed, baseline)

    def test_round3_wrong_occurrence_owner_fails_for_owned_and_shared(self):
        stdout, baseline, key = self.shared_fixture()
        for shared in [False, True]:
            for owner in [None, "", "Wrong.Owner", key[0]]:
                with self.subTest(shared=shared, owner=owner):
                    changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
                        lambda r: r.__setitem__("owner_module", owner),
                        lambda r: r["name"] == key[1] and r["shared"] is shared)
                    with self.assertRaisesRegex(RuntimeError, "owner"):
                        self.parse_stdout(3, changed, baseline)

    def test_round3_occurrence_identity_and_safety_flags_fail_closed(self):
        stdout, baseline, _ = self.shared_fixture()
        fields = {
            "is_unsafe": True, "is_partial": True, "is_axiom": True,
            "type_matches_environment": False, "level_params_match_environment": False,
            "kind_matches_environment": False, "all_dependencies_present": False,
        }
        for shared in [False, True]:
            for field, bad in fields.items():
                for missing in [False, True]:
                    with self.subTest(shared=shared, field=field, missing=missing):
                        def edit(record):
                            if missing:
                                record.pop(field)
                            else:
                                record[field] = bad
                        changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ", edit,
                            lambda r: r["shared"] is shared)
                        with self.assertRaisesRegex(RuntimeError, "occurrence safety flag|occurrence validation"):
                            self.parse_stdout(3, changed, baseline)

    def test_round3_shared_validation_flags_fail_closed(self):
        stdout, baseline, _ = self.shared_fixture()
        fields = ["owner_precedes_serialized", "owner_has_serialized_theorem",
                  "type_matches_owner", "level_params_match_owner",
                  "theorem_all_matches_owner_and_environment"]
        for field in fields:
            for missing in [False, True]:
                with self.subTest(field=field, missing=missing):
                    def edit(record):
                        if missing:
                            record["shared_validation"].pop(field)
                        else:
                            record["shared_validation"][field] = False
                    changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ", edit, lambda r: r["shared"])
                    with self.assertRaisesRegex(RuntimeError, "shared theorem validation"):
                        self.parse_stdout(3, changed, baseline)

    def test_round3_shared_non_theorem_fails(self):
        stdout, baseline, _ = self.shared_fixture(external_owner=True)
        changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
            lambda r: r.__setitem__("kind", "definition"), lambda r: r["shared"])
        with self.assertRaisesRegex(RuntimeError, "not a theorem"):
            self.parse_stdout(3, changed, baseline)

    def test_round3_shared_flag_and_validation_shape_are_exact(self):
        stdout, baseline, _ = self.shared_fixture()
        edits = [
            (True, lambda r: r.__setitem__("shared", False)),
            (False, lambda r: r.__setitem__("shared", True)),
            (True, lambda r: r.pop("shared")),
            (False, lambda r: r.pop("shared")),
            (True, lambda r: r.__setitem__("shared_validation", None)),
            (True, lambda r: r.pop("shared_validation")),
            (False, lambda r: r.__setitem__("shared_validation", {})),
            (False, lambda r: r.pop("shared_validation")),
        ]
        for index, (shared, edit) in enumerate(edits):
            with self.subTest(variant=index):
                changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ", edit,
                    lambda r: r["shared"] is shared)
                with self.assertRaisesRegex(RuntimeError, "shared flag|shared validation|shared theorem validation"):
                    self.parse_stdout(3, changed, baseline)

    def test_round3_raw_sorry_axiom_fails_even_when_cached_declaration_axioms_are_allowed(self):
        stdout, baseline, _ = self.shared_fixture()
        for shared in [False, True]:
            for field in ["raw_dependency_names", "raw_dependency_axioms"]:
                with self.subTest(shared=shared, field=field):
                    changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
                        lambda r: r[field].append("sorryAx"), lambda r: r["shared"] is shared)
                    with self.assertRaisesRegex(RuntimeError, "Forbidden raw axiom dependency"):
                        self.parse_stdout(3, changed, baseline)

    def test_round3_direct_raw_theorem_self_dependency_fails(self):
        stdout, baseline, key = self.shared_fixture()
        for shared in [False, True]:
            with self.subTest(shared=shared):
                changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
                    lambda r: r["raw_dependency_names"].append(r["name"]),
                    lambda r: r["name"] == key[1] and r["shared"] is shared)
                with self.assertRaisesRegex(RuntimeError, "self-dependency"):
                    self.parse_stdout(3, changed, baseline)

    def test_round3_missing_dependency_detection_flag_is_mandatory(self):
        stdout, baseline, _ = self.shared_fixture()
        for missing in [False, True]:
            with self.subTest(missing=missing):
                def edit(record):
                    record["raw_dependency_names"].append("Missing.Declaration")
                    if missing:
                        record.pop("all_dependencies_present")
                    else:
                        record["all_dependencies_present"] = False
                changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ", edit, lambda r: r["shared"])
                with self.assertRaisesRegex(RuntimeError, "all_dependencies_present"):
                    self.parse_stdout(3, changed, baseline)

    def test_round3_raw_dependency_lists_must_be_present_unique_strings(self):
        stdout, baseline, _ = self.shared_fixture()
        for field in ["raw_dependency_names", "raw_dependency_axioms"]:
            for bad in [None, "propext", ["propext", "propext"], [""], [1]]:
                with self.subTest(field=field, bad=bad):
                    changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
                        lambda r: r.__setitem__(field, bad), lambda r: r["shared"])
                    with self.assertRaisesRegex(RuntimeError, "raw dependency"):
                        self.parse_stdout(3, changed, baseline)

    def test_round3_raw_expression_count_matches_each_kind(self):
        stdout, baseline, _ = self.shared_fixture()
        for kind, count in [("theorem", 1), ("definition", 1), ("constructor", 2)]:
            changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
                lambda r: r.__setitem__("raw_expression_count", count), lambda r: r["kind"] == kind)
            with self.subTest(kind=kind):
                self.assertNotEqual(changed, stdout)
                with self.assertRaisesRegex(RuntimeError, "Incorrect raw expression count"):
                    self.parse_stdout(3, changed, baseline)
        for bad in [None, True, 0, -1]:
            with self.subTest(bad=bad):
                changed = edit_records(stdout, "P0_ROUND3_OCCURRENCE ",
                    lambda r: r.__setitem__("raw_expression_count", bad), lambda r: r["shared"])
                with self.assertRaisesRegex(RuntimeError, "Incorrect raw expression count"):
                    self.parse_stdout(3, changed, baseline)

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
                if number == 6:
                    self.assertIn("owned.qsort Name.lt == data.constNames.qsort Name.lt", source)
                else:
                    for marker in ["P0_ROUND3_OCCURRENCE", "owned_constant_names",
                                   "shared_constant_names", "all_dependencies_present"]:
                        self.assertIn(marker, source)
                self.assertIn("if info.isPartial then", source)


if __name__ == "__main__":
    unittest.main()
