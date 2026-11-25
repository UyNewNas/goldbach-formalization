"""Focused, compiler-free negative checks for the P2.4 input adapter."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import p24_qualify_native_inputs as q


class OriginalImportMapTests(unittest.TestCase):
    def setUp(self):
        self.old = "/original/project"
        self.parts = [self.old + "/lib/Mathlib/Fixture.olean", self.old + "/lib/Mathlib/Fixture.ir"]
        self.files = {p: {"sha256": str(i + 1) * 64} for i, p in enumerate(self.parts)}
        self.expected = {"Mathlib.Fixture": [[p, self.files[p]["sha256"]] for p in self.parts]}
        self.row = {"command": {"cwd": self.old}, "actual_import_map_sha256": q.signature(self.expected)}
        self.setup = {"importArts": {"Mathlib.Fixture": [["lib/Mathlib/Fixture.olean"], [self.parts[1]]]}}

    def test_relative_original_paths_rebind_without_changing_historical_hash(self):
        self.assertEqual(q.original_map(self.setup, self.row, self.files), self.expected)

    def test_missing_original_physical_receipt_is_not_backfilled(self):
        with self.assertRaisesRegex(ValueError, "lacks SHA receipt"):
            q.original_map(self.setup, self.row, {self.parts[0]: self.files[self.parts[0]]})

    def test_changed_physical_hash_rejects_historical_map(self):
        changed = {p: dict(row) for p, row in self.files.items()}
        changed[self.parts[0]]["sha256"] = "f" * 64
        with self.assertRaisesRegex(ValueError, "map SHA differs"):
            q.original_map(self.setup, self.row, changed)

    def test_reordered_import_parts_are_not_treated_as_equivalent(self):
        self.setup["importArts"]["Mathlib.Fixture"].reverse()
        with self.assertRaisesRegex(ValueError, "map SHA differs"):
            q.original_map(self.setup, self.row, self.files)

    def test_duplicate_import_groups_are_rejected(self):
        group = ["Mathlib.Fixture", [[p] for p in self.parts]]
        with self.assertRaisesRegex(ValueError, "Duplicate"):
            q.original_map({"importArts": [group, group]}, self.row, self.files)


class PhysicalAndScopeTests(unittest.TestCase):
    def test_previously_bound_file_cannot_be_replaced_even_without_an_expected_argument(self):
        with tempfile.TemporaryDirectory() as directory:
            obj = q.P24Qualification.__new__(q.P24Qualification)
            obj.hashes, obj.bound = q.PhysicalHashes(), {}
            path = Path(directory) / "input"
            path.write_bytes(b"first")
            obj.bind(path, "actual-input")
            path.write_bytes(b"other")
            with self.assertRaisesRegex(ValueError, "Previously bound"):
                obj.bind(path, "actual-input")

    def test_current_endpoint_source_graph_selects_only_actual_transitive_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            sources = {q.ROOT: "import ImbalancedChen.Child\nimport MathlibNt.Native\n",
                       "ImbalancedChen.Child": "import Mathlib.Data.Real.Basic\n",
                       "ImbalancedChen.Unrelated": "import MathlibNt.Other\n"}
            for name, text in sources.items():
                path = root / (name.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
            nodes, order = q.project_census(root, q.PhysicalHashes())
            self.assertEqual(set(nodes), {q.ROOT, "ImbalancedChen.Child"})
            self.assertEqual(order[-1], q.ROOT)
            child = root / "ImbalancedChen/Child.lean"
            child.write_text("import " + q.ROOT + "\n")
            with self.assertRaisesRegex(ValueError, "cycle"):
                q.project_census(root, q.PhysicalHashes())

    def test_quarantined_provider_blocks_dependents_and_publishes_no_snapshot(self):
        with tempfile.TemporaryDirectory() as directory:
            obj = q.P24Qualification.__new__(q.P24Qualification)
            obj.out = Path(directory)
            obj.hashes, obj.bound, obj.rebindings = q.PhysicalHashes(), {}, {}
            obj.local_blocked, obj.metadata_checks, obj.projects = {}, {}, {q.ROOT: {}}
            obj.member = {"modules": {}}
            obj.runtime_checks, obj.abi_checks = [], []
            obj.order = ["Architect.Command", "Architect"]
            obj.nodes = {"Architect.Command": {"direct_imports": ["Lean"]},
                         "Architect": {"direct_imports": ["Architect.Command"]}}

            class Archive:
                def close(self):
                    pass

            obj.archive = Archive()

            def attempt(name):
                if name == "Architect.Command":
                    raise ValueError("ORIGINAL_QUARANTINE_RETAINED_REQUIRES_INDEPENDENT_LEAF_RECEIPT:Architect.Command")
                return {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND"}

            with patch.object(obj, "freeze_current_core"), patch.object(obj, "recheck"), patch.object(obj, "rebind", side_effect=attempt):
                self.assertEqual(obj.run(), 2)
            report = json.loads((obj.out / "QUALIFICATION.json").read_text())
            self.assertEqual(report["qualified"], {})
            self.assertIn("Architect.Command", report["direct_blockers"])
            self.assertIn("UNQUALIFIED_NATIVE_DEPENDENCIES:Architect.Command", report["blocked"]["Architect"])
            self.assertFalse(report["compile_credit"])
            self.assertFalse(report["kernel_credit"])
            self.assertFalse((obj.out / "EXTERNAL_SNAPSHOT.json").exists())
            self.assertFalse((obj.out / "PENDING_EXTERNAL_SNAPSHOT.json").exists())


class DirectProviderRebindTests(unittest.TestCase):
    """Exercise actual files; only authentic ZIP metadata extraction is stubbed."""
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        base = Path(self.temporary.name)
        self.obj = obj = q.P24Qualification.__new__(q.P24Qualification)
        obj.hashes, obj.bound, obj.resolutions = q.PhysicalHashes(), {}, {}
        obj.metadata_checks, obj.rebindings = {}, {}
        obj.packages = {"LeanArchitect": base / "arch", "mathlib": base / "mathlib"}
        self.name = name = "Architect.Fixture"
        source = obj.packages["LeanArchitect"] / (name.replace(".", "/") + ".lean")
        source.parent.mkdir(parents=True)
        source.write_bytes(b"import Mathlib.Fixture\n")
        wanted = q.source_row(source, "LeanArchitect", obj.hashes)
        obj.nodes = {name: wanted}
        imported = obj.packages["mathlib"] / "Mathlib/Fixture.lean"
        imported.parent.mkdir(parents=True)
        imported.write_bytes(b"-- standard fixture\n")
        self.imported_obj = obj.packages["mathlib"] / ".lake/build/lib/lean/Mathlib/Fixture.olean"
        self.imported_obj.parent.mkdir(parents=True)
        self.imported_obj.write_bytes(b"import object")
        self.own = obj.packages["LeanArchitect"] / (".lake/build/lib/lean/" + name.replace(".", "/") + ".olean")
        self.own.parent.mkdir(parents=True)
        self.own.write_bytes(b"own object")
        old_import = "/original/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean"
        old_own = "/original/.lake/packages/LeanArchitect/.lake/build/lib/lean/" + name.replace(".", "/") + ".olean"
        imported_sha = hashlib.sha256(self.imported_obj.read_bytes()).hexdigest()
        old_map = {"Mathlib.Fixture": [[old_import, imported_sha]]}
        obj.cp = {"runtime_state": {"root": "/original"}, "actual_import_sources": {
            "Mathlib.Fixture": {"package": "mathlib", "source": {
                "sha256": hashlib.sha256(imported.read_bytes()).hexdigest(), "bytes": imported.stat().st_size}}},
            "files": {old_import: {"sha256": imported_sha, "bytes": self.imported_obj.stat().st_size}}}
        obj.selected = {name: {"original_classification": q.carrier.CLASSIFIED,
            "original_record_collection": "all_guarded_package_compilations", "original_guarded_row_index": 0,
            "facets": [{"original_path": old_own, "sha256": hashlib.sha256(self.own.read_bytes()).hexdigest(),
                        "bytes": self.own.stat().st_size}]}}
        obj.omitted = {}
        obj.member = {"modules": {name: {"source_sha256": wanted["source_sha256"],
            "actual_import_map_sha256_verified": q.signature(old_map)}}, "source_checks": {name: {
            "sha256": wanted["source_sha256"], "actual_imports": wanted["direct_imports"]}}}
        self.row = {"command": {"cwd": "/original"}, "actual_import_map_sha256": q.signature(old_map)}
        self.setup = {"importArts": {"Mathlib.Fixture": [[old_import]]}}

    def rebind(self):
        with patch.object(self.obj, "metadata", return_value=(self.row, self.setup, {})):
            return self.obj.rebind(self.name)

    def test_valid_provider_freezes_current_physical_map(self):
        result = self.rebind()
        current = {"Mathlib.Fixture": [[str(self.imported_obj.resolve()), hashlib.sha256(self.imported_obj.read_bytes()).hexdigest()]]}
        self.assertEqual(result["actual_import_map_sha256"], q.signature(current))
        self.assertEqual(len(self.obj.rebindings), 1)
        self.assertTrue(result["member_provider_present"])

    def test_absent_member_row_does_not_discard_complete_cp_provenance(self):
        self.obj.member["modules"].clear()
        result = self.rebind()
        self.assertEqual(result["status"], "EXACT_ORIGINAL_IMPORTS_REBOUND")
        self.assertFalse(result["member_provider_present"])
        self.assertIsNone(result["member_receipt_sha256"])

    def test_missing_real_cp_provider_cannot_be_replaced_by_member_presence(self):
        self.obj.selected.clear()
        with self.assertRaisesRegex(ValueError, "NO_ORIGINAL_PROVIDER"):
            self.rebind()

    def test_original_quarantine_cannot_be_cleared_by_member_receipt(self):
        self.obj.selected[self.name]["original_classification"] = q.carrier.ARCHITECT_QUARANTINE
        with self.assertRaisesRegex(ValueError, "ORIGINAL_QUARANTINE_RETAINED"):
            self.rebind()

    def test_mutated_own_object_is_rejected(self):
        self.own.write_bytes(b"bad object")
        with self.assertRaisesRegex(ValueError, "Physical SHA differs"):
            self.rebind()

    def test_mutated_import_object_is_rejected(self):
        self.imported_obj.write_bytes(b"bad import")
        with self.assertRaisesRegex(ValueError, "Physical SHA differs"):
            self.rebind()

    def test_extra_unrecorded_loadable_facet_is_rejected(self):
        self.own.with_suffix(".ir").write_bytes(b"extra ir")
        with self.assertRaisesRegex(ValueError, "facet set differs"):
            self.rebind()


if __name__ == "__main__":
    unittest.main()
