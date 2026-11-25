#!/usr/bin/env python3
"""Focused rejection tests for evidence union (no Lean execution)."""

import copy
import importlib.util
import io
import json
from pathlib import Path
import tarfile
import tempfile
import unittest


SPEC = importlib.util.spec_from_file_location(
    "accepted_union", Path(__file__).with_name("build_p2_accepted_union.py"))
union = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(union)


def fixture(module="ImbalancedChen.Example", name="example"):
    declaration = {"name": name, "module": module, "type": "True",
                   "unsafe": False, "partial": False, "axiom": False,
                   "axioms": ["propext"]}
    payload = {"declaration_count": 1, "declarations": [declaration],
               "axiom_counts": {"propext": 1}, "imports": ["Init"],
               "inventory": {"module": module, "environment": [name], "serialized": [name]}}
    meta = {"source_sha256": "source", "object_sha256": "object",
            "compile_closure_signature": "closure", "project_modules": [module],
            "declaration_count": 1, "page_binding": None, "axiom_counts": {"propext": 1}}
    occurrence = {"archive": "first.tar.xz", "source_sha256": "source",
                  "object_sha256": "object", "compile_closure_signature": "closure",
                  "receipt_sha256": "receipt1", "driver_sha256": "driver1",
                  "declarations_path": "audit/declarations.json", "declarations_sha256": "payload1"}
    return module, meta, payload, occurrence


class OwnedUnionTests(unittest.TestCase):
    def test_same_proof_different_receipt_is_counted_once_and_recorded(self):
        module, meta, payload, first = fixture()
        checked = union.validate_payload(module, meta, payload)
        accumulator = union.OwnedUnion()
        self.assertTrue(accumulator.add(module, meta, checked, first))
        second = {**first, "archive": "second.tar.xz", "receipt_sha256": "receipt2",
                  "driver_sha256": "driver2", "declarations_path": "new/declarations.json"}
        self.assertFalse(accumulator.add(module, copy.deepcopy(meta), copy.deepcopy(checked), second))
        result = accumulator.result([], 0)
        self.assertEqual(result["accepted_modules"], 1)
        self.assertEqual(result["owned_declarations"], 1)
        self.assertEqual(result["raw_export_owned_declaration_occurrences"], 2)
        self.assertEqual(result["deduplicated_owned_declaration_occurrences"], 1)
        differences = result["deduplicated_modules"][module]["provenance_differences"]
        self.assertEqual(differences["receipt_sha256"], ["receipt1", "receipt2"])

    def test_changed_duplicate_proof_is_rejected(self):
        for field in union.PROOF_META:
            with self.subTest(field=field):
                module, meta, payload, occurrence = fixture()
                checked = union.validate_payload(module, meta, payload)
                accumulator = union.OwnedUnion()
                accumulator.add(module, meta, checked, occurrence)
                changed = copy.deepcopy(meta)
                changed[field] = "changed"
                with self.assertRaisesRegex(union.UnionError, "proof metadata differs"):
                    accumulator.add(module, changed, checked, occurrence)
        for field in ("owned", "inventory", "imports"):
            with self.subTest(field=field):
                module, meta, payload, occurrence = fixture()
                checked = union.validate_payload(module, meta, payload)
                accumulator = union.OwnedUnion()
                accumulator.add(module, meta, checked, occurrence)
                changed = copy.deepcopy(checked)
                if field == "owned":
                    changed["owned"]["example"]["type"] = "False"
                elif field == "inventory":
                    changed["inventory"]["module"] = "Other"
                else:
                    changed["imports"].append("Other")
                with self.assertRaisesRegex(union.UnionError, "duplicate complete"):
                    accumulator.add(module, meta, changed, occurrence)
        module, meta, payload, occurrence = fixture()
        checked = union.validate_payload(module, meta, payload)
        accumulator = union.OwnedUnion()
        accumulator.add(module, meta, checked, occurrence)
        changed = copy.deepcopy(checked)
        changed["owned"]["example"]["axioms"] = ["Classical.choice"]
        with self.assertRaisesRegex(union.UnionError, "duplicate complete owned"):
            accumulator.add(module, meta, changed, occurrence)

    def test_same_name_in_different_modules_is_rejected(self):
        accumulator = union.OwnedUnion()
        for module_name in ("ImbalancedChen.First", "ImbalancedChen.Second"):
            module, meta, payload, occurrence = fixture(module_name, "sharedName")
            checked = union.validate_payload(module, meta, payload)
            if module_name.endswith("First"):
                accumulator.add(module, meta, checked, occurrence)
            else:
                with self.assertRaisesRegex(union.UnionError, "cross-module owned name collision"):
                    accumulator.add(module, meta, checked, occurrence)

    def test_unsafe_axiom_inventory_and_internal_duplicate_are_rejected(self):
        for flag in ("unsafe", "partial", "axiom"):
            with self.subTest(flag=flag):
                module, meta, payload, _ = fixture()
                payload["declarations"][0][flag] = True
                with self.assertRaisesRegex(union.UnionError, "forbidden"):
                    union.validate_payload(module, meta, payload)
        module, meta, payload, _ = fixture()
        payload["declarations"][0]["axioms"] = ["sorryAx"]
        with self.assertRaisesRegex(union.UnionError, "unexpected transitive axiom"):
            union.validate_payload(module, meta, payload)
        module, meta, payload, _ = fixture()
        payload["inventory"]["serialized"] = []
        with self.assertRaisesRegex(union.UnionError, "incomplete serialized inventory"):
            union.validate_payload(module, meta, payload)
        module, meta, payload, _ = fixture()
        payload["declarations"].append(copy.deepcopy(payload["declarations"][0]))
        payload["declaration_count"] = meta["declaration_count"] = 2
        with self.assertRaisesRegex(union.UnionError, "duplicate owned name"):
            union.validate_payload(module, meta, payload)

    def test_numeric_row_overlap_and_gap_are_rejected(self):
        accumulator = union.OwnedUnion()
        for index in (0, 1):
            module, meta, payload, occurrence = fixture(f"ImbalancedChen.Page{index}", f"row{index}")
            meta["page_binding"] = {"first_ordinal": 0, "row_count": 1}
            accumulator.add(module, meta, union.validate_payload(module, meta, payload), occurrence)
        with self.assertRaisesRegex(union.UnionError, "overlapping numeric rows"):
            accumulator.result([], 1)
        accumulator = union.OwnedUnion()
        module, meta, payload, occurrence = fixture()
        meta["page_binding"] = {"first_ordinal": 1, "row_count": 1}
        accumulator.add(module, meta, union.validate_payload(module, meta, payload), occurrence)
        with self.assertRaisesRegex(union.UnionError, "not exactly 0"):
            accumulator.result([], 1)

    def test_changed_archive_payload_hash_is_rejected(self):
        module, meta, payload, _ = fixture()
        artifact_path = "audit/declarations.json"
        meta.update({"artifact_paths": [artifact_path]})
        raw = json.dumps(payload).encode()
        manifest = {"accepted_modules": {module: meta}, "accepted_module_count": 1,
                    "files": {artifact_path: {"bytes": len(raw), "sha256": "wrong-hash"}}}
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            path = repo / "evidence.tar.xz"
            with tarfile.open(path, "w:xz") as archive:
                for name, content in (("ORIGINAL_EXPORT_MANIFEST.json", json.dumps(manifest).encode()),
                                      ("packages/all.tar.gz/" + artifact_path, raw)):
                    item = tarfile.TarInfo(name)
                    item.size = len(content)
                    archive.addfile(item, io.BytesIO(content))
            with self.assertRaisesRegex(union.UnionError, "payload hash/size mismatch"):
                union.scan_archive(path, repo, union.OwnedUnion())


if __name__ == "__main__":
    unittest.main(verbosity=2)
