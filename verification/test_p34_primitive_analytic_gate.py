"""Focused checks for the analytic supplier's source/owner and fresh-run contracts."""
import hashlib
import json
import tempfile
import zipfile
import unittest
from pathlib import Path

from verify_p34_primitive_analytic import (classify_declarations, reverse_repairs,
                                          checkpoint_prefix, read_archive, verify_bound_prefix,
                                          source_declarations, verify_tool_hashes)
from run_p34_primitive_analytic_cloud import fresh_paths


class DeclarationOrigins(unittest.TestCase):
    def setUp(self):
        self.modules = [{"module": "Project.A", "source_declarations": [
            {"name": "Pair", "qualified_name": "N.Pair", "kind": "abbrev", "private": False},
            {"name": "lemmaA", "qualified_name": "N.lemmaA", "kind": "theorem", "private": True},
        ]}]
        self.rows = [
            {"module": "Project.A", "kind": "definition", "name": "N.Pair"},
            {"module": "Project.A", "kind": "theorem", "name": "_private.Project.A.4.N.lemmaA"},
            {"module": "Project.A", "kind": "theorem", "name": "N.Pair.eq_1"},
        ]

    def test_maps_private_abbrev_and_generated_records(self):
        actual = classify_declarations(self.rows, self.modules)
        self.assertEqual([r["origin"] for r in actual],
                         ["explicit_public", "explicit_private", "generated"])

    def test_generated_auxiliary_cannot_satisfy_missing_private_theorem(self):
        self.rows[1]["name"] += ".eq_1"
        with self.assertRaisesRegex(ValueError, "N.lemmaA"):
            classify_declarations(self.rows, self.modules)

    def test_public_decl_must_have_the_right_owner_and_kind(self):
        for field, wrong in (("module", "Project.B"), ("kind", "theorem")):
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "N.Pair"):
                classify_declarations([{**self.rows[0], field: wrong}, *self.rows[1:]],
                                      self.modules)

    def test_two_private_matches_are_ambiguous(self):
        other = {**self.rows[1], "name": "_private.Project.A.8.N.lemmaA"}
        with self.assertRaisesRegex(ValueError, "N.lemmaA"):
            classify_declarations(self.rows + [other], self.modules)


class BaselineDeclarations(unittest.TestCase):
    def test_reverses_only_documented_unique_anchored_edits_in_reverse_order(self):
        first = dict(id="r1", original="by exact h", repaired="by exact h₁",
                     reason="type", diagnostic_task="attempt-one")
        second = dict(id="r2", original="by exact h₁", repaired="by exact h₂",
                      reason="type", diagnostic_task="attempt-two")
        self.assertEqual(reverse_repairs("Q := by exact h₂", [first, second]), "Q := by exact h")
        for source in ("Q := by exact h", "Q := by exact h₂; by exact h₂"):
            with self.subTest(source=source), self.assertRaisesRegex(ValueError, "r2"):
                reverse_repairs(source, [first, second])
        with self.assertRaisesRegex(ValueError, "r1"):
            reverse_repairs("Q := by exact h₁", [{**first, "diagnostic_task": ""}])

    def test_unrecognized_explicit_owner_cannot_be_counted_as_generated(self):
        with self.assertRaisesRegex(ValueError, "opaque"):
            source_declarations("def one := 1\nopaque another : Nat := 1\n", "N")

    def test_proof_repairs_preserve_types_definitions_privacy_and_names(self):
        original = ("def phase (n : Int) := -n\n"
                    "private theorem negative (n : Int) : phase n = -n := by\n  rfl\n")
        signature = source_declarations(original, "N")
        self.assertEqual(len(signature), 2)
        self.assertEqual(signature, source_declarations(original.replace("  rfl", "  exact rfl"), "N"))
        for changed in (original.replace(":= -n", ":= n"), original.replace("= -n :=", "= n :="),
                        original.replace("private ", ""), original.replace("negative", "other")):
            with self.subTest(changed=changed):
                self.assertNotEqual(signature, source_declarations(changed, "N"))


class CheckpointEvidence(unittest.TestCase):
    def test_failed_or_changed_module_ends_the_entire_reusable_prefix(self):
        modules = ["ImbalancedChen.A", "ImbalancedChen.B", "ImbalancedChen.C"]
        sources = [{"module": m, "path": m + ".lean", "sha256": str(i)}
                   for i, m in enumerate(modules)]
        report = {"source_sha256": {s["path"]: s["sha256"] for s in sources},
                  "project_object_bindings": dict.fromkeys(modules, {}),
                  "stages": [{"name": "A-strict", "exit_code": 0},
                             {"name": "B-strict", "exit_code": 1}]}
        self.assertEqual(checkpoint_prefix(report, sources), modules[:1])
        report["stages"][1]["exit_code"] = 0
        self.assertEqual(checkpoint_prefix(report, sources), modules[:2])
        report["source_sha256"]["ImbalancedChen.A.lean"] = "changed"
        self.assertEqual(checkpoint_prefix(report, sources), [])

    def test_rejects_damaged_archive_member_even_with_correct_outer_hash(self):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "evidence.zip"
            with zipfile.ZipFile(path, "w") as archive:
                archive.writestr("verification/output.log", b"new")
                archive.writestr("ARCHIVE_MEMBERS.json", json.dumps({
                    "verification/output.log": {"bytes": 3,
                    "sha256": hashlib.sha256(b"old").hexdigest()}}))
            with self.assertRaisesRegex(ValueError, "member"):
                read_archive(path, hashlib.sha256(path.read_bytes()).hexdigest())

    def test_changed_object_part_invalidates_previously_authenticated_module(self):
        with tempfile.TemporaryDirectory() as temp:
            objroot = Path(temp)
            path = objroot / "ImbalancedChen" / "A.olean"
            path.parent.mkdir()
            path.write_bytes(b"original")
            binding = {"ImbalancedChen.A": {"resolved_olean": str(path), "parts": {
                "ImbalancedChen/A.olean": hashlib.sha256(b"original").hexdigest()}}}
            verify_bound_prefix(objroot, binding, ())
            path.write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "ImbalancedChen.A"):
                verify_bound_prefix(objroot, binding, ())


class FreshInputs(unittest.TestCase):
    def test_tool_hash_disagreement_is_fatal(self):
        with self.assertRaisesRegex(ValueError, "leanchecker"):
            verify_tool_hashes({"lean": "a", "leanchecker": "b"},
                               {"lean": "a", "leanchecker": "c"})

    def test_fresh_paths_reject_nested_existing_or_redirected_outputs(self):
        with tempfile.TemporaryDirectory() as folder:
            workspace = Path(folder).resolve()
            root = workspace / "p34-primitive-analytic-src"
            receipts = workspace / "p34-primitive-analytic-evidence"
            self.assertEqual(fresh_paths(root, receipts, workspace), (root, receipts))
            redir = workspace / "redirect"
            redir.symlink_to(workspace, target_is_directory=True)
            for candidate in (root, root / receipts.name, redir / receipts.name,
                              workspace.parent / receipts.name):
                with self.subTest(candidate=candidate), self.assertRaises(ValueError):
                    fresh_paths(root, candidate, workspace)
            receipts.with_suffix(".zip").touch()
            with self.assertRaises(ValueError):
                fresh_paths(root, receipts, workspace)


if __name__ == "__main__":
    unittest.main()
