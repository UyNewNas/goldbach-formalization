"""Regression tests for the classical support source and object gates."""
import json
import copy
import hashlib
import zipfile
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
import verify_p34_classical_support as gate


class ClassicalSupportGate(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name).resolve()

    def file(self, path, contents=b""):
        path = self.root / path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(contents)
        return path

    def test_literal_segment_tampering(self):
        intake = json.loads((gate.ROOT / gate.INTAKE).read_text())
        source = (gate.ROOT / gate.module_file(gate.NEW, ".lean")).read_bytes()
        gate.validate_segment(source, intake)
        with self.assertRaisesRegex(RuntimeError, "segment differs"):
            gate.validate_segment(source.replace(b"64*", b"32*"), intake)

    def test_documented_proof_repairs_preserve_the_original_statement(self):
        # A source gate must accept these two expression repairs, while still
        # rejecting any change to the mathematical statements or phase.
        intake = json.loads((gate.ROOT / gate.INTAKE).read_text())
        source = (gate.ROOT / gate.module_file(gate.NEW, ".lean")).read_bytes()
        repairs = [
            {"id": "explicit_nat_power_and_real_bounds",
             "original": "  have hvN : 1 ≤ (2 : ℕ)^j := pow_pos (by norm_num) _\n  have hv : (1 : ℝ) ≤ ((2 : ℕ)^j : ℝ) := by exact_mod_cast hvN\n  unfold classicalMScale\n  constructor\n  · linarith\n  constructor <;> linarith\n",
             "repaired": "  have hvN : 1 ≤ (2 : ℕ)^j := pow_pos (by norm_num : (0 : ℕ) < 2) j\n  have hv : (1 : ℝ) ≤ ((2 : ℕ)^j : ℝ) := by exact_mod_cast hvN\n  unfold classicalMScale\n  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hv ⊢\n  constructor\n  · linarith only [hv]\n  constructor <;> linarith only [hv]\n"},
            {"id": "normalize_real_support_bounds",
             "original": "  unfold classicalMScale\n  constructor <;> linarith\n",
             "repaired": "  unfold classicalMScale\n  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hloR hhiR ⊢\n  constructor\n  · linarith only [hloR]\n  · linarith only [hhiR]\n"},
        ]
        if intake["consumer"]["segment_byte_identical"]:
            for repair in repairs:
                source = source.replace(repair["original"].encode(), repair["repaired"].encode())
            intake["consumer"]["segment_lines_inclusive"][1] += 4
        intake["consumer"].update(segment_byte_identical=False, expression_repairs=repairs)
        gate.validate_segment(source, intake)
        for changed in (source.replace(b"64*", b"32*"),
                        source.replace(b"classicalMScale j < (m", b"classicalMScale j <= (m")):
            with self.assertRaisesRegex(RuntimeError, "segment differs"):
                gate.validate_segment(changed, intake)
        undocumented = copy.deepcopy(intake)
        undocumented["consumer"]["expression_repairs"] = []
        with self.assertRaisesRegex(RuntimeError, "segment differs"):
            gate.validate_segment(source, undocumented)

    def test_missing_project_import_is_rejected(self):
        self.file("ImbalancedChen/A.lean", b"import ImbalancedChen.B\n")
        with self.assertRaisesRegex(RuntimeError, "Missing or redirected"):
            gate.project_closure(self.root, ("ImbalancedChen.A",))

    def test_unknown_external_and_shadowed_source_fail(self):
        path = self.file("ImbalancedChen/A.lean", b"import Surprise.B\n")
        with self.assertRaisesRegex(RuntimeError, "Unrecognized or shadowed"):
            gate.project_closure(self.root, ("ImbalancedChen.A",))
        path.write_text("import Mathlib.Tactic\n")
        self.file("Mathlib/Tactic.lean")
        with self.assertRaisesRegex(RuntimeError, "Unrecognized or shadowed"):
            gate.project_closure(self.root, ("ImbalancedChen.A",))

    def test_dependencies_must_match_parsed_header_and_owner(self):
        source = self.file("Main.lean", b"import Mathlib.Tactic\n")
        init = self.file("sys/Init.olean")
        tactic = self.file("packages/mathlib/Mathlib/Tactic.olean")
        roots = {"mathlib": self.root / "packages/mathlib", "Qq": self.root / "packages/Qq"}
        obj = self.root / "project"
        log = str(init) + "\n" + str(tactic)
        check = lambda output: gate.expected_deps(source, output, set(), obj, roots, init.parent)
        self.assertEqual(check(log), sorted([str(init), str(tactic)]))
        with self.assertRaisesRegex(RuntimeError, "parsed import set differs"):
            check(str(init))
        shadow = self.file("packages/Qq/Mathlib/Tactic.olean")
        with self.assertRaisesRegex(RuntimeError, "shadowed module"):
            check(str(init) + "\n" + str(shadow))

    def test_goldbach_namespace_requires_its_own_verified_root(self):
        module = gate.GOLDBACH_MODULE
        source = self.file("Main.lean", ("import " + module + "\n").encode())
        init = self.file("sys/Init.olean")
        path = gate.module_file(module, ".olean")
        obj = self.file(Path("packages/goldbach") / path)
        roots = {n: self.root / "packages" / n for n in ("mathlib", "goldbach")}
        def check(olean):
            return gate.expected_deps(source, str(init) + "\n" + str(olean), set(),
                                      self.root / "project", roots, init.parent)
        self.assertIn(str(obj), check(obj))
        obj.unlink()
        impostor = self.file(Path("packages/mathlib") / path)
        with self.assertRaisesRegex(RuntimeError, "shadowed module"):
            check(impostor)

    def test_package_set_must_include_architect_and_goldbach(self):
        manifest = json.loads((gate.ROOT / "lake-manifest.json").read_text())
        self.assertEqual(len(gate.package_pins(manifest)), 11)
        for name in ("goldbach", "LeanArchitect"):
            partial = {"packages": [p for p in manifest["packages"] if p["name"] != name]}
            with self.assertRaisesRegex(RuntimeError, "Unexpected package manifest"):
                gate.package_pins(partial)

    def test_committed_closure_matches_all_reachable_sources(self):
        actual = gate.project_closure(gate.ROOT)
        committed = json.loads((gate.ROOT / gate.CLOSURE).read_text())
        self.assertEqual(actual, committed)
        self.assertEqual(len(actual["topological_order"]), 57)
        self.assertIn(gate.GOLDBACH_MODULE, actual["external_imports"])
        self.assertEqual(actual["topological_order"][-1], gate.NEW)
        self.assertEqual(actual["topological_order"][-2], gate.REUSED)

    def test_server_or_private_part_changes_binding(self):
        module = "ImbalancedChen.A"
        obj = self.file("project/ImbalancedChen/A.olean")
        objroot = self.root / "project"
        before = gate.bind_object(module, objroot, ())
        private = Path(str(obj) + ".private")
        private.write_bytes(b"private")
        added = gate.bind_object(module, objroot, ())
        self.assertNotEqual(added, before)
        private.write_bytes(b"changed")
        self.assertNotEqual(gate.bind_object(module, objroot, ()), added)
        private.unlink()
        private.symlink_to(obj)
        with self.assertRaisesRegex(RuntimeError, "Invalid project object part"):
            gate.bind_object(module, objroot, ())

    def test_checkpoint_archive_cannot_be_replaced(self):
        self.assertTrue(callable(getattr(gate, "load_resume_archive", None)),
                        "The incremental gate must authenticate its failed-run evidence")
        archive = gate.ROOT / gate.R2_ARCHIVE
        report, provenance, _ = gate.load_resume_archive(archive)
        self.assertEqual(report["status"], "FAILED")
        self.assertEqual(len(report["project_object_bindings"]), 56)
        self.assertEqual(provenance["source"], "4c213f5d6477aa30e1d4636d5c4fb9d01cf8e188")
        changed = self.file("changed.zip", archive.read_bytes() + b"changed")
        with self.assertRaisesRegex(RuntimeError, "checkpoint archive"):
            gate.load_resume_archive(changed)

    def test_reuse_rejects_changed_dependency_or_missing_compilation(self):
        self.assertTrue(callable(getattr(gate, "validate_resume_closure", None)),
                        "The incremental gate must require the same complete provider closure")
        archive = gate.ROOT / gate.DOC / "verification-attempts/proof-expression-failure-r2.zip"
        with zipfile.ZipFile(archive) as z:
            report = json.loads(z.read("verification/report.json"))
        current = gate.project_closure(gate.ROOT)
        gate.validate_resume_closure(report, current)
        changed = copy.deepcopy(current)
        changed["project_sources"][0]["sha256"] = "0" * 64
        with self.assertRaisesRegex(RuntimeError, "provider closure"):
            gate.validate_resume_closure(report, changed)
        changed = copy.deepcopy(current)
        changed["project_sources"][0]["imports"] = []
        with self.assertRaisesRegex(RuntimeError, "provider closure"):
            gate.validate_resume_closure(report, changed)
        incomplete = copy.deepcopy(report)
        incomplete["project_object_bindings"].pop(gate.REUSED)
        with self.assertRaisesRegex(RuntimeError, "provider closure"):
            gate.validate_resume_closure(incomplete, current)

    def test_checkpoint_copy_rejects_stale_parts_and_never_overwrites(self):
        self.assertTrue(callable(getattr(gate, "copy_checkpoint_object", None)),
                        "Reusing a module must check every object part before copying")
        oldroot, newroot = self.root / "old", self.root / "new"
        self.file("old/ImbalancedChen/A.olean", b"compiled")
        private = self.file("old/ImbalancedChen/A.olean.private", b"private")
        binding = {"resolved_olean": str(oldroot / "ImbalancedChen/A.olean"),
                   "parts": {"ImbalancedChen/A.olean": hashlib.sha256(b"compiled").hexdigest(),
                             "ImbalancedChen/A.olean.private": hashlib.sha256(b"private").hexdigest()}}
        private.write_bytes(b"stale")
        with self.assertRaisesRegex(RuntimeError, "checkpoint object"):
            gate.copy_checkpoint_object("ImbalancedChen.A", binding, oldroot, newroot, ())
        self.assertFalse((newroot / "ImbalancedChen/A.olean").exists())
        private.write_bytes(b"private")
        copied = gate.copy_checkpoint_object("ImbalancedChen.A", binding, oldroot, newroot, ())
        self.assertEqual((newroot / "ImbalancedChen/A.olean").read_bytes(), b"compiled")
        self.assertEqual((newroot / "ImbalancedChen/A.olean.private").read_bytes(), b"private")
        self.assertEqual(copied["parts"], binding["parts"])
        self.assertNotEqual(private.stat().st_ino, (newroot / "ImbalancedChen/A.olean.private").stat().st_ino)
        with self.assertRaisesRegex(RuntimeError, "Existing checkpoint destination"):
            gate.copy_checkpoint_object("ImbalancedChen.A", binding, oldroot, newroot, ())


if __name__ == "__main__":
    unittest.main()
