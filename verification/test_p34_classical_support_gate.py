"""Regression tests for the classical support source and object gates."""
import json
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


if __name__ == "__main__":
    unittest.main()
