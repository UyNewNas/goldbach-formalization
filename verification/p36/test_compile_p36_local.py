"""Temporary runner checks; no Lean compilation is performed by this suite."""
from __future__ import annotations

import hashlib
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True

SCRIPT = Path(__file__).with_name("compile_p36_local.py")


class RunnerTests(unittest.TestCase):
    def runner(self):
        self.assertTrue(SCRIPT.is_file(), "the requested local runner is not implemented")
        if "p36_test_runner" not in sys.modules:
            spec = importlib.util.spec_from_file_location("p36_test_runner", SCRIPT)
            module = importlib.util.module_from_spec(spec)
            sys.modules[spec.name] = module
            spec.loader.exec_module(module)
        return sys.modules["p36_test_runner"]

    def test_imports_ignore_nested_comments_and_strings(self):
        runner = self.runner()
        text = '''/- import Wrong.A /- import Wrong.B -/ -/
public import Mathlib.A Mathlib.B -- import Wrong.C
import Native.C
def text := "import Wrong.D"
'''
        self.assertEqual(runner.parse_imports(text), ["Mathlib.A", "Mathlib.B", "Native.C"])

    def test_preflight_finds_missing_transitive_mathlib_cache(self):
        runner = self.runner()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project, packages, core = root / "project", root / "packages", root / "core"
            (project / "ImbalancedChen").mkdir(parents=True)
            (project / "ImbalancedChen/Main.lean").write_text("import Mathlib.A\n")
            (packages / "mathlib/Mathlib").mkdir(parents=True)
            (packages / "mathlib/Mathlib/A.lean").write_text("import Mathlib.B\n")
            (packages / "mathlib/Mathlib/B.lean").write_text("-- no imports\n")
            cached = packages / "mathlib/.lake/build/lib/lean/Mathlib/A.olean"
            cached.parent.mkdir(parents=True)
            cached.write_bytes(b"cached A")
            core.mkdir()
            (core / "Init.olean").write_bytes(b"Init")
            graph = runner.BuildGraph(project, packages, core)
            graph.collect(["ImbalancedChen.Main"])
            self.assertIn("Mathlib.B", {item["module"] for item in graph.blockers})
            self.assertEqual(graph.nodes["Mathlib.A"].kind, "cached")
            self.assertEqual(graph.nodes["ImbalancedChen.Main"].kind, "build")

    def test_native_sources_are_scheduled_before_project_consumer(self):
        runner = self.runner()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project, packages, core = root / "project", root / "packages", root / "core"
            project.mkdir()
            (project / "Main.lean").write_text("import Native.A\n")
            (packages / "native/Native").mkdir(parents=True)
            (packages / "native/Native/A.lean").write_text("import Native.B\n")
            (packages / "native/Native/B.lean").write_text("-- leaf\n")
            core.mkdir()
            (core / "Init.olean").write_bytes(b"Init")
            graph = runner.BuildGraph(project, packages, core)
            graph.collect(["Main"])
            built = [name for name in graph.order if graph.nodes[name].kind == "build"]
            self.assertEqual(built, ["Native.B", "Native.A", "Main"])
            self.assertEqual(graph.nodes["Native.A"].source_root, packages / "native")

    def test_private_object_change_invalidates_previous_success(self):
        runner = self.runner()
        with tempfile.TemporaryDirectory() as temporary:
            obj = Path(temporary) / "Main.olean"
            obj.write_bytes(b"object")
            private = Path(str(obj) + ".private")
            private.write_bytes(b"private-v1")
            expected = {str(obj): hashlib.sha256(b"object").hexdigest(),
                        str(private): hashlib.sha256(b"private-v1").hexdigest()}
            record = {"exit_code": 0, "input_key": "stable-inputs", "objects": expected}
            self.assertTrue(runner.can_reuse(record, "stable-inputs", obj))
            private.write_bytes(b"private-v2")
            self.assertFalse(runner.can_reuse(record, "stable-inputs", obj))
            self.assertFalse(runner.can_reuse(record, "changed-input", obj))

    def test_external_compile_uses_its_source_root_and_local_output(self):
        runner = self.runner()
        source = Path("/shared/packages/goldbach/MathlibNt/Example.lean")
        node = runner.Node("MathlibNt.Example", "goldbach", source,
                           Path("/shared/packages/goldbach"), "build")
        output = Path("/owned/build/MathlibNt/Example.olean")
        normal = runner.compile_command(Path("/pinned/lean"), node, output, False)
        strict = runner.compile_command(Path("/pinned/lean"), node, output, True)
        self.assertEqual(normal[normal.index("-R") + 1], "/shared/packages/goldbach")
        self.assertEqual(normal[normal.index("-o") + 1], str(output))
        self.assertNotIn("-DwarningAsError=true", normal)
        self.assertIn("-DwarningAsError=true", strict)


if __name__ == "__main__":
    unittest.main()
