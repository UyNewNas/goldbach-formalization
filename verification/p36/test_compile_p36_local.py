"""Temporary runner checks; no Lean compilation is performed by this suite."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
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

    def test_verified_bundle_rejects_self_declared_receipt(self):
        from project_cache_reuse import inspect_verified_leaf_bundle
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "RECEIPT.json").write_text(json.dumps({
                "module": "ImbalancedChen.P3TaggedPhysicalRhoPushforward",
                "strict_compilation": True, "bundled_kernel_replay": True,
                "complete_transitive_axiom_audit": True}))
            with self.assertRaisesRegex(ValueError, "independently accepted"):
                inspect_verified_leaf_bundle(root, SimpleNamespace(), {}, {})

    def test_old_donor_state_cannot_be_reused_as_compiled_success(self):
        runner = self.runner()
        with tempfile.TemporaryDirectory() as temporary:
            obj = Path(temporary) / "A.olean"
            obj.write_bytes(b"object")
            record = {"exit_code": 0, "input_key": "key", "objects": runner.object_hashes(obj),
                      "reuse_origin": {"unqualified_old_donor": True}}
            self.assertFalse(runner.can_reuse(record, "key", obj))

    def test_core_module_shadow_in_lean_path_blocks_preflight(self):
        runner = self.runner()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            own, package, core = root / "own", root / "package", root / "core"
            for directory in (own, package, core): directory.mkdir()
            (package / "Init.olean").write_bytes(b"shadow")
            (core / "Init.olean").write_bytes(b"expected core")
            node = runner.Node("Init", "core", None, None, "core", core / "Init.olean")
            instance = runner.Runner.__new__(runner.Runner)
            instance.report = {"lean_path": list(map(str, (own, package, core))), "blockers": []}
            instance.graph = SimpleNamespace(nodes={"Init": node})
            instance.check_import_resolution()
            self.assertEqual(instance.report["blockers"][0]["reason"], "external_import_resolution_mismatch")

    def test_strict_dependency_reuse_preserves_key_and_rejects_changed_inputs_or_objects(self):
        runner = self.runner()
        for case in ("unchanged", "source_changed", "object_changed", "imports_changed", "ordinary_owned"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                source = root / "A.lean"
                source.write_text("theorem sample : True := trivial\n")
                node = runner.Node("A", "project", source, root, "build")
                instance = runner.Runner.__new__(runner.Runner)
                owned = case == "ordinary_owned"
                instance.args = SimpleNamespace(modules=["A"] if owned else ["Fresh"], verify_owned=True)
                instance.graph = SimpleNamespace(order=["A"], nodes={"A": node})
                instance.build = root / "build"
                instance.objdir = instance.build / "lib/lean"
                instance.objdir.mkdir(parents=True)
                instance.state_path = instance.build / "state.json"
                instance.toolchain = root / "toolchain"
                instance.env, instance.signatures, instance.snapshots, instance.project_reuse = {}, {}, {}, {}
                instance.report = {"strict_owned": True, "compiler": {"test": True},
                                   "lean_path": [str(instance.objdir)], "modules": {"A": {}}}
                obj = instance.objdir / "A.olean"
                obj.write_bytes(b"old compiled object")
                inputs = {"source": str(source), "source_sha256": runner.sha256(source),
                          "compiler": instance.report["compiler"], "strict": not owned,
                          "imports": {}, "lean_path": [str(instance.objdir)], "trust": 0, "threads": 1}
                old_key, old_objects = runner.digest_json(inputs), runner.object_hashes(obj)
                instance.state = {"schema": 1, "modules": {"A": {
                    **inputs, "exit_code": 0, "input_key": old_key, "objects": old_objects,
                    "log": "previous-strict.log"}}}
                if case == "source_changed":
                    source.write_text("theorem different : True := trivial\n")
                elif case == "object_changed":
                    obj.write_bytes(b"different object")
                elif case == "imports_changed":
                    node.imports = ["Dependency"]
                    instance.signatures["Dependency"] = "new dependency signature"
                calls = []
                def command(name, arguments, checked=False):
                    calls.append(arguments)
                    obj.write_bytes(b"fresh compiled object")
                    return 0, "", {"name": name, "command": arguments, "exit_code": 0, "log": "fresh.log"}
                instance.command, instance.save = command, lambda: None
                instance.build_modules()
                item = instance.report["modules"]["A"]
                if case == "unchanged":
                    self.assertEqual(calls, [])
                    self.assertEqual(item["action"], "reused")
                    self.assertTrue(item["strict"])
                    self.assertTrue(item["reused_stricter_warning_policy"])
                    self.assertEqual(item["input_key"], old_key)
                    self.assertEqual(item["previous_log"], "previous-strict.log")
                    self.assertEqual(instance.signatures["A"], runner.digest_json({
                        "input_key": old_key, "objects": old_objects}))
                else:
                    self.assertEqual(len(calls), 1)
                    self.assertEqual(item["action"], "compiled")
                    self.assertEqual("-DwarningAsError=true" in calls[0], owned)

    def test_verify_owned_performs_fresh_strict_compile_despite_valid_local_cache(self):
        runner = self.runner()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            source = root / "A.lean"
            source.write_text("theorem sample : True := trivial\n")
            node = runner.Node("A", "project", source, root, "build")
            instance = runner.Runner.__new__(runner.Runner)
            instance.args = SimpleNamespace(modules=["A"], verify_owned=True)
            instance.graph = SimpleNamespace(order=["A"], nodes={"A": node})
            instance.build = root / "build"
            instance.objdir = instance.build / "lib/lean"
            instance.objdir.mkdir(parents=True)
            instance.state_path = instance.build / "state.json"
            instance.toolchain = root / "toolchain"
            instance.env, instance.signatures, instance.snapshots, instance.project_reuse = {}, {}, {}, {}
            instance.report = {"strict_owned": True, "compiler": {"test": True},
                               "lean_path": [str(instance.objdir)], "modules": {"A": {}}}
            obj = instance.objdir / "A.olean"
            obj.write_bytes(b"old compiled object")
            inputs = {"source": str(source), "source_sha256": runner.sha256(source),
                      "compiler": instance.report["compiler"], "strict": True,
                      "imports": {}, "lean_path": [str(instance.objdir)], "trust": 0, "threads": 1}
            instance.state = {"schema": 1, "modules": {"A": {
                "exit_code": 0, "input_key": runner.digest_json(inputs),
                "objects": runner.object_hashes(obj)}}}
            calls = []
            def command(name, arguments, checked=False):
                calls.append(arguments)
                obj.write_bytes(b"fresh compiled object")
                return 0, "", {"name": name, "command": arguments, "exit_code": 0, "log": "fresh.log"}
            instance.command, instance.save = command, lambda: None
            instance.build_modules()
            self.assertEqual(len(calls), 1)
            self.assertIn("-DwarningAsError=true", calls[0])
            self.assertEqual(instance.report["modules"]["A"]["action"], "compiled")
            def failure(name, arguments, checked=False):
                return 1, "Application type mismatch: explicit argument is not accepted", {
                    "name": name, "command": arguments, "exit_code": 1, "log": "failed.log"}
            instance.command = failure
            with self.assertRaisesRegex(RuntimeError, "Application type mismatch"):
                instance.build_modules()
            self.assertFalse(obj.exists())
            self.assertEqual(instance.state["modules"]["A"]["exit_code"], 1)



if __name__ == "__main__":
    unittest.main()
