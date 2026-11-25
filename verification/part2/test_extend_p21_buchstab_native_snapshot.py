"""Local synthetic checks. Run python verification/part2/test_extend_p21_buchstab_native_snapshot.py."""
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import extend_p21_buchstab_native_snapshot as extension


class BuchstabExtensionTests(unittest.TestCase):
    def setUp(self):
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        task = extension.Extension.__new__(extension.Extension)
        task.out = self.root
        task.hashes = extension.PhysicalHashes()
        task.files = {}
        task.base = SimpleNamespace(files=task.files, raw_sha256="synthetic-parent")
        task.modules, task.resolutions, task.links = {}, {}, {}
        task.lib = self.root / "lib"
        task.lib.mkdir()
        task.source_roots = [self.root / "src"]
        task.pins, task.source_names, task.extra_roots = {}, {}, {}
        self.task = task

    def test_transitive_imports_include_implicit_init_and_detect_changed_object(self):
        for name, content in {"Init": "prelude", "Mathlib.Example": "import Init",
                              "Mathlib.Other": "import Mathlib.Example"}.items():
            source = self.task.source_roots[0] / extension.relative(name, ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text(content)
            self.task.bind(source, "fixture-source")
            obj = self.task.lib / extension.relative(name, ".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            obj.write_text(name)
            self.task.bind(obj, "fixture-object")
            self.task.resolutions[name] = str(obj)
        closure = self.task.inputs(["Mathlib.Other"], [self.task.lib])
        self.assertEqual(set(closure), {"Init", "Mathlib.Other", "Mathlib.Example"})
        self.assertIn("Init", closure["Mathlib.Other"]["imports"])
        (self.task.lib / "Mathlib/Other.olean").write_bytes(b"changed")
        with self.assertRaisesRegex(ValueError, "changed"):
            self.task.inputs(["Mathlib.Other"], [self.task.lib])

    def test_batteries_overlay_recovers_only_frozen_source_in_locked_checkout(self):
        repo = self.root / "detached"
        subprocess.run(["git", "init", "-q", str(repo)], check=True)
        source = repo / "Batteries/Example.lean"
        source.parent.mkdir()
        source.write_text("import Init")
        subprocess.run(["git", "-C", str(repo), "add", "."], check=True)
        subprocess.run(["git", "-C", str(repo), "-c", "user.name=Test", "-c", "user.email=test@local",
                        "commit", "-qm", "fixture"], check=True)
        self.task.pins["batteries"] = extension.git(repo, "rev-parse", "HEAD").decode().strip()
        self.task.source_names[source.name] = [source]
        self.task.bind(source, "fixture-source")
        self.assertEqual(self.task.standard_source("Batteries.Example"), source)
        self.assertIn(repo, self.task.extra_roots)

    def test_failed_candidate_does_not_publish_snapshot_or_success_marker(self):
        self.task.modules = {name: {"provider": {}} for name in extension.TARGETS}
        self.task.value = {"runtime": {"lean_path": [], "lean": "/lean"}, "context_signature": "old"}
        self.task.view = lambda _: self.root
        with patch.object(extension, "ExternalSnapshot", side_effect=ValueError("bad candidate")):
            with self.assertRaisesRegex(ValueError, "bad candidate"):
                self.task.run()
        self.assertTrue((self.root / "candidates/combined-snapshot.json").is_file())
        self.assertFalse((self.root / "EXTERNAL_SNAPSHOT.json").exists())
        self.assertFalse((self.root / "QUALIFICATION.json").exists())


if __name__ == "__main__":
    unittest.main()
