"""Local synthetic checks. Run python verification/part2/test_extend_p21_buchstab_native_snapshot.py."""
import json
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
        task.base = SimpleNamespace(files={}, modules={}, value={"resolutions": {}}, raw_sha256="synthetic-parent")
        task.modules, task.resolutions, task.links = {}, {}, {}
        task.lib = self.root / "lib"
        task.lib.mkdir()
        task.base.search_path = [task.lib]
        task.source_roots = [self.root / "src"]
        task.pins, task.source_names, task.extra_roots = {}, {}, {}
        self.task = task

    def standard(self, name, text):
        source = self.task.source_roots[0] / extension.relative(name, ".lean")
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(text)
        obj = self.task.lib / extension.relative(name, ".olean")
        obj.parent.mkdir(parents=True, exist_ok=True)
        obj.write_text(name)
        for p in (source, obj):
            self.task.bind(p, "fixture")
            self.task.base.files[str(p)] = self.task.files[str(p)].copy()
        self.task.base.value["resolutions"][name] = str(obj)
        return str(obj)

    def test_exact_original_header_and_no_observer_import(self):
        prefix = b"import Mathlib.Tactic\r\n\r\n"
        data = extension.probe_source(prefix + b"open Set\n", ["Mathlib.Tactic"])
        self.assertEqual(data, prefix + extension.OBSERVER)
        self.assertEqual(extension.imports(data.decode()), ["Mathlib.Tactic"])
        with self.assertRaisesRegex(ValueError, "Unsupported pinned"):
            extension.probe_source(b"public import Mathlib.Tactic\n\n", ["Mathlib.Tactic"])

    def test_inventory_checks_provider_identity_count_duplicates_and_implicit_init(self):
        names = ["Init", "Mathlib.Tactic"]
        def log(rows, count=2, main="Native.Example"):
            lines = ["P21_IMPORT " + json.dumps({"module": n, "olean": "/tmp/" + n}) for n in rows]
            lines.append("P21_HEADER " + json.dumps({"main": main, "count": count}))
            return "\n".join(lines).encode()
        def parsed(data):
            return extension.observed(data, "Native.Example", ["Mathlib.Tactic"])
        self.assertEqual(set(parsed(log(names))), set(names))
        for data in [log(names + names), log(names, count=3), log(names, main="_stdin"),
                     log(["Init"], count=1), log(["Mathlib.Tactic"], count=1)]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                parsed(data)

    def test_only_observed_modules_credited_and_every_observed_source_and_facet_frozen(self):
        init = self.standard("Init", "prelude")
        example = self.standard("Mathlib.Example", "private import Lake.Util.Casing")
        imported = {"Init": init, "Mathlib.Example": example}
        def capture(rows):
            return self.task.inputs(rows, [self.task.lib])
        self.assertEqual(set(capture(imported)), set(imported))
        with self.assertRaisesRegex(ValueError, "No unambiguous frozen source"):
            capture(dict(imported, **{"Lake.Util.Casing": "/unqualified"}))
        with self.assertRaisesRegex(ValueError, "Missing qualified native predecessor"):
            capture({"MathlibNt.Unknown": "/unqualified"})
        with self.assertRaisesRegex(ValueError, "Observed object differs"):
            capture(dict(imported, **{"Mathlib.Example": init}))
        extra = Path(example + ".private")
        extra.write_bytes(b"not originally frozen")
        with self.assertRaisesRegex(ValueError, "Unfrozen or redirected"):
            capture(imported)
        extra.unlink()
        Path(example).write_bytes(b"changed public bytes")
        with self.assertRaisesRegex(ValueError, "changed"):
            capture(imported)

    def test_observer_uses_original_filename_cwd_and_options_and_fails_on_missing_commands(self):
        name = extension.TARGETS[0]
        source = self.root / "provider.lean"
        source.write_text("import Mathlib.Tactic\n\nexample : True := True.intro\n")
        self.task.gold, self.task.value = self.root, {"runtime": {"lean": "/pinned/lean"}}
        self.task.recheck_base = lambda: None
        env = {"LEAN_PATH": str(self.task.lib)}
        fake = subprocess.CompletedProcess([], 1, b"unknown constant Lean.findOLean")
        with patch.object(subprocess, "run", return_value=fake) as invoked:
            with self.assertRaisesRegex(ValueError, "Header inventory exit 1"):
                self.task.observe(name, source, ["Mathlib.Tactic"], [self.task.lib], env, "before")
        self.assertEqual(invoked.call_args.args[0], ["/pinned/lean", "-t0", "-j1", "-M6144",
                         "-DwarningAsError=true", "--stdin", extension.relative(name, ".lean"), "--json"])
        self.assertEqual(invoked.call_args.kwargs["cwd"], self.task.gold)
        self.assertEqual(invoked.call_args.kwargs["env"], env)
        self.assertEqual(extension.imports(invoked.call_args.kwargs["input"].decode()), ["Mathlib.Tactic"])
        self.assertFalse((self.task.out / "probes" / name / "before.log").exists())
        self.assertFalse((self.task.out / "providers" / (name + ".json")).exists())

    def test_existing_native_cannot_borrow_extension_facet_or_provider(self):
        name = "MathlibNt.Existing"
        obj = self.standard(name, "import Init")
        receipt = self.root / "old-receipt"
        receipt.write_text("old")
        self.task.bind(receipt, "provider")
        self.task.base.files[str(receipt)] = self.task.files[str(receipt)].copy()
        row = {"provider": {"status": "EXACT_ORIGINAL_IMPORTS_REBOUND", "receipt": str(receipt)},
               "source": str(self.task.source_roots[0] / extension.relative(name, ".lean")),
               "object": obj, "closure_signature": "original"}
        self.task.base.modules[name] = row
        self.task.modules[name] = dict(row, closure_signature="replacement")
        self.task.resolutions[name] = obj
        def capture():
            return self.task.inputs({name: obj}, [self.task.lib])
        self.assertEqual(capture()[name]["closure_signature"], "original")
        extra = Path(obj + ".private")
        extra.write_text("extension-only")
        self.task.bind(extra, "extension-output")
        with self.assertRaisesRegex(ValueError, "Unfrozen or redirected"):
            capture()
        extra.unlink()
        del self.task.base.files[str(receipt)]
        with self.assertRaisesRegex(ValueError, "lacks a qualified provider"):
            capture()

    def test_new_binding_cannot_authorize_a_missing_original_standard_resolution(self):
        obj = self.standard("Mathlib.Example", "import Init")
        del self.task.base.value["resolutions"]["Mathlib.Example"]
        self.task.resolutions["Mathlib.Example"] = obj
        with self.assertRaisesRegex(ValueError, "Unfrozen source or resolution"):
            self.task.inputs({"Mathlib.Example": obj}, [self.task.lib])

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
        self.task.base.files[str(source)] = self.task.files[str(source)].copy()
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
