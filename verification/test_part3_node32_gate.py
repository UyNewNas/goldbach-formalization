"""Focused source/object gate regressions; these tests do not run Lean or Lake."""
from __future__ import annotations

import copy
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
import verify_part3_continuation as verifier


class ProjectClosureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.target = "ImbalancedChen.Terminal"
        self.provider = "ImbalancedChen.Provider"
        self.targets = (self.target,)
        sources = {
            self.target: ("import ImbalancedChen.Provider\nimport Mathlib.Foo\n"
                          "namespace ImbalancedChen\nend ImbalancedChen\n"),
            self.provider: "import Mathlib.Bar\nnoncomputable section\n",
        }
        self.closure = {
            "targets": list(self.targets), "project_module_count": len(sources),
            "external_imports": ["Mathlib.Bar", "Mathlib.Foo"],
            "full_external_kernel_replay_claimed": False,
            "project_sources": [],
        }
        for module, text in sources.items():
            relative = module.replace(".", "/") + ".lean"
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            self.closure["project_sources"].append({
                "module": module, "path": relative,
                "sha256": hashlib.sha256(text.encode()).hexdigest(),
                "imports": ([self.provider, "Mathlib.Foo"] if module == self.target
                            else ["Mathlib.Bar"]),
            })

    def validate(self, closure: dict | None = None) -> tuple[str, ...]:
        return verifier.validate_project_closure(
            self.root, self.closure if closure is None else closure, self.targets)

    def test_reachable_graph_excludes_unrelated_new_source(self) -> None:
        (self.root / "ImbalancedChen/Unrelated.lean").write_text("import Missing.Provider\n")
        self.assertEqual(self.validate(), tuple(sorted((self.target, self.provider))))

    def test_lexer_ignores_comments_and_body_string(self) -> None:
        text = ("/- import Fake.One /- import Fake.Two -/ -/\n"
                "import ImbalancedChen.Provider -- import Fake.Three\n"
                "import Mathlib.Foo\nnamespace ImbalancedChen\n"
                'def text := "import Fake.Four"\nend ImbalancedChen\n')
        self.assertEqual(verifier.source_imports(text, "fixture"),
                         (self.provider, "Mathlib.Foo"))
        for body in ("namespace ImbalancedChen", "noncomputable section", "set_option maxErrors 1000"):
            with self.subTest(body=body):
                self.assertEqual(verifier.source_imports("import Mathlib.Foo\n" + body, "fixture"),
                                 ("Mathlib.Foo",))

    def test_unsupported_header_fails_closed(self) -> None:
        for text in ("import\nImbalancedChen.Provider\n", "public import Mathlib.Foo\n",
                     "import Mathlib.Foo\n  ImbalancedChen.Provider\nnamespace Test\n",
                     "import Mathlib.Foo import ImbalancedChen.Provider\n"):
            with self.subTest(text=text), self.assertRaisesRegex(RuntimeError, "Unsupported.*header"):
                verifier.source_imports(text, "fixture")

    def test_omitted_provider_fails_even_with_self_consistent_count(self) -> None:
        self.closure["project_sources"].pop()
        self.closure["project_module_count"] = 1
        with self.assertRaisesRegex(RuntimeError, "closure differs: missing=.*Provider"):
            self.validate()

    def test_extra_and_duplicate_records_fail(self) -> None:
        for duplicate in (False, True):
            closure = copy.deepcopy(self.closure)
            extra = copy.deepcopy(closure["project_sources"][-1])
            if not duplicate:
                extra.update(module="ImbalancedChen.Unrelated", path="ImbalancedChen/Unrelated.lean")
                (self.root / extra["path"]).write_text("import Mathlib.Bar\nnoncomputable section\n")
            closure["project_sources"].append(extra)
            closure["project_module_count"] += 1
            with self.subTest(duplicate=duplicate), self.assertRaisesRegex(
                    RuntimeError, "Duplicate.*source|closure differs:.*extra=.*Unrelated"):
                self.validate(closure)

    def test_import_edges_and_order_are_checked_independently_of_hash(self) -> None:
        for imports in ([], ["Mathlib.Foo", self.provider], [self.provider, self.provider]):
            closure = copy.deepcopy(self.closure)
            closure["project_sources"][0]["imports"] = imports
            with self.subTest(imports=imports), self.assertRaisesRegex(RuntimeError, "imports"):
                self.validate(closure)

    def test_external_missing_extra_duplicate_and_count_mismatch_fail(self) -> None:
        for external in (["Mathlib.Foo"], ["Mathlib.Bar", "Mathlib.Foo", "Mathlib.Extra"],
                         ["Mathlib.Bar", "Mathlib.Foo", "Mathlib.Foo"]):
            closure = copy.deepcopy(self.closure)
            closure["external_imports"] = external
            with self.subTest(external=external), self.assertRaisesRegex(RuntimeError, "external import"):
                self.validate(closure)
        for count in (1, 3, True):
            closure = copy.deepcopy(self.closure)
            closure["project_module_count"] = count
            with self.subTest(count=count), self.assertRaisesRegex(RuntimeError, "module count"):
                self.validate(closure)

    def test_hash_path_and_target_tampering_fail(self) -> None:
        for key, value, expected in (("sha256", "0" * 64, "source changed"),
                                     ("path", "ImbalancedChen/Wrong.lean", "source path")):
            closure = copy.deepcopy(self.closure)
            closure["project_sources"][0][key] = value
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, expected):
                self.validate(closure)
        self.closure["targets"] = [self.provider]
        with self.assertRaisesRegex(RuntimeError, "targets differ"):
            self.validate()

    def test_missing_reachable_project_file_and_false_replay_claim_fail(self) -> None:
        closure = copy.deepcopy(self.closure)
        closure["full_external_kernel_replay_claimed"] = True
        with self.assertRaisesRegex(RuntimeError, "must not claim"):
            self.validate(closure)
        (self.root / "ImbalancedChen/Provider.lean").unlink()
        with self.assertRaisesRegex(RuntimeError, "Missing.*Provider"):
            self.validate()


class ProjectObjectTests(unittest.TestCase):
    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        self.objdir = self.root / ".lake/build/lib/lean"
        self.target = "ImbalancedChen.Terminal"
        self.provider = "ImbalancedChen.Provider"
        self.modules = (self.target, self.provider)
        self.roots = [self.objdir]
        for module in self.modules:
            path = self.part(module)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(("object " + module).encode())
        self.part(self.provider, ".server").write_bytes(b"provider server")
        self.part(self.target, ".private").write_bytes(b"terminal private")

    def part(self, module: str, suffix: str = "") -> Path:
        return self.objdir / (module.replace(".", "/") + ".olean" + suffix)

    def snapshot(self) -> dict:
        return verifier.snapshot_project_objects(self.root, self.roots, self.modules)

    def test_all_modules_and_existing_parts_are_recorded(self) -> None:
        snapshot = self.snapshot()
        self.assertEqual(set(snapshot), set(self.modules))
        for module, suffix in ((self.target, ".private"), (self.provider, ".server")):
            self.assertEqual(snapshot[module]["resolved_olean"], str(self.part(module)))
            self.assertEqual(snapshot[module]["parts"], {
                self.part(module, part).relative_to(self.root).as_posix():
                hashlib.sha256(self.part(module, part).read_bytes()).hexdigest()
                for part in ("", suffix)})

    def test_provider_shadowed_on_lean_path_fails(self) -> None:
        shadow_root = self.root / "shadow"
        shadow = shadow_root / (self.provider.replace(".", "/") + ".olean")
        shadow.parent.mkdir(parents=True)
        shadow.write_bytes(b"unverified provider")
        self.roots.insert(0, shadow_root)
        with self.assertRaisesRegex(RuntimeError, "outside.*Provider"):
            self.snapshot()

    def test_missing_provider_object_fails(self) -> None:
        self.part(self.provider).unlink()
        with self.assertRaisesRegex(RuntimeError, "outside.*Provider"):
            self.snapshot()

    def test_provider_hash_and_sidecar_set_changes_fail(self) -> None:
        for action in ("hash", "add", "remove"):
            with self.subTest(action=action):
                before = self.snapshot()
                path = self.part(self.provider, ".private" if action == "add" else ".server")
                old = path.read_bytes() if path.exists() else None
                if action == "remove":
                    path.unlink()
                else:
                    path.write_bytes(b"changed provider object part")
                after = self.snapshot()
                with self.assertRaisesRegex(RuntimeError, "hashes changed:.*Provider"):
                    verifier.require_frozen_project_objects(before, after, (self.target,))
                if old is None:
                    path.unlink()
                else:
                    path.write_bytes(old)

    def test_strict_terminal_refresh_then_full_audit_freeze(self) -> None:
        built = self.snapshot()
        self.part(self.target).write_bytes(b"strict terminal object")
        self.part(self.target, ".server").write_bytes(b"strict terminal server")
        strict = self.snapshot()
        verifier.require_frozen_project_objects(built, strict, (self.target,))
        verifier.require_frozen_project_objects(strict, self.snapshot())
        self.part(self.target, ".private").unlink()
        with self.assertRaisesRegex(RuntimeError, "hashes changed:.*Terminal"):
            verifier.require_frozen_project_objects(strict, self.snapshot())

    def test_symlink_sidecar_outside_object_tree_fails(self) -> None:
        foreign = self.root / "foreign-private"
        foreign.write_bytes(b"foreign private part")
        self.part(self.provider, ".private").symlink_to(foreign)
        with self.assertRaisesRegex(RuntimeError, "Invalid.*object part"):
            self.snapshot()


if __name__ == "__main__":
    unittest.main()
