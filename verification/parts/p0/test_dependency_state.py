"""Adversarial temporary Git fixtures only; no real dependency, Lean, or network use."""
from __future__ import annotations

from copy import deepcopy
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parents[2]
spec = importlib.util.spec_from_file_location("fixture_dependency_verifier", HERE / "verify_dependency_state.py")
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)
PRODUCTION_PINS = dict(verifier.PINS)
PRODUCTION_HASHES = dict(verifier.BUNDLE_SHA256)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], stderr=subprocess.PIPE)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def initialize_git(root):
    subprocess.run(["git", "init", "-q", str(root)], check=True, capture_output=True)
    git(root, "config", "user.name", "Synthetic fixture")
    git(root, "config", "user.email", "fixture@example.invalid")
    git(root, "add", ".")
    git(root, "commit", "-qm", "Synthetic fixture only")


def snapshot(root):
    return {str(p.relative_to(root)): ("symlink", p.readlink().as_posix()) if p.is_symlink()
            else ("file", sha(p.read_bytes()), p.stat().st_mode)
            for p in root.rglob("*") if p.is_file() or p.is_symlink()}


class ProductionAnchorTests(unittest.TestCase):
    def test_checked_in_bundle_is_exact_and_transitively_bound(self):
        manifest, hashes = verifier.load_overlay(PROJECT)
        self.assertEqual(hashes, PRODUCTION_HASHES)
        self.assertEqual(manifest["basePin"], PRODUCTION_PINS["goldbach"])
        self.assertEqual(len(manifest["files"]), 3)

    def test_original_pin_table_is_unchanged(self):
        self.assertEqual(len(PRODUCTION_PINS), 11)
        lock = json.loads((PROJECT / "lake-manifest.json").read_text())
        self.assertEqual({p["name"]: p["rev"] for p in lock["packages"]}, PRODUCTION_PINS)
        self.assertEqual((PROJECT / "lean-toolchain").read_text().strip(), verifier.TOOLCHAIN)


class DependencyStateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.template_temp = tempfile.TemporaryDirectory(prefix="synthetic-dependency-template-")
        cls.template = Path(cls.template_temp.name)
        cls.pins, cls.patched = {}, {}
        for name in PRODUCTION_PINS:
            root = cls.template / ".lake/packages" / name
            root.mkdir(parents=True)
            (root / "untouched.lean").write_text("synthetic source for " + name + "\n")
            if name == "goldbach":
                for index, relative in enumerate(sorted(verifier.OVERLAY_FILES)):
                    target = root / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    target.write_text(f"synthetic base {index}\n")
                    cls.patched[relative] = f"synthetic exact patched {index}\n".encode()
            initialize_git(root)
            cls.pins[name] = git(root, "rev-parse", "HEAD").decode().strip()
        (cls.template / "lean-toolchain").write_text(verifier.TOOLCHAIN + "\n")
        lock = json.loads((PROJECT / "lake-manifest.json").read_text())
        for item in lock["packages"]:
            item["rev"] = cls.pins[item["name"]]
        write_json(cls.template / "lake-manifest.json", lock)
        for relative in PRODUCTION_HASHES:
            target = cls.template / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes((PROJECT / relative).read_bytes())
        bundle = cls.template / verifier.BUNDLE
        manifest = json.loads((bundle / "manifest.json").read_text())
        manifest["basePin"] = cls.pins["goldbach"]
        (bundle / "dependency.patch").write_bytes(b"synthetic fixture patch; never executed\n")
        manifest["patchSha256"] = sha((bundle / "dependency.patch").read_bytes())
        dep = cls.template / ".lake/packages/goldbach"
        for relative, metadata in manifest["files"].items():
            metadata["baseGitBlob"] = git(dep, "rev-parse", "HEAD:" + relative).decode().strip()
            metadata["baseSha256"] = sha((dep / relative).read_bytes())
            metadata["patchedSha256"] = sha(cls.patched[relative])
        write_json(bundle / "manifest.json", manifest)
        review = json.loads((bundle / "acceptance-review.json").read_text())
        review.update(basePin=manifest["basePin"], files=manifest["files"],
                      manifestSha256=sha((bundle / "manifest.json").read_bytes()),
                      overlayPatchSha256=manifest["patchSha256"])
        write_json(bundle / "acceptance-review.json", review)
        activation = dict(status="PASS", manifestSha256=review["manifestSha256"],
                          reviewSha256=sha((bundle / "acceptance-review.json").read_bytes()))
        write_json(bundle / "activation.json", activation)
        cls.hashes = {relative: sha((cls.template / relative).read_bytes()) for relative in PRODUCTION_HASHES}

    @classmethod
    def tearDownClass(cls):
        cls.template_temp.cleanup()

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="synthetic-dependency-case-")
        self.root = Path(self.temp.name) / "project"
        shutil.copytree(self.template, self.root)
        self.dep = self.root / ".lake/packages/goldbach"
        self.addCleanup(self.temp.cleanup)
        self.patch_pins = patch.dict(verifier.PINS, self.pins, clear=True)
        self.patch_hashes = patch.dict(verifier.BUNDLE_SHA256, self.hashes, clear=True)
        self.patch_pins.start()
        self.patch_hashes.start()
        self.addCleanup(self.patch_hashes.stop)
        self.addCleanup(self.patch_pins.stop)

    def apply_fixture(self):
        # Writes only synthetic fixture bytes, not the actual overlay or a real dependency.
        for relative, data in self.patched.items():
            (self.dep / relative).write_bytes(data)

    def verify(self, state="goldbach-stage002-exact"):
        return verifier.verify_dependency_state(self.root, state)

    def test_original_clean_passes_and_is_read_only(self):
        before = snapshot(self.root)
        result = self.verify("original-clean")
        self.assertEqual(snapshot(self.root), before)
        self.assertIsNone(result["overlay_patch_sha256"])
        self.assertEqual(result["overlay_sources"], {})
        self.assertTrue(all(not changes for changes in result["tracked_changed_files"].values()))

    def test_exact_overlay_passes_and_is_read_only(self):
        self.apply_fixture()
        before = snapshot(self.root)
        result = self.verify()
        self.assertEqual(snapshot(self.root), before)
        self.assertEqual(set(result["overlay_sources"]), verifier.OVERLAY_FILES)
        self.assertEqual(set(result["tracked_changed_files"]["goldbach"]), verifier.OVERLAY_FILES)
        self.assertIn("not original fixed source", result["source_classification"])
        self.assertFalse(result["dependency_mutation_performed"])
        self.assertEqual(result, self.verify())

    def test_original_mode_rejects_exact_overlay(self):
        self.apply_fixture()
        with self.assertRaisesRegex(RuntimeError, "tracked dependency files changed"):
            self.verify("original-clean")

    def test_overlay_mode_rejects_clean_and_mixed_sources(self):
        with self.assertRaisesRegex(RuntimeError, "exactly.*three-file"):
            self.verify()
        relative = next(iter(self.patched))
        (self.dep / relative).write_bytes(self.patched[relative])
        with self.assertRaisesRegex(RuntimeError, "exactly.*three-file"):
            self.verify()

    def test_overlay_rejects_single_byte_change(self):
        self.apply_fixture()
        relative = next(iter(self.patched))
        with (self.dep / relative).open("ab") as handle:
            handle.write(b" ")
        with self.assertRaisesRegex(RuntimeError, "Patched source SHA mismatch"):
            self.verify()

    def test_overlay_rejects_extra_tracked_change(self):
        self.apply_fixture()
        (self.dep / "untouched.lean").write_text("changed\n")
        with self.assertRaisesRegex(RuntimeError, "exactly.*three-file"):
            self.verify()

    def test_other_packages_remain_clean(self):
        self.apply_fixture()
        for name in set(self.pins) - {"goldbach"}:
            with self.subTest(package=name):
                target = self.root / ".lake/packages" / name / "untouched.lean"
                original = target.read_bytes()
                target.write_text("changed\n")
                with self.assertRaisesRegex(RuntimeError, "tracked dependency files changed"):
                    self.verify()
                target.write_bytes(original)

    def test_staged_change_rejected_even_when_worktree_restores_head_bytes(self):
        self.apply_fixture()
        target = self.dep / "untouched.lean"
        original = target.read_bytes()
        target.write_text("staged change\n")
        git(self.dep, "add", "untouched.lean")
        target.write_bytes(original)
        with self.assertRaisesRegex(RuntimeError, "staged dependency changes"):
            self.verify()

    def test_staging_the_exact_overlay_is_rejected(self):
        self.apply_fixture()
        git(self.dep, "add", ".")
        with self.assertRaisesRegex(RuntimeError, "staged dependency changes"):
            self.verify()

    def test_hidden_index_flags_are_rejected(self):
        self.apply_fixture()
        for flag, undo in [("--assume-unchanged", "--no-assume-unchanged"),
                           ("--skip-worktree", "--no-skip-worktree")]:
            with self.subTest(flag=flag):
                git(self.dep, "update-index", flag, "untouched.lean")
                with self.assertRaisesRegex(RuntimeError, "hidden/skip-worktree"):
                    self.verify()
                git(self.dep, "update-index", undo, "untouched.lean")

    def test_untracked_and_ignored_extra_sources_are_rejected(self):
        self.apply_fixture()
        for ignored in [False, True]:
            with self.subTest(ignored=ignored):
                if ignored:
                    (self.dep / ".git/info/exclude").write_text("extra.lean\n")
                target = self.dep / "extra.lean"
                target.write_text("unexpected source\n")
                with self.assertRaisesRegex(RuntimeError, "extra untracked dependency content"):
                    self.verify()
                target.unlink()

    def test_dependency_build_outputs_are_allowed_without_being_modified(self):
        self.apply_fixture()
        out = self.dep / ".lake/build/generated.olean"
        out.parent.mkdir(parents=True)
        out.write_bytes(b"synthetic build output")
        before = snapshot(self.root)
        self.verify()
        self.assertEqual(snapshot(self.root), before)

    def test_wrong_head_is_rejected(self):
        self.apply_fixture()
        git(self.dep, "commit", "--allow-empty", "-qm", "wrong synthetic head")
        with self.assertRaisesRegex(RuntimeError, "checkout revision differs"):
            self.verify()

    def test_wrong_toolchain_and_manifest_pins_are_rejected(self):
        self.apply_fixture()
        toolchain = self.root / "lean-toolchain"
        toolchain.write_text("wrong\n")
        with self.assertRaisesRegex(RuntimeError, "Toolchain pin changed"):
            self.verify()
        toolchain.write_text(verifier.TOOLCHAIN + "\n")
        lock = json.loads((self.root / "lake-manifest.json").read_text())
        lock["packages"][0]["rev"] = "0" * 40
        write_json(self.root / "lake-manifest.json", lock)
        with self.assertRaisesRegex(RuntimeError, "Manifest pins changed"):
            self.verify()

    def test_duplicate_manifest_package_is_rejected(self):
        lock = json.loads((self.root / "lake-manifest.json").read_text())
        lock["packages"].append(deepcopy(lock["packages"][0]))
        write_json(self.root / "lake-manifest.json", lock)
        with self.assertRaisesRegex(RuntimeError, "Manifest pins changed"):
            self.verify("original-clean")

    def test_missing_dependency_is_not_silently_skipped(self):
        shutil.rmtree(self.root / ".lake/packages/Cli")
        with self.assertRaisesRegex(RuntimeError, "Missing materialized dependency"):
            self.verify("original-clean")

    def test_working_executable_mode_is_rejected_even_if_git_config_ignores_it(self):
        self.apply_fixture()
        git(self.dep, "config", "core.fileMode", "false")
        relative = next(iter(self.patched))
        target = self.dep / relative
        target.chmod(0o755)
        with self.assertRaisesRegex(RuntimeError, "Executable overlay source"):
            self.verify()

    def test_unrelated_executable_mode_is_rejected_in_original_mode(self):
        git(self.dep, "config", "core.fileMode", "false")
        (self.dep / "untouched.lean").chmod(0o755)
        with self.assertRaisesRegex(RuntimeError, "tracked dependency files changed"):
            self.verify("original-clean")

    def test_overlay_source_symlink_is_rejected(self):
        self.apply_fixture()
        relative = next(iter(self.patched))
        target = self.dep / relative
        elsewhere = self.root / "same-bytes.lean"
        elsewhere.write_bytes(target.read_bytes())
        target.unlink()
        target.symlink_to(elsewhere)
        with self.assertRaisesRegex(RuntimeError, "Symlink path rejected"):
            self.verify()

    def test_dependency_directory_symlink_is_rejected(self):
        elsewhere = self.root / "other-dependency"
        self.dep.rename(elsewhere)
        self.dep.symlink_to(elsewhere, target_is_directory=True)
        with self.assertRaisesRegex(RuntimeError, "Symlink path rejected"):
            self.verify("original-clean")

    def test_each_bundle_file_is_independently_hash_pinned(self):
        self.apply_fixture()
        for relative in PRODUCTION_HASHES:
            with self.subTest(file=relative):
                path = self.root / relative
                original = path.read_bytes()
                path.write_bytes(original + b" ")
                with self.assertRaisesRegex(RuntimeError, "evidence hash changed"):
                    self.verify()
                path.write_bytes(original)

    def test_self_consistent_replacement_bundle_is_not_automatically_trusted(self):
        self.apply_fixture()
        bundle = self.root / verifier.BUNDLE
        manifest = json.loads((bundle / "manifest.json").read_text())
        manifest["authorizationReference"] = "untrusted new authorization claim"
        write_json(bundle / "manifest.json", manifest)
        review = json.loads((bundle / "acceptance-review.json").read_text())
        review["manifestSha256"] = sha((bundle / "manifest.json").read_bytes())
        write_json(bundle / "acceptance-review.json", review)
        write_json(bundle / "activation.json", dict(status="PASS", manifestSha256=review["manifestSha256"],
                    reviewSha256=sha((bundle / "acceptance-review.json").read_bytes())))
        with self.assertRaisesRegex(RuntimeError, "evidence hash changed"):
            self.verify()

    def test_inherited_git_routing_does_not_redirect_checks(self):
        self.apply_fixture()
        before = self.verify()
        with patch.dict("os.environ", {"GIT_DIR": "/nonexistent", "GIT_WORK_TREE": "/nonexistent",
                                       "GIT_INDEX_FILE": "/nonexistent", "GIT_CONFIG_COUNT": "999"}):
            self.assertEqual(self.verify(), before)

    def test_changes_between_snapshots_cannot_pass(self):
        self.apply_fixture()
        before = self.verify()
        self.assertEqual(before, self.verify())
        (self.dep / next(iter(self.patched))).write_text("changed after export\n")
        with self.assertRaisesRegex(RuntimeError, "Patched source SHA mismatch"):
            self.verify()

    def exporter_fixture(self, round_number):
        module_spec = importlib.util.spec_from_file_location(
            f"fixture_round{round_number}", HERE / f"check_round{round_number}_types.py")
        module = importlib.util.module_from_spec(module_spec)
        module_spec.loader.exec_module(module)
        module.ROOT = self.root
        for relative in [*verifier.EVIDENCE_FILES, "verification/parts/p0/check_pins.py",
                         f"verification/parts/p0/check_round{round_number}_types.py", "lakefile.toml"]:
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            # Preserve the synthetic evidence binding rather than replacing it with production bytes.
            if relative not in verifier.BUNDLE_SHA256:
                target.write_bytes((PROJECT / relative).read_bytes())
        helper = self.root / "verification/verify_variable_envelope_boxes.py"
        helper.write_text("def lean_code(text):\n    return text\n")
        (self.root / ".gitignore").write_text(".lake/\n__pycache__/\n")
        audit = self.root / module.AUDIT
        audit.parent.mkdir(parents=True, exist_ok=True)
        audit.write_text("-- Synthetic fixture only. Never compiled.\n")
        targets = getattr(module, "MODULES", getattr(module, "EXPECTED", {}))
        for name in set(targets) | {"ImbalancedChen", module.FINAL_MODULE}:
            source = self.root / (name.replace(".", "/") + ".lean")
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text("-- Synthetic fixture only. Never compiled.\n")
            obj = self.root / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            obj.write_bytes(b"synthetic object, not a Lean object")
        for relative in module.FROZEN:
            target = self.root / relative
            if not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((PROJECT / relative).read_bytes())
        initialize_git(self.root)
        module.FROZEN = {name: sha((self.root / name).read_bytes()) for name in module.FROZEN}
        helper_module = types.ModuleType("verification.verify_variable_envelope_boxes")
        helper_module.lean_code = lambda text: text
        return module, helper_module

    def run_exporter_fixture(self, round_number, *, mutate_during_export=False, preflight_bad=False):
        import io
        module, helper = self.exporter_fixture(round_number)
        self.apply_fixture()
        if preflight_bad:
            (self.dep / next(iter(self.patched))).write_text("preflight corruption\n")
        calls = []
        project_index_before = (self.root / ".git/index").read_bytes()

        def fake_run(command, **kwargs):
            calls.append(command)
            if command[1] == "verification/parts/p0/check_pins.py":
                self.assertEqual(command[-2:], ["--expected-state", "goldbach-stage002-exact"])
                kwargs["stdout"].write(json.dumps(self.verify()).encode())
            else:
                self.assertEqual(command[1:3], ["env", "lean"])
                output = Path(command[command.index("-o") + 1])
                output.write_bytes(b"synthetic audit object, no Lean was run")
                if mutate_during_export:
                    (self.dep / next(iter(self.patched))).write_text("changed during synthetic export\n")
            return types.SimpleNamespace(returncode=0)

        targets = getattr(module, "MODULES", getattr(module, "EXPECTED", {}))
        declaration = dict(name="fixture", module=next(iter(targets)), axioms=["propext"])
        bridge = dict(axioms=["propext"], type="hLower hUpper", readable_type="hLower hUpper")
        parsed = ([declaration], bridge)
        if round_number in (3, 6):
            parsed += ([dict(module=declaration["module"], serialized_constant_count=1,
                shared_constant_count=0, occurrences=[dict(raw_dependency_axioms=["propext"])])],)
        fake_subprocess = types.SimpleNamespace(run=fake_run, check_output=subprocess.check_output)
        stdout, stderr = io.TextIOWrapper(io.BytesIO()), io.TextIOWrapper(io.BytesIO())
        with patch.dict(sys.modules, {"verification.verify_variable_envelope_boxes": helper,
                                      "verification.parts.p0.verify_dependency_state": verifier}), \
             patch.object(module, "subprocess", fake_subprocess), \
             patch.object(module.shutil, "which", return_value="/synthetic/lake"), \
             patch.object(module, "parse_types", return_value=parsed), \
             patch.object(sys, "argv", ["synthetic-exporter"]), \
             patch.object(sys, "stdout", stdout), patch.object(sys, "stderr", stderr):
            result = module.main()
        self.assertEqual((self.root / ".git/index").read_bytes(), project_index_before)
        paths = list((self.root / f".lake/part0-round{round_number}-types").glob("*/receipt.json"))
        self.assertEqual(len(paths), 1)
        return result, json.loads(paths[0].read_text()), calls

    def test_round3_exporter_receipt_binds_exact_overlay_before_and_after(self):
        code, receipt, calls = self.run_exporter_fixture(3)
        self.assertEqual(code, 0)
        self.assertEqual(receipt["status"], "PASS")
        self.assertEqual(receipt["dependency_state_before"], receipt["dependency_state_after"])
        self.assertEqual(receipt["dependency_state_before"]["expected_state"], "goldbach-stage002-exact")
        self.assertIn("not original fixed source", receipt["scope"])
        self.assertEqual(len(calls), 2)
        self.assertTrue(set(verifier.EVIDENCE_FILES) <= set(receipt["inputs_before"]["source_sha256"]))

    def test_round4_exporter_receipt_binds_exact_overlay_before_and_after(self):
        code, receipt, calls = self.run_exporter_fixture(4)
        self.assertEqual(code, 0)
        self.assertEqual(receipt["status"], "PASS")
        self.assertEqual(receipt["dependency_state_before"], receipt["dependency_state_after"])
        self.assertEqual(receipt["dependency_state_after"]["expected_state"], "goldbach-stage002-exact")
        self.assertIn("not original fixed source", receipt["scope"])
        self.assertEqual(len(calls), 2)

    def test_round3_post_export_dependency_tampering_invalidates_receipt(self):
        code, receipt, _ = self.run_exporter_fixture(3, mutate_during_export=True)
        self.assertEqual(code, 1)
        self.assertEqual(receipt["status"], "FAILED")
        self.assertTrue(any("Postcheck" in failure and "Patched source SHA mismatch" in failure
                            for failure in receipt["failures"]))

    def test_round4_post_export_dependency_tampering_invalidates_receipt(self):
        code, receipt, _ = self.run_exporter_fixture(4, mutate_during_export=True)
        self.assertEqual(code, 1)
        self.assertEqual(receipt["status"], "FAILED")
        self.assertTrue(any("Postcheck" in failure and "Patched source SHA mismatch" in failure
                            for failure in receipt["failures"]))

    def test_bad_dependency_blocks_exporter_before_any_lean_or_pin_subprocess(self):
        code, receipt, calls = self.run_exporter_fixture(3, preflight_bad=True)
        self.assertEqual(code, 1)
        self.assertEqual(receipt["status"], "FAILED")
        self.assertFalse(receipt["lean_invocation_started"])
        self.assertEqual(calls, [])

    def test_round6_exporter_receipt_binds_exact_overlay_before_and_after(self):
        code, receipt, calls = self.run_exporter_fixture(6)
        self.assertEqual(code, 0)
        self.assertEqual(receipt["status"], "PASS")
        self.assertEqual(receipt["dependency_state_before"], receipt["dependency_state_after"])
        self.assertEqual(receipt["dependency_state_before"]["expected_state"], "goldbach-stage002-exact")
        self.assertIn("not original fixed source", receipt["scope"])
        self.assertEqual(len(calls), 2)
        self.assertTrue(set(verifier.EVIDENCE_FILES) <= set(receipt["inputs_before"]["source_sha256"]))

    def test_round6_post_export_dependency_tampering_invalidates_receipt(self):
        code, receipt, _ = self.run_exporter_fixture(6, mutate_during_export=True)
        self.assertEqual(code, 1)
        self.assertEqual(receipt["status"], "FAILED")
        self.assertTrue(any("Postcheck" in failure and "Patched source SHA mismatch" in failure
                            for failure in receipt["failures"]))

    def test_round6_bad_dependency_prevents_lean_invocation(self):
        code, receipt, calls = self.run_exporter_fixture(6, preflight_bad=True)
        self.assertEqual(code, 1)
        self.assertEqual(receipt["status"], "FAILED")
        self.assertFalse(receipt["lean_invocation_started"])
        self.assertEqual(calls, [])

    def test_base_blob_and_mode_are_checked_independently(self):
        self.apply_fixture()
        original_git = verifier.git
        for old, new in [(b"100644", b"100755"), (b" blob ", b" tree ")]:
            with self.subTest(replacement=new):
                def changed_tree(directory, *args):
                    result = original_git(directory, *args)
                    return result.replace(old, new, 1) if args[0] == "ls-tree" else result
                with patch.object(verifier, "git", side_effect=changed_tree):
                    with self.assertRaisesRegex(RuntimeError, "Base blob/mode mismatch"):
                        self.verify()
        manifest, hashes = verifier.load_overlay(self.root)
        for field in ["baseGitBlob", "baseSha256"]:
            with self.subTest(field=field):
                invalid = deepcopy(manifest)
                invalid["files"][next(iter(self.patched))][field] = "0" * (40 if field == "baseGitBlob" else 64)
                with patch.object(verifier, "load_overlay", return_value=(invalid, hashes)):
                    with self.assertRaisesRegex(RuntimeError, "Base blob/mode mismatch|Base source SHA mismatch"):
                        self.verify()

    def test_unsafe_relative_paths_are_rejected(self):
        for relative in ["", "../outside", "/absolute", "a/../b", "a/./b", "a//b", "a\\b"]:
            with self.subTest(path=relative):
                with self.assertRaisesRegex(RuntimeError, "Unsafe relative path"):
                    verifier.safe_path(self.root, relative)

    def test_missing_and_symlinked_overlay_evidence_are_rejected(self):
        self.apply_fixture()
        relative = next(iter(verifier.BUNDLE_SHA256))
        path = self.root / relative
        content = path.read_bytes()
        path.unlink()
        with self.assertRaisesRegex(RuntimeError, "Missing historical overlay evidence"):
            self.verify()
        other = self.root / "identical-evidence.py"
        other.write_bytes(content)
        path.symlink_to(other)
        with self.assertRaisesRegex(RuntimeError, "Symlink path rejected"):
            self.verify()

    def test_unknown_expected_state_is_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "Unknown expected dependency state"):
            self.verify("allow-any-dirty")

    def test_original_mode_also_rejects_dirty_other_package(self):
        target = self.root / ".lake/packages/mathlib/untouched.lean"
        target.write_text("changed\n")
        with self.assertRaisesRegex(RuntimeError, "tracked dependency files changed"):
            self.verify("original-clean")


if __name__ == "__main__":
    unittest.main()
