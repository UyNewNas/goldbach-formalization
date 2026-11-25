"""Local filesystem/Git fixtures only; never invokes Lean or a remote service."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

try:
    import p24_recover_scoped_baseline as recovery
except ModuleNotFoundError:
    recovery = None


class RecoveryTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(recovery, "Scoped recovery implementation is missing")
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.top = Path(self.temp.name)
        self.baseline = self.top / "baseline"
        self.project = self.top / "project"
        self.donor = self.top / "donor"
        self.baseline.mkdir()
        self.donor.mkdir()
        self.git(self.baseline, "init", "--quiet")
        self.write(self.baseline / ".gitignore", b".lake/\n")
        self.root = recovery.ROOT
        sources = {
            self.root: "import ImbalancedChen.Keep\n",
            "ImbalancedChen.Keep": "def keptValue := 1\n",
            "ImbalancedChen.Drop": "def dropValue := 2\n",
            "ImbalancedChen.RecordKeep": "def recordValue := 3\n",
            "ImbalancedChen.ReceiptKeep": "def receiptValue := 4\n",
            "ImbalancedChen.Changed": "def changedValue := 5\n",
            "ImbalancedChen.Linked": "def linkedValue := 6\n",
            "ImbalancedChen.Later": "def laterValue := 7\n",
        }
        for name, text in sources.items():
            self.write(self.baseline / (name.replace(".", "/") + ".lean"), text.encode())
        self.git(self.baseline, "add", ".")
        self.git(self.baseline, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--quiet", "-m", "fixture")
        self.pin = self.git(self.baseline, "rev-parse", "HEAD").strip()
        self.pin_patch = patch.object(recovery, "BASELINE", self.pin)
        self.pin_patch.start()
        self.addCleanup(self.pin_patch.stop)
        self.git(self.top, "clone", "--quiet", "--shared", str(self.baseline), str(self.project))
        self.git(self.project, "checkout", "--quiet", "-b", recovery.OWN_BRANCH)
        self.base_lib = self.baseline / ".lake/build/lib/lean"
        self.lib = self.project / ".lake/p2-private/lib"
        self.lib.mkdir(parents=True)
        for name in ("Keep", "Drop", "RecordKeep", "ReceiptKeep", "Changed", "Linked"):
            self.write(self.base_lib / f"ImbalancedChen/{name}.olean", (name + "-object").encode())
            self.write(self.lib / f"ImbalancedChen/{name}.olean", (name + "-object").encode())
        self.write(self.base_lib / "ImbalancedChen/Drop.olean.hash", b"same-hash")
        self.write(self.lib / "ImbalancedChen/Drop.olean.hash", b"same-hash")
        self.write(self.lib / "ImbalancedChen/Changed.olean", b"different-target")
        self.write(self.lib / "unknown.bin", b"unknown")
        self.write(self.base_lib / "unknown.bin", b"unknown")
        self.write(self.lib / "ImbalancedChen/Unknown.olean", b"no-known-source")
        self.write(self.base_lib / "ImbalancedChen/Unknown.olean", b"no-known-source")
        self.write(self.base_lib / "ImbalancedChen/Keep.olean.private", b"private-facet")
        self.write(self.base_lib / "ImbalancedChen/Keep.ir", b"ir-facet")
        self.snapshot = self.donor / "EXTERNAL_SNAPSHOT.json"
        self.write(self.snapshot, b'{"fixture_only": true}\n')
        self.receipt = self.project / ".lake/p24-cache-migration/attempt-001/MIGRATION.json"
        self.records = self.project / ".lake/p2-private/records.json"
        receipt = {
            "schema": "p24-verified-private-cache-transport-v1", "status": recovery.MIGRATION_STATUS,
            "root": self.root, "project_root": str(self.project), "donor_root": str(self.donor),
            "actual_project_scope": [self.root, "ImbalancedChen.Keep", "ImbalancedChen.ReceiptKeep"],
            "migrated": {"ImbalancedChen.Keep": {}}, "retained": {},
            "new_source_compilations": 0, "kernel_replays": 0,
            "new_external_binding": {
                "snapshot": str(self.snapshot), "snapshot_sha256": self.sha(self.snapshot),
                "lean_path": [str(self.lib)], "native_modules": [f"Fixture.Native{i}" for i in range(515)]},
        }
        self.write(self.receipt, json.dumps(receipt).encode())
        records = {
            "ImbalancedChen.Keep": {"module": "ImbalancedChen.Keep",
                "object": str(self.lib / "ImbalancedChen/Keep.olean"),
                "verified_cache_migration": {"path": str(self.receipt), "sha256": self.sha(self.receipt)}},
            "ImbalancedChen.RecordKeep": {"module": "ImbalancedChen.RecordKeep",
                "object": str(self.lib / "ImbalancedChen/RecordKeep.olean")},
        }
        self.write(self.records, json.dumps(records).encode())
        self.write(self.project / ".lake/p2-private/p24-migration.lock", b"")

    @staticmethod
    def write(path, raw):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(raw)

    @staticmethod
    def sha(path):
        return hashlib.sha256(path.read_bytes()).hexdigest()

    @staticmethod
    def git(root, *args):
        env = dict(os.environ, GIT_OPTIONAL_LOCKS="0")
        return subprocess.check_output(["git", *args], cwd=root, text=True, stderr=subprocess.PIPE, env=env)

    def fixture(self):
        return recovery.Recovery(self.project, self.baseline, self.donor, self.snapshot)

    def test_plan_is_read_only_and_preserves_unknown_protected_or_different_files(self):
        linked = self.lib / "ImbalancedChen/Linked.olean"
        linked.unlink()
        os.link(self.base_lib / "ImbalancedChen/Linked.olean", linked)
        before = {str(p): self.sha(p) for p in self.project.rglob("*") if p.is_file()}
        run = self.fixture()
        self.assertEqual([r["relative"] for r in run.plan["delete"]],
                         ["ImbalancedChen/Drop.olean", "ImbalancedChen/Drop.olean.hash"])
        self.assertEqual(before, {str(p): self.sha(p) for p in self.project.rglob("*") if p.is_file()})
        self.assertFalse(run.out.exists())
        self.assertFalse(run.mirror_root.exists())

    def test_cleanup_preserves_registry_receipt_baseline_and_protected_objects(self):
        run = self.fixture()
        records, receipt = self.records.read_bytes(), self.receipt.read_bytes()
        baseline = {str(p): self.sha(p) for p in self.baseline.rglob("*") if p.is_file()}
        result = run.recover()
        self.assertEqual(result["deleted_files"], 3)
        self.assertFalse((self.lib / "ImbalancedChen/Drop.olean").exists())
        self.assertTrue((self.lib / "ImbalancedChen/Keep.olean").exists())
        self.assertTrue((self.lib / "ImbalancedChen/RecordKeep.olean").exists())
        self.assertTrue((self.lib / "ImbalancedChen/ReceiptKeep.olean").exists())
        self.assertTrue((self.lib / "ImbalancedChen/Changed.olean").exists())
        self.assertTrue((self.lib / "unknown.bin").exists())
        self.assertEqual(self.records.read_bytes(), records)
        self.assertEqual(self.receipt.read_bytes(), receipt)
        self.assertEqual(baseline, {str(p): self.sha(p) for p in self.baseline.rglob("*") if p.is_file()})
        self.assertTrue((run.out / "RECOVERY.json").is_file())

    def test_cleanup_allocates_no_evidence_before_freeing_a_duplicate(self):
        run = self.fixture()
        original = Path.mkdir
        def full_until_unlinked(path, *args, **kwargs):
            if (self.lib / "ImbalancedChen/Drop.olean").exists():
                raise OSError(28, "fixture: disk full before first unlink")
            return original(path, *args, **kwargs)
        with patch.object(Path, "mkdir", full_until_unlinked):
            run.recover()
        self.assertTrue((run.out / "RECOVERY.json").is_file())

    def test_unpublished_migration_receipt_blocks_cleanup(self):
        records = json.loads(self.records.read_text())
        records["ImbalancedChen.Keep"]["verified_cache_migration"]["sha256"] = "0" * 64
        self.records.write_text(json.dumps(records))
        with self.assertRaises(ValueError):
            self.fixture()
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean").exists())

    def test_wrong_baseline_commit_blocks_cleanup(self):
        with patch.object(recovery, "BASELINE", "0" * 40), self.assertRaises(ValueError):
            self.fixture()

    def test_dirty_baseline_blocks_cleanup(self):
        (self.baseline / "ImbalancedChen/Drop.lean").write_text("changed baseline\n")
        with self.assertRaises(ValueError):
            self.fixture()

    def test_changed_registry_after_plan_blocks_all_deletions(self):
        run = self.fixture()
        self.records.write_bytes(self.records.read_bytes() + b"\n")
        with self.assertRaises(ValueError):
            run.recover()
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean").exists())

    def test_new_registry_after_plan_blocks_all_deletions(self):
        run = self.fixture()
        self.write(self.project / ".lake/p2-private/probe-records.json", b'{"ImbalancedChen.Drop": {}}')
        with self.assertRaises(ValueError):
            run.recover()
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean").exists())

    def test_auxiliary_registry_object_alias_protects_all_of_its_facets(self):
        self.write(self.base_lib / "ImbalancedChen/Linked.olean.private", b"linked-private")
        self.write(self.lib / "ImbalancedChen/Linked.olean.private", b"linked-private")
        self.write(self.project / ".lake/p2-private/probe-records.json",
                   json.dumps({"alias": {"object": str(self.lib / "ImbalancedChen/Linked.olean")}}).encode())
        run = self.fixture()
        run.recover()
        self.assertTrue((self.lib / "ImbalancedChen/Linked.olean").exists())
        self.assertTrue((self.lib / "ImbalancedChen/Linked.olean.private").exists())

    def test_registry_dotdot_reference_protects_its_physical_module_and_facets(self):
        (self.lib / "alias-parent").mkdir()
        alias = self.lib / "alias-parent/../ImbalancedChen/Drop.olean"
        self.write(self.project / ".lake/p2-private/probe-records.json",
                   json.dumps({"alias": {"object": str(alias)}}).encode())
        run = self.fixture()
        self.assertNotIn("ImbalancedChen/Drop.olean", [row["relative"] for row in run.plan["delete"]])
        run.recover()
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean").exists())
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean.hash").exists())

    def test_same_byte_target_replacement_after_plan_is_preserved(self):
        run = self.fixture()
        target = self.lib / "ImbalancedChen/Drop.olean"
        replacement = target.with_suffix(".replacement")
        replacement.write_bytes(target.read_bytes())
        replacement.replace(target)
        inode = target.stat().st_ino
        with self.assertRaises(ValueError):
            run.recover()
        self.assertEqual(target.stat().st_ino, inode)

    def test_changed_baseline_object_after_plan_blocks_deletion(self):
        run = self.fixture()
        (self.base_lib / "ImbalancedChen/Drop.olean").write_bytes(b"changed baseline object")
        with self.assertRaises(ValueError):
            run.recover()
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean").exists())

    def test_symlinked_library_is_rejected_and_nested_symlinks_are_preserved(self):
        outside = self.top / "outside"
        outside.mkdir()
        self.write(outside / "Drop.olean", b"Drop-object")
        (self.lib / "Foreign").symlink_to(outside, target_is_directory=True)
        link = self.lib / "ImbalancedChen/Linked.olean"
        link.unlink()
        link.symlink_to(self.base_lib / "ImbalancedChen/Linked.olean")
        run = self.fixture()
        run.recover()
        self.assertTrue(link.is_symlink())
        self.assertEqual((outside / "Drop.olean").read_bytes(), b"Drop-object")
        moved = self.project / ".lake/p2-private/moved-lib"
        self.lib.rename(moved)
        self.lib.symlink_to(moved, target_is_directory=True)
        with self.assertRaises(ValueError):
            self.fixture()

    def test_partial_hash_file_is_retained(self):
        target = self.lib / "ImbalancedChen/Drop.olean.hash"
        target.write_bytes(b"")
        run = self.fixture()
        run.recover()
        self.assertTrue(target.exists())
        self.assertEqual(target.read_bytes(), b"")

    def test_existing_output_or_mirror_prevents_any_cleanup(self):
        for kind in ("out", "mirror_root"):
            run = self.fixture()
            path = getattr(run, kind)
            path.mkdir(parents=True)
            with self.assertRaises(ValueError):
                run.recover()
            self.assertTrue((self.lib / "ImbalancedChen/Drop.olean").exists())
            path.rmdir()

    def test_scoped_mirror_keeps_same_clean_commit_and_independent_loadable_copies(self):
        before = {str(p): self.sha(p) for p in self.baseline.rglob("*") if p.is_file()}
        run = self.fixture()
        run.recover()
        result = run.build_mirror(full_checkout_limit=1024 * 1024)
        self.assertEqual(self.git(run.mirror_root, "rev-parse", "HEAD").strip(), self.pin)
        self.assertEqual(self.git(run.mirror_root, "status", "--porcelain", "--untracked-files=no").strip(), "")
        mirror_lib = run.mirror_root / ".lake/build/lib/lean"
        files = sorted(str(p.relative_to(mirror_lib)) for p in mirror_lib.rglob("*") if p.is_file())
        self.assertEqual(files, ["ImbalancedChen/Keep.ir", "ImbalancedChen/Keep.olean", "ImbalancedChen/Keep.olean.private"])
        for relative in files:
            copied, original = mirror_lib / relative, self.base_lib / relative
            self.assertFalse(copied.is_symlink())
            self.assertEqual(copied.read_bytes(), original.read_bytes())
            self.assertNotEqual((copied.stat().st_dev, copied.stat().st_ino),
                                (original.stat().st_dev, original.stat().st_ino))
        self.assertEqual(result["new_compile_credit"], False)
        self.assertTrue((run.mirror_root / ".git").is_dir())
        self.assertFalse((run.mirror_root / ".git").is_symlink())
        self.assertEqual(result["git_object_alternates"], [str(self.baseline / ".git/objects")])
        self.assertEqual(before, {str(p): self.sha(p) for p in self.baseline.rglob("*") if p.is_file()})

    def test_sparse_mirror_preserves_required_sources_without_unrelated_sources(self):
        run = self.fixture()
        run.recover()
        result = run.build_mirror(full_checkout_limit=0)
        self.assertEqual(result["checkout_mode"], "sparse")
        self.assertTrue((run.mirror_root / "ImbalancedChen/Keep.lean").is_file())
        self.assertTrue((run.mirror_root / (self.root.replace(".", "/") + ".lean")).is_file())
        self.assertFalse((run.mirror_root / "ImbalancedChen/Drop.lean").exists())
        self.assertEqual(self.git(run.mirror_root, "status", "--porcelain", "--untracked-files=no").strip(), "")

    def test_mirror_uses_current_runtime_source_scope_after_owned_branch_update(self):
        run = self.fixture()
        run.recover()
        self.write(self.base_lib / "ImbalancedChen/Later.olean", b"existing-later-object")
        source = self.project / (self.root.replace(".", "/") + ".lean")
        source.write_text("import ImbalancedChen.Keep\nimport ImbalancedChen.Later\n")
        self.git(self.project, "add", str(source))
        self.git(self.project, "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "commit", "--quiet", "-m", "runtime source update")
        latest = self.git(self.project, "rev-parse", "HEAD").strip()
        resumed = self.fixture()
        result = resumed.build_mirror()
        self.assertEqual(result["runtime_source_head"], latest)
        self.assertIn("ImbalancedChen.Later", result["project_scope"])
        self.assertEqual((resumed.mirror_root / ".lake/build/lib/lean/ImbalancedChen/Later.olean").read_bytes(),
                         b"existing-later-object")
        self.assertEqual(json.loads((resumed.out / "RUNTIME_SOURCE.json").read_text())["source_head"], latest)

    def test_partial_cleanup_records_actual_deletions_and_cannot_build_mirror(self):
        run = self.fixture()
        original = Path.unlink
        def fail_after_first(path, *args, **kwargs):
            if path == self.lib / "ImbalancedChen/Drop.olean.hash":
                raise OSError(5, "fixture interrupted cleanup")
            return original(path, *args, **kwargs)
        with patch.object(Path, "unlink", fail_after_first), self.assertRaises(OSError):
            run.recover()
        result = json.loads((run.out / "RECOVERY.json").read_text())
        self.assertEqual(result["status"], "PARTIAL_RECOVERY_STOPPED")
        self.assertEqual(result["deleted_files"], 1)
        self.assertTrue((self.lib / "ImbalancedChen/Drop.olean.hash").exists())
        with self.assertRaises(ValueError):
            run.build_mirror()

    def test_inherited_lock_must_identify_existing_migration_lock(self):
        run = self.fixture()
        with self.records.open("rb") as wrong, self.assertRaises(ValueError):
            with run.lock(wrong.fileno()):
                self.fail("A registry descriptor cannot substitute for the lock")
        with (self.project / ".lake/p2-private/p24-migration.lock").open("rb") as correct:
            with run.lock(correct.fileno()):
                self.assertFalse(run.out.exists())

    def test_complete_source_runs_from_python_c_without_file_or_bytecode_outputs(self):
        source = Path(recovery.__file__).read_text()
        bootstrap = "ns={'__name__':'fixture_recovery'};exec(" + repr(source) + ",ns);ns['BASELINE']="
        bootstrap += repr(self.pin) + ";raise SystemExit(ns['main']())"
        before = {str(p): self.sha(p) for p in self.project.rglob("*") if p.is_file()}
        env = dict(os.environ, PYTHONPATH=str(Path(recovery.__file__).parent))
        result = subprocess.run(["python3", "-B", "-c", bootstrap, "--project-root", str(self.project),
                                 "--baseline-root", str(self.baseline), "--donor-root", str(self.donor),
                                 "--external-snapshot", str(self.snapshot)], cwd=self.project,
                                capture_output=True, text=True, env=env)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout)["eligible_files"], 3)
        self.assertEqual(before, {str(p): self.sha(p) for p in self.project.rglob("*") if p.is_file()})

    def make_precheckout_clone(self, run, shared=False):
        run.mirror_root.parent.mkdir(parents=True, exist_ok=True)
        recovery.git(self.project, "clone", "--quiet", "--no-checkout", "--no-hardlinks",
                     "--shared" if shared else "--no-local", str(self.baseline), str(run.mirror_root),
                     allow_file=True)

    def test_resume_reuses_independent_precheckout_clone_without_clone_or_cleanup(self):
        run = self.fixture()
        run.recover()
        self.make_precheckout_clone(run)
        objects = run.mirror_root / ".git/objects"
        self.assertFalse((objects / "info/alternates").exists())
        before = {str(p): (p.stat().st_ino, self.sha(p)) for p in objects.rglob("*") if p.is_file()}
        bound = {str(p): p.read_bytes() for p in (self.records, self.receipt, run.out / "RECOVERY.json")}
        original_git = recovery.git
        def forbid_clone(root, *args, **kwargs):
            self.assertNotIn("clone", args, "Resume must not repeat the completed clone")
            return original_git(root, *args, **kwargs)
        with patch.object(recovery, "git", forbid_clone):
            result = run.build_mirror(resume_clone=True)
        self.assertTrue(result["clone_resumed"])
        self.assertEqual(result["git_object_alternates"], [])
        self.assertEqual(result["git_object_storage"], "independent local Git object files")
        self.assertEqual(before, {str(p): (p.stat().st_ino, self.sha(p)) for p in objects.rglob("*") if p.is_file()})
        self.assertEqual(bound, {str(p): p.read_bytes() for p in map(Path, bound)})
        self.assertEqual(self.git(run.mirror_root, "status", "--porcelain", "--untracked-files=no").strip(), "")

    def test_default_still_rejects_existing_precheckout_clone(self):
        run = self.fixture()
        run.recover()
        self.make_precheckout_clone(run)
        with self.assertRaises(ValueError):
            run.build_mirror()
        self.assertEqual([p.name for p in run.mirror_root.iterdir()], [".git"])

    def test_resume_rejects_states_other_than_known_precheckout_interruption(self):
        run = self.fixture()
        run.recover()
        self.make_precheckout_clone(run)
        for relative in ("unrelated.txt", ".git/index", ".lake/build/lib/lean/ImbalancedChen/Keep.olean"):
            with self.subTest(relative=relative):
                path = run.mirror_root / relative
                self.write(path, b"preserve me")
                with self.assertRaises(ValueError):
                    run.build_mirror(resume_clone=True)
                self.assertEqual(path.read_bytes(), b"preserve me")
                path.unlink()
                while path.parent != run.mirror_root and path.parent != run.mirror_root / ".git":
                    path = path.parent
                    path.rmdir()
        self.git(run.mirror_root, "config", "remote.origin.url", str(self.donor))
        with self.assertRaises(ValueError):
            run.build_mirror(resume_clone=True)
        self.git(run.mirror_root, "config", "remote.origin.url", str(self.baseline))
        head = run.mirror_root / ".git/HEAD"
        old_head = head.read_bytes()
        head.write_text("0" * 40 + "\n")
        with self.assertRaises((ValueError, subprocess.CalledProcessError)):
            run.build_mirror(resume_clone=True)
        head.write_bytes(old_head)
        alternate = run.mirror_root / ".git/objects/info/alternates"
        alternate.write_text(str(self.donor) + "\n")
        with self.assertRaises(ValueError):
            run.build_mirror(resume_clone=True)
        alternate.unlink()
        linked = run.mirror_root / ".git/objects/foreign-object"
        linked.symlink_to(self.records)
        with self.assertRaises(ValueError):
            run.build_mirror(resume_clone=True)
        self.assertTrue(linked.is_symlink())

    def test_resume_rejects_git_storage_environment_redirection(self):
        run = self.fixture()
        run.recover()
        self.make_precheckout_clone(run)
        for name in ("GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_OBJECT_DIRECTORY",
                     "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_INDEX_FILE", "GIT_NAMESPACE"):
            with self.subTest(name=name), patch.dict(os.environ, {name: str(self.donor)}):
                with self.assertRaises(ValueError):
                    run.build_mirror(resume_clone=True)
        self.assertEqual([p.name for p in run.mirror_root.iterdir()], [".git"])


if __name__ == "__main__":
    unittest.main()
