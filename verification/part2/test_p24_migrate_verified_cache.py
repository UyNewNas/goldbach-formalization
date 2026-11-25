"""Verified cache transport tests use fixture executables, never Lean credit."""
from __future__ import annotations

import contextlib
from copy import deepcopy
import io
import json
import fcntl
import os
from pathlib import Path
import shutil
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import p24_migrate_verified_cache as migration
import test_private_cache_binding as cache_tests
from test_private_external_snapshot import NativeFixture


class P24CacheMigrationTests(unittest.TestCase):
    def setUp(self):
        self.fixture = cache_tests.ProofCacheBindingTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.native = NativeFixture(self.fixture)
        self.fixture.run_runner(extra_args=self.native.args())
        self.donor = self.fixture.root
        self.target = self.fixture.base / "p24-target"
        shutil.copytree(self.donor / "ImbalancedChen", self.target / "ImbalancedChen")
        self.old_records = self.fixture.records_path.read_bytes()
        self.target_records = self.target / ".lake/p2-private/records.json"
        self.args = SimpleNamespace(project_root=self.target, donor_root=self.donor,
                                    external_snapshot=self.native.path,
                                    out=self.target / ".lake/p24-cache/attempt-001")
        self.patchers = [patch.object(migration, "ROOT", "ImbalancedChen.Page"),
                         patch.object(migration, "LEAN", self.fixture.runner.LEAN),
                         patch.object(migration, "MATHLIB", str(self.fixture.baseline)),
                         patch.object(migration, "PIN", self.fixture.runner.PIN)]
        for p in self.patchers:
            p.start()
            self.addCleanup(p.stop)

    def run_migration(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return migration.Migration(self.args).run()

    def records(self):
        return json.loads(self.target_records.read_text()) if self.target_records.exists() else {}

    def test_exact_old_closures_migrate_without_new_compile_credit(self):
        for suffix in (".olean.private", ".olean.server", ".ir", ".ir.sig"):
            (self.donor / (".lake/p2-private/lib/ImbalancedChen/Page" + suffix)).write_bytes(suffix.encode())
        result = self.run_migration()
        self.assertEqual(result["migrated"], 3)
        records = self.records()
        for name, row in records.items():
            self.assertFalse(row["new_strict_compile"])
            self.assertEqual(row["closure_signature"], self.fixture.runner.closure_signature(row))
            self.assertIn("verified_cache_migration", row)
        page = records["ImbalancedChen.Page"]
        self.assertEqual(page["external_snapshot"]["lean_path"][0], str(self.target / ".lake/p2-private/lib"))
        for suffix in migration.LOAD_SUFFIXES:
            self.assertEqual((self.target / (".lake/p2-private/lib/ImbalancedChen/Page" + suffix)).read_bytes(),
                             (self.donor / (".lake/p2-private/lib/ImbalancedChen/Page" + suffix)).read_bytes())
        self.assertEqual(self.fixture.records_path.read_bytes(), self.old_records)
        receipt = json.loads(Path(result["receipt"]).read_text())
        self.assertEqual(receipt["new_source_compilations"], 0)
        self.assertEqual(receipt["kernel_replays"], 0)
        self.assertEqual(receipt["original_records"]["ImbalancedChen.Page"], json.loads(self.old_records)["ImbalancedChen.Page"])

    def test_changed_target_ancestor_blocks_all_dependent_transport(self):
        (self.target / "ImbalancedChen/Dep.lean").write_text("def baselineValue : Nat := 1\n")
        self.assertEqual(self.run_migration()["migrated"], 0)
        self.assertFalse(self.target_records.exists())

    def test_invalid_original_dependency_signature_is_not_reconstructed(self):
        old = self.fixture.records()
        old["ImbalancedChen.Mid"]["dependency_signatures"]["ImbalancedChen.Dep"] = "0" * 64
        self.fixture.write_records(old)
        result = self.run_migration()
        self.assertEqual(result["migrated"], 1)
        self.assertEqual(set(self.records()), {"ImbalancedChen.Dep"})

    def test_missing_old_external_batch_check_is_not_upgraded(self):
        old = self.fixture.records()
        old["ImbalancedChen.Mid"].pop("external_check")
        self.fixture.write_records(old)
        self.assertEqual(self.run_migration()["migrated"], 1)

    def test_wrong_old_object_is_not_adopted(self):
        (self.donor / ".lake/p2-private/lib/ImbalancedChen/Mid.olean").write_bytes(b"changed")
        self.assertEqual(self.run_migration()["migrated"], 1)

    def test_existing_different_target_object_is_preserved(self):
        path = self.target / ".lake/p2-private/lib/ImbalancedChen/Mid.olean"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"unrelated existing work")
        self.assertEqual(self.run_migration()["migrated"], 1)
        self.assertEqual(path.read_bytes(), b"unrelated existing work")

    def test_extra_target_loadable_facet_is_not_silently_accepted(self):
        path = self.target / ".lake/p2-private/lib/ImbalancedChen/Mid.ir"
        path.parent.mkdir(parents=True)
        path.write_bytes(b"extra current artifact")
        self.assertEqual(self.run_migration()["migrated"], 1)
        self.assertNotIn("ImbalancedChen.Mid", self.records())
        self.assertEqual(path.read_bytes(), b"extra current artifact")

    def test_unrelated_donor_records_do_not_expand_scope(self):
        old = self.fixture.records()
        old["ImbalancedChen.Unrelated"] = deepcopy(old["ImbalancedChen.Dep"])
        self.fixture.write_records(old)
        self.assertEqual(self.run_migration()["migrated"], 3)
        self.assertNotIn("ImbalancedChen.Unrelated", self.records())

    def test_changed_external_input_aborts_without_records(self):
        original = migration.Migration.recheck
        def changed(instance):
            self.native.obj.write_bytes(b"changed during migration")
            return original(instance)
        with patch.object(migration.Migration, "recheck", changed):
            with self.assertRaisesRegex(ValueError, "External physical input changed"):
                self.run_migration()
        self.assertFalse(self.target_records.exists())

    def test_donor_records_concurrent_change_aborts_without_target_records(self):
        original = migration.Migration.recheck
        def changed(instance):
            self.fixture.records_path.write_text(self.fixture.records_path.read_text() + "\n")
            return original(instance)
        with patch.object(migration.Migration, "recheck", changed):
            with self.assertRaisesRegex(ValueError, "Donor records changed"):
                self.run_migration()
        self.assertFalse(self.target_records.exists())

    def test_target_records_concurrent_change_is_preserved(self):
        original = migration.Migration.recheck
        changed_bytes = b'{"concurrent_writer": true}\n'
        def changed(instance):
            self.target_records.write_bytes(changed_bytes)
            return original(instance)
        with patch.object(migration.Migration, "recheck", changed):
            with self.assertRaisesRegex(ValueError, "Target records changed"):
                self.run_migration()
        self.assertEqual(self.target_records.read_bytes(), changed_bytes)

    def test_late_copy_failure_cannot_publish_that_module(self):
        old_path = self.donor / ".lake/p2-private/lib/ImbalancedChen/Mid.ir"
        old_path.write_bytes(b"second facet")
        copy = migration.atomic_missing
        def fail(path, raw, expected):
            if path.name == "Mid.ir":
                raise OSError("fixture partial facet copy failure")
            return copy(path, raw, expected)
        with patch.object(migration, "atomic_missing", side_effect=fail):
            self.assertEqual(self.run_migration()["migrated"], 1)
        self.assertNotIn("ImbalancedChen.Mid", self.records())

    def test_only_project_search_root_may_change_in_external_binding(self):
        a = {"lean_path": ["/old/lib", "/native/lib"], "context_signature": "same"}
        b = {"lean_path": ["/new/lib", "/native/lib"], "context_signature": "same"}
        migration.check_binding_delta(a, b, Path("/old/lib"), Path("/new/lib"))
        for changed in ({**b, "context_signature": "different"},
                        {**b, "lean_path": ["/new/lib", "/another/native"]}):
            with self.assertRaises(ValueError):
                migration.check_binding_delta(a, changed, Path("/old/lib"), Path("/new/lib"))

    def target_dep(self, *, different_object=False, extra_ir=False):
        row = deepcopy(self.fixture.records()["ImbalancedChen.Dep"])
        path = self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean"
        path.parent.mkdir(parents=True)
        source = self.donor / ".lake/p2-private/lib/ImbalancedChen/Dep.olean"
        path.write_bytes(b"independently valid target fixture" if different_object else source.read_bytes())
        row.update(object=str(path), object_sha256=migration.sha(path.read_bytes()))
        row["closure_signature"] = migration.closure_signature(row)
        self.target_records.write_text(json.dumps({"ImbalancedChen.Dep": row}))
        if extra_ir:
            path.with_suffix(".ir").write_bytes(b"different target side facet")
        return path, self.target_records.read_bytes()

    def test_valid_but_different_dependency_cannot_rebind_old_child(self):
        path, original = self.target_dep(different_object=True)
        instance = migration.Migration(self.args)
        nodes = migration.closure(instance.nodes, "ImbalancedChen.Dep")
        migration.verify_compilation(instance.records, nodes,
                                     instance.frozen(instance.project, instance.lib, nodes, instance.binding))
        self.assertEqual(instance.run()["migrated"], 0)
        self.assertEqual(self.target_records.read_bytes(), original)
        self.assertEqual(path.read_bytes(), b"independently valid target fixture")

    def test_full_dependency_facet_set_must_match_even_with_same_public_object(self):
        _, original = self.target_dep(extra_ir=True)
        result = self.run_migration()
        self.assertEqual(result["migrated"], 0)
        self.assertEqual(result["retained"], 1)
        self.assertEqual(self.target_records.read_bytes(), original)

    def test_registry_change_inside_last_long_check_is_not_overwritten(self):
        instance = migration.Migration(self.args)
        verify, calls = instance.external.verify, []
        changed = b'{"other_writer_record": true}\n'
        def mutate():
            calls.append(True)
            if len(calls) == 2:
                self.target_records.write_bytes(changed)
            return verify()
        with patch.object(instance.external, "verify", side_effect=mutate):
            with self.assertRaisesRegex(ValueError, "Target records changed"):
                instance.run()
        self.assertEqual(len(calls), 2)
        self.assertEqual(self.target_records.read_bytes(), changed)
        self.assertFalse((self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean").exists())

    def test_nested_destination_symlink_cannot_escape_owned_tree(self):
        outside = self.fixture.base / "unrelated-work"
        outside.mkdir()
        lib = self.target / ".lake/p2-private/lib"
        lib.mkdir(parents=True)
        (lib / "ImbalancedChen").symlink_to(outside, target_is_directory=True)
        try:
            self.run_migration()
        except (OSError, ValueError):
            pass
        self.assertEqual(list(outside.iterdir()), [])
        self.assertFalse(self.target_records.exists())

    def put_stale_target_dep(self):
        self.target_records.parent.mkdir(parents=True)
        self.target_records.write_text(json.dumps({"ImbalancedChen.Dep": self.fixture.records()["ImbalancedChen.Dep"]}))
        return self.target_records.read_bytes()

    def test_partial_copy_cannot_enable_preexisting_stale_target_record(self):
        original = self.put_stale_target_dep()
        (self.donor / ".lake/p2-private/lib/ImbalancedChen/Dep.ir").write_bytes(b"second facet")
        atomic = migration.atomic_missing
        def fail(path, raw, expected):
            if path.name == "Dep.ir":
                raise OSError("late fixture copy failure")
            return atomic(path, raw, expected)
        with patch.object(migration, "atomic_missing", side_effect=fail):
            self.assertEqual(self.run_migration()["migrated"], 0)
        self.assertFalse((self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean").exists())
        self.assertEqual(self.target_records.read_bytes(), original)

    def test_global_failure_rolls_back_new_facets_without_enabling_stale_record(self):
        original = self.put_stale_target_dep()
        with patch.object(migration.Migration, "recheck", side_effect=ValueError("fixture global failure")):
            with self.assertRaisesRegex(ValueError, "fixture global failure"):
                self.run_migration()
        self.assertFalse((self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean").exists())
        self.assertEqual(self.target_records.read_bytes(), original)

    def test_rollback_preserves_preexisting_valid_files(self):
        path, original = self.target_dep()
        body = path.read_bytes()
        with patch.object(migration.Migration, "recheck", side_effect=ValueError("fixture global failure")):
            with self.assertRaisesRegex(ValueError, "fixture global failure"):
                self.run_migration()
        self.assertEqual(path.read_bytes(), body)
        self.assertEqual(self.target_records.read_bytes(), original)
        self.assertFalse((self.target / ".lake/p2-private/lib/ImbalancedChen/Mid.olean").exists())

    def test_rollback_preserves_concurrently_replaced_object(self):
        path = self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean"
        replacement = b"concurrent writer owns this replacement"
        def replace(_):
            path.unlink()
            path.write_bytes(replacement)
            raise ValueError("fixture replacement")
        with patch.object(migration.Migration, "recheck", replace):
            with self.assertRaisesRegex(ValueError, "Could not safely roll back"):
                self.run_migration()
        self.assertEqual(path.read_bytes(), replacement)
        self.assertFalse(self.target_records.exists())

    def test_valid_target_records_are_retained_without_registry_change(self):
        self.assertEqual(self.run_migration()["migrated"], 3)
        saved = self.target_records.read_bytes()
        self.args.out = self.target / ".lake/p24-cache/attempt-002"
        result = self.run_migration()
        self.assertEqual((result["migrated"], result["retained"]), (0, 3))
        self.assertEqual(self.target_records.read_bytes(), saved)

    def test_original_strict_consumer_reuses_all_migrated_fixture_records(self):
        self.assertEqual(self.run_migration()["migrated"], 3)
        self.fixture.root = self.target
        self.fixture.cache = self.target / ".lake/p2-private"
        self.fixture.records_path = self.target_records
        self.assertEqual(self.fixture.run_runner(extra_args=self.native.args())["reused"], 3)

    def test_concurrent_migration_lock_is_observed_before_any_active_copy(self):
        instance = migration.Migration(self.args)
        path = self.target / ".lake/p2-private/p24-migration.lock"
        descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            with self.assertRaises(BlockingIOError):
                instance.run()
        finally:
            os.close(descriptor)
        self.assertFalse((self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean").exists())

    def test_same_byte_replacement_after_link_is_never_claimed_as_our_inode(self):
        (self.donor / ".lake/p2-private/lib/ImbalancedChen/Dep.ir").write_bytes(b"force later failure")
        target = self.target / ".lake/p2-private/lib/ImbalancedChen/Dep.olean"
        original_link, original_copy, replacements = migration.os.link, migration.atomic_missing, []
        expected = (self.donor / ".lake/p2-private/lib/ImbalancedChen/Dep.olean").read_bytes()
        def replace_after_link(source, destination, *args, **kwargs):
            result = original_link(source, destination, *args, **kwargs)
            if str(destination) == "Dep.olean" and "dst_dir_fd" in kwargs:
                own_inode = target.stat().st_ino
                foreign = target.with_suffix(".foreign")
                foreign.write_bytes(target.read_bytes())
                foreign_inode = foreign.stat().st_ino
                foreign.replace(target)
                replacements.append((own_inode, foreign_inode))
            return result
        def fail_later(path, raw, expected):
            if path.name == "Dep.ir":
                raise OSError("fixture later copy failure")
            return original_copy(path, raw, expected)
        with patch.object(migration.os, "link", side_effect=replace_after_link), \
                patch.object(migration, "atomic_missing", side_effect=fail_later):
            with self.assertRaisesRegex(ValueError, "Could not safely roll back"):
                self.run_migration()
        self.assertEqual(len(replacements), 1)
        self.assertNotEqual(*replacements[0])
        self.assertEqual(target.stat().st_ino, replacements[0][1])
        self.assertEqual(target.read_bytes(), expected)
        self.assertFalse(self.target_records.exists())


if __name__ == "__main__":
    unittest.main()
