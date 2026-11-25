"""Small storage fixtures only: no Lean compiler, audit or stock replay is run."""
from __future__ import annotations

import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import import_winner9_ci_artifacts as I


SCRIPT = Path(__file__).with_name("import_winner9_external_archive.py")
COMMIT = "94c7c507ab747cf4e05a4f19d8d4507cedfede38"
INDEX = "687c35f8ef018ad85e7cc68581dcadd98cd0acd22bd22f031dfd95966abfc70e"
CHILD = "45611402948-1-" + INDEX[:12]
RELATIVE = ".lake/p2-private/ci-imports/" + CHILD


def digest(data):
    return hashlib.sha256(data).hexdigest()


def put(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
    return digest(data)


class Fixture:
    def __init__(self, base, other=None):
        self.root = base / "proof"
        self.incoming = (other or base) / "incoming"
        self.temporary = (other or base) / "staging"
        self.parent = (other or base) / "retained"
        for directory in (self.root, self.incoming, self.temporary, self.parent):
            directory.mkdir()
        self.records = self.root / I.PRIVATE / "records.json"
        # A full receiver registry, not the 93-record public bootstrap fixture.
        old = {f"old.{n}": {"preserve": n, "object": f"historical/{n}"} for n in range(414)}
        new = {f"new.{n}": {"origin": n} for n in range(598)}
        self.old = (json.dumps(old, indent=1) + "\n\n").encode()
        self.merged = (json.dumps(dict(old, **new), indent=3) + "\n\n\n").encode()
        put(self.records, self.old)
        index_raw = json.dumps({"run_attempt": 1}).encode()
        put(self.incoming / "index.json", index_raw)
        self.files = {I.PRIVATE + "/lib/New.olean": b"original object\x00\xff",
                      I.PRIVATE + "/audit/New/attempt-1/receipt.json": b'{"original":true}\n'}
        hashes = {name: digest(raw) for name, raw in self.files.items()}
        imported = {"run_id": "45611402948", "commit": COMMIT, "index_sha256": INDEX,
                    "records_before_sha256": digest(self.old), "records_after_sha256": digest(self.merged),
                    "modules": sorted(new), "installed_files": hashes, "terminal_integrated": False}
        self.archive_payloads = {
            "index.json": index_raw, "bootstrap.tar.gz": b"preserved original bootstrap",
            "blocks/08/control/original.json": b'{"unaltered":"producer"}\n',
            "local-records-before.json": self.old,
            "import-receipt.json": (json.dumps(imported, indent=2) + "\n").encode(),
        }
        self.verified = {
            "stage": self.temporary / "worktree", "archive": self.temporary / "archive",
            "archive_relative": RELATIVE, "files": hashes,
            "archive_files": {name: digest(raw) for name, raw in self.archive_payloads.items()},
            "inputs": {self.records: digest(self.old), self.incoming / "index.json": digest(index_raw)},
            "records_path": self.records, "merged_raw": self.merged,
            "old_snapshot": {"fixture": "unchanged"}, "base": {}, "toolchain": {},
        }
        self.populate(self.temporary)
        runtime = self.root / ".lake/p210-tools" / ("a" * 40) / SCRIPT.name
        runtime_sha = put(runtime, b"fixture storage adapter identity\n")
        self.adapter = {"commit": "a" * 40, "sha256": runtime_sha, "path": str(runtime)}
        self.state = {"committed": False, "phase": "installation"}

    def populate(self, temporary):
        self.temporary = temporary
        self.verified["stage"] = temporary / "worktree"
        self.verified["archive"] = temporary / "archive"
        for name, data in self.files.items():
            put(self.verified["stage"] / name, data)
        for name, data in self.archive_payloads.items():
            put(self.verified["archive"] / name, data)

    @property
    def external(self):
        return self.parent / CHILD

    @property
    def internal(self):
        return self.root / RELATIVE


class ExternalArchiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if SCRIPT.is_file():
            spec = importlib.util.spec_from_file_location("winner9_external_archive", SCRIPT)
            cls.module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(cls.module)
        else:
            cls.module = None

    def setUp(self):
        self.assertIsNotNone(self.module, "The external-archive adapter does not exist yet")
        self.addCleanup(mock.patch.stopall)
        mock.patch.object(self.module, "RESERVE_BYTES", 4096).start()
        mock.patch.object(self.module, "verify_proof_source").start()
        self.snapshot = mock.patch.object(I.A, "snapshot", return_value={"fixture": "unchanged"}).start()
        self.f = self.fixture()

    def fixture(self, other=None):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        return Fixture(Path(temporary.name), other)

    def install(self, fixture=None):
        f = fixture or self.f
        return self.module.install_split_archive(I, f.root, f.incoming, f.temporary,
                                                 f.parent, f.verified, f.adapter, f.state)

    def unchanged(self, fixture=None):
        f = fixture or self.f
        self.assertEqual(f.records.read_bytes(), f.old)
        self.assertFalse(f.external.exists())
        self.assertFalse(f.internal.exists())
        for relative in f.files:
            self.assertFalse((f.root / relative).exists())
        self.assertFalse(f.state["committed"])

    def test_exact_full_registry_local_copies_and_same_volume_links(self):
        f = self.f
        old_inode = f.records.stat().st_ino
        result = self.install()
        self.assertTrue(f.state["committed"])
        self.assertEqual(f.records.read_bytes(), f.merged)
        self.assertEqual((f.internal / "local-records-before.json").read_bytes(), f.old)
        self.assertEqual((f.internal / "local-records-before.json").stat().st_ino, old_inode)
        self.assertNotEqual(f.records.stat().st_ino, old_inode)
        self.assertEqual({p.name for p in f.internal.iterdir()},
                         {"external-archive.json", "import-receipt.json", "local-records-before.json"})
        binding = json.loads((f.internal / "external-archive.json").read_bytes())
        self.assertEqual(set(binding), {"schema", "source", "adapter", "validation", "archive_root",
                                       "archive_relative", "archive_files", "local_copies", "registry"})
        self.assertEqual(binding["schema"], "p210-external-archive-binding-v1")
        self.assertEqual(binding["registry"], {"before_sha256": digest(f.old), "after_sha256": digest(f.merged),
                                              "before_count": 414, "added_count": 598, "after_count": 1012})
        self.assertEqual(binding["validation"], {"calls": 1, "original_install_invoked": False,
                                                "version_probe": 1, "proof_compilation": 0, "stock_replay": 0})
        self.assertEqual(binding["adapter"], f.adapter)
        for name, raw in f.archive_payloads.items():
            self.assertEqual((f.external / name).read_bytes(), raw)
            self.assertEqual(binding["archive_files"][name], {"sha256": digest(raw), "bytes": len(raw)})
            self.assertEqual((f.external / name).stat().st_ino, (f.verified["archive"] / name).stat().st_ino)
        for name, raw in f.files.items():
            self.assertEqual((f.root / name).read_bytes(), raw)
            self.assertEqual((f.root / name).stat().st_ino, (f.verified["stage"] / name).stat().st_ino)
        self.assertEqual(result["binding_sha256"], digest((f.internal / "external-archive.json").read_bytes()))
        self.assertEqual(result["status"], "P210_EXTERNAL_ARCHIVE_INSTALLED_EXACT")

    def test_preexisting_external_archive_is_never_changed(self):
        self.f.external.mkdir()
        sentinel = self.f.external / "keep"
        sentinel.write_bytes(b"not owned by this transaction")
        with self.assertRaises((ValueError, RuntimeError, AssertionError, FileExistsError)):
            self.install()
        self.assertEqual(sentinel.read_bytes(), b"not owned by this transaction")
        self.assertEqual(self.f.records.read_bytes(), self.f.old)
        self.assertFalse(self.f.internal.exists())

    def test_preexisting_target_and_internal_anchor_are_never_overwritten(self):
        for kind in ("target", "anchor"):
            f = self.fixture()
            path = f.root / next(iter(f.files)) if kind == "target" else f.internal / "keep"
            put(path, b"existing bytes")
            with self.subTest(kind=kind), self.assertRaises((ValueError, RuntimeError, AssertionError, FileExistsError)):
                self.install(f)
            self.assertEqual(path.read_bytes(), b"existing bytes")
            self.assertEqual(f.records.read_bytes(), f.old)
            self.assertFalse(f.external.exists())

    def test_rejects_external_symlink_parent_and_internal_symlink_ancestor(self):
        for kind in ("external", "internal"):
            f = self.fixture()
            if kind == "external":
                alias = f.parent.with_name("external-alias")
                alias.symlink_to(f.parent, target_is_directory=True)
                f.parent = alias
            else:
                alias = f.root / I.PRIVATE / "ci-imports"
                alias.symlink_to(f.parent, target_is_directory=True)
            with self.subTest(kind=kind), self.assertRaises((ValueError, RuntimeError, AssertionError)):
                self.install(f)
            self.assertEqual(f.records.read_bytes(), f.old)
            self.assertFalse(f.external.exists())

    def test_rejects_external_destination_inside_proof_or_cleanup_tree(self):
        for kind in ("proof", "temporary", "incoming"):
            f = self.fixture()
            f.parent = {"proof": f.root, "temporary": f.temporary, "incoming": f.incoming}[kind]
            with self.subTest(kind=kind), self.assertRaises((ValueError, RuntimeError, AssertionError)):
                self.install(f)
            self.unchanged(f)

    def test_tampered_staged_object_is_rejected_and_rolled_back(self):
        put(self.f.verified["stage"] / next(iter(self.f.files)), b"tampered object")
        with self.assertRaises((ValueError, RuntimeError, AssertionError)):
            self.install()
        self.unchanged()

    def test_tampered_archive_is_rejected_and_rolled_back(self):
        put(self.f.verified["archive"] / "blocks/08/control/original.json", b"tampered archive")
        with self.assertRaises((ValueError, RuntimeError, AssertionError)):
            self.install()
        self.unchanged()

    def test_failure_after_materialization_rolls_back_before_registry_commit(self):
        self.snapshot.side_effect = RuntimeError("injected dependency snapshot failure")
        with self.assertRaisesRegex(RuntimeError, "snapshot failure"):
            self.install()
        self.unchanged()

    def test_registry_replace_failure_keeps_original_bytes_and_rolls_back(self):
        with mock.patch.object(self.module.os, "replace", side_effect=OSError("injected precommit failure")):
            with self.assertRaisesRegex(OSError, "precommit failure"):
                self.install()
        self.unchanged()
        self.assertFalse(list(self.f.records.parent.glob(".records-ci-import-*")))

    def test_external_change_before_commit_is_detected(self):
        def snapshot(*args):
            (self.f.external / "blocks/08/control/original.json").write_bytes(b"concurrent change")
            return {"fixture": "unchanged"}
        self.snapshot.side_effect = snapshot
        with self.assertRaises((ValueError, RuntimeError, AssertionError)):
            self.install()
        self.unchanged()

    def test_insufficient_actual_capacity_creates_no_destinations(self):
        with mock.patch.object(self.module, "available_bytes", return_value=0):
            with self.assertRaises((ValueError, RuntimeError, AssertionError)):
                self.install()
        self.unchanged()

    def test_real_cross_filesystem_copy_preserves_original_bytes(self):
        other = None
        for candidate in (Path("/dev/shm"), Path("/tmp")):
            if candidate.is_dir() and candidate.stat().st_dev != self.f.root.stat().st_dev:
                other = tempfile.TemporaryDirectory(dir=candidate)
                self.addCleanup(other.cleanup)
                break
        if other is None:
            self.skipTest("No writable second filesystem is available")
        f = self.fixture(Path(other.name))
        self.install(f)
        self.assertEqual(f.records.read_bytes(), f.merged)
        for name, raw in f.files.items():
            self.assertEqual((f.root / name).read_bytes(), raw)
            self.assertNotEqual((f.root / name).stat().st_dev, (f.verified["stage"] / name).stat().st_dev)
        self.assertEqual((f.internal / "import-receipt.json").read_bytes(), f.archive_payloads["import-receipt.json"])

    def receive(self, emit):
        f = self.f
        args = SimpleNamespace(run_id="45611402948", commit=COMMIT, index_sha256=INDEX)
        def validated(root, incoming, temporary, args):
            f.populate(temporary)
            return f.verified
        with mock.patch.object(I, "validate", side_effect=validated) as validate, \
             mock.patch.object(I, "install", side_effect=AssertionError("Original installer must not run")) as install:
            try:
                return self.module.receive(I, f.root, f.incoming, f.parent, f.parent.parent,
                                           args, f.adapter, f.state, emit)
            finally:
                self.assertEqual(validate.call_count, 1)
                install.assert_not_called()

    def test_original_validation_runs_once_and_original_install_is_not_claimed(self):
        observed = []
        result = self.receive(observed.append)
        self.assertEqual(len(observed), 1)
        self.assertEqual(json.loads(observed[0]), result)
        self.assertTrue(self.f.state["committed"])
        self.assertEqual(self.f.records.read_bytes(), self.f.merged)

    def test_output_failure_after_commit_preserves_every_installed_file(self):
        def fail(_):
            raise OSError("injected postcommit output failure")
        with self.assertRaisesRegex(OSError, "postcommit output failure"):
            self.receive(fail)
        self.assertTrue(self.f.state["committed"])
        self.assertEqual(self.f.records.read_bytes(), self.f.merged)
        self.assertEqual((self.f.internal / "local-records-before.json").read_bytes(), self.f.old)
        for name, raw in self.f.archive_payloads.items():
            self.assertEqual((self.f.external / name).read_bytes(), raw)
        for name, raw in self.f.files.items():
            self.assertEqual((self.f.root / name).read_bytes(), raw)

    def test_main_failure_preserves_specific_reason_and_committed_state(self):
        f = self.f
        argv = [SCRIPT.name, str(f.incoming), "--run-id", "45611402948", "--commit", COMMIT,
                "--index-sha256", INDEX, "--archive-parent", str(f.parent),
                "--adapter-commit", f.adapter["commit"], "--adapter-sha256", f.adapter["sha256"]]
        for committed in (False, True):
            def failed_receive(*args):
                args[-2].update(committed=committed, phase="report" if committed else "validation")
                raise ValueError("specific original validation/storage rejection")
            errors = io.StringIO()
            with self.subTest(committed=committed), \
                 mock.patch.object(self.module.sys, "argv", argv), \
                 mock.patch.object(self.module.sys, "stderr", errors), \
                 mock.patch.object(self.module, "load_original", return_value=(I, f.adapter)), \
                 mock.patch.object(self.module, "receive", side_effect=failed_receive):
                self.assertEqual(self.module.main(), 1)
                failure = json.loads(errors.getvalue())
                self.assertEqual(failure["error"], "specific original validation/storage rejection")
                self.assertIs(failure["committed"], committed)

    def test_runtime_filename_is_fixed_before_original_modules_are_loaded(self):
        f = self.f
        alias = Path(f.adapter["path"]).with_name("renamed-adapter.py")
        alias.write_bytes(Path(f.adapter["path"]).read_bytes())
        args = SimpleNamespace(commit=COMMIT, run_id="45611402948", index_sha256=INDEX,
                               adapter_commit=f.adapter["commit"], adapter_sha256=f.adapter["sha256"])
        with mock.patch.object(self.module, "__file__", str(alias)):
            with self.assertRaisesRegex(ValueError, "Adapter location"):
                self.module.load_original(f.root, args)


if __name__ == "__main__":
    unittest.main()
