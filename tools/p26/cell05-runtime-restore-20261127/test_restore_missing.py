"""Local filesystem regressions for the missing-byte restore. Operates only in test fixtures."""
from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('restore_missing', HERE / 'restore_missing.py')
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)


def inventory(root):
    """Include dirs, bytes and dangling entries, without following links."""
    result = {}
    for path in root.rglob('*'):
        key = path.relative_to(root)
        st = path.lstat()
        if stat.S_ISLNK(st.st_mode):
            value = path.readlink()
        elif stat.S_ISREG(st.st_mode):
            value = path.read_bytes()
        else:
            value = None
        result[key] = (st.st_mode, st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns, value)
    return result


class RestoreIO(unittest.TestCase):
    def setUp(self):
        scratch = TemporaryDirectory(dir=HERE)
        self.addCleanup(scratch.cleanup)
        self.base = Path(scratch.name)
        self.stage = self.base / 'stage'
        self.root = self.base / 'runtime'
        self.stage.mkdir()
        self.root.mkdir()
        self.capsule = self.stage / 'capsule'
        self.capsule.write_bytes(b'fixture capsule')
        self.guard = self.base / 'guard'
        self.guard.write_bytes(b'original fixture guard')
        self.snapshot = self.base / 'snapshot'
        self.existing = self.root / 'Keep.olean'
        self.existing.write_bytes(b'keep')
        self.launch = self.stage / 'RESTORE_LAUNCH.json'
        self.result = self.stage / 'RESTORED.json'

    def invoke(self, action='restore', names=('A.olean', 'Z.olean')):
        files = {'files/' + n: ('fixture ' + n).encode() for n in names}
        selected = {n: dict(relative_path=n, **R.pin(files['files/' + n])) for n in names}
        snapshot = R.encoded({'roots': [{'logical_root': 'mathlib-objects',
                              'files': [{'relative_path': 'Keep.olean'}, *selected.values()]}]})
        if not self.snapshot.exists():
            self.snapshot.write_bytes(snapshot)
        settings = dict(ROOT=self.root, STAGE=self.stage, CAPSULE=self.capsule, CAPSULE_PIN=R.pin(self.capsule.read_bytes()),
                        SNAPSHOT=self.snapshot, SNAPSHOT_PIN=R.pin(snapshot), OLD_GUARD=self.guard,
                        OLD_GUARD_PIN=R.pin(b'original fixture guard'))
        output = io.StringIO()
        with (patch.multiple(R, **settings), patch.object(R, 'unpack', return_value=files),
              patch.object(R, 'validate_payload', return_value=selected), patch.object(sys, 'argv', ['restore_missing.py', action]),
              redirect_stdout(output)):
            R.main()
        return json.loads(output.getvalue())

    def fail_without_writes(self, names=('A.olean', 'Z.olean'), action='restore'):
        # Complete setup of the fixture snapshot before comparing filesystem inventories.
        rows = [{'relative_path': 'Keep.olean'}] + [dict(relative_path=n, **R.pin(('fixture ' + n).encode())) for n in names]
        if not self.snapshot.exists():
            self.snapshot.write_bytes(R.encoded({'roots': [{'logical_root': 'mathlib-objects', 'files': rows}]}))
        before = inventory(self.base)
        with self.assertRaises((ValueError, OSError)):
            self.invoke(action, names)
        self.assertEqual(before, inventory(self.base))

    def test_late_selected_directory_blocks_earlier_regular_file(self):
        (self.root / 'Z.olean').mkdir()
        self.fail_without_writes()

    def test_dangling_result_and_dangling_launch(self):
        for path in (self.result, self.launch):
            with self.subTest(path=path.name):
                path.symlink_to('absent')
                self.fail_without_writes()
                path.unlink()

    def test_non_directory_parent_and_unexpected_extra(self):
        blocker = self.root / 'Z'
        blocker.write_bytes(b'parent collision')
        self.fail_without_writes(('A.olean', 'Z/file.olean'))
        blocker.unlink()
        (self.root / 'Extra.olean').write_bytes(b'extra')
        self.fail_without_writes(('A.olean', 'Z/file.olean'))

    @unittest.skipIf(os.geteuid() == 0, 'Permission fixture requires ordinary user')
    def test_unreadable_subtree_aborts_before_launch(self):
        path = self.root / 'blocked'
        path.mkdir()
        path.chmod(0)
        try:
            self.fail_without_writes()
        finally:
            path.chmod(0o700)

    def test_existing_target_and_prior_launch_are_preserved(self):
        for path in (self.root / 'Z.olean', self.launch):
            with self.subTest(path=path.name):
                path.write_bytes(b'existing')
                self.fail_without_writes()
                path.unlink()

    def test_restore_and_verify_with_absent_and_existing_parents(self):
        (self.root / 'existing').mkdir()
        names = ('existing/A.olean', 'missing/sub/Z.olean')
        self.assertEqual(self.invoke(names=names)['status'], 'RESTORED')
        for n in names:
            self.assertEqual((self.root / n).read_bytes(), ('fixture ' + n).encode())
        before = inventory(self.base)
        self.assertEqual(self.invoke('verify', names)['status'], 'RESTORE_REVERIFIED')
        self.assertEqual(before, inventory(self.base))
        (self.root / names[1]).write_bytes(b'corruption')
        self.fail_without_writes(names, 'verify')
        self.assertEqual(self.guard.read_bytes(), b'original fixture guard')
        self.assertEqual(self.existing.read_bytes(), b'keep')

    def test_leaf_is_exclusive_even_when_added_after_preflight(self):
        with R.bound_root(self.root) as root:
            R.destination_inventory(root)
            root.require_absent('X.olean')
            (self.root / 'X.olean').write_bytes(b'concurrent existing data')
            with self.assertRaises(FileExistsError):
                root.write_new('X.olean', b'fixture new contents')
            self.assertEqual((self.root / 'X.olean').read_bytes(), b'concurrent existing data')

    def test_replaced_root_blocks_descriptor_create(self):
        with R.bound_root(self.root) as root:
            R.destination_inventory(root)
            root.require_absent('A.olean')
            previous = self.base / 'previous-root'
            self.root.rename(previous)
            self.root.mkdir()
            before = inventory(self.base)
            with self.assertRaisesRegex(ValueError, 'Root identity changed'):
                root.write_new('A.olean', b'fixture')
            self.assertEqual(before, inventory(self.base))

    def test_replaced_parent_after_launch_preserves_unrelated_directory(self):
        parent = self.root / 'selected'
        parent.mkdir()
        original_write = R.DirectoryRoot.write_new

        def swap_after_launch(bound, relative, body):
            original_write(bound, relative, body)
            if relative == self.launch.name:
                parent.rename(self.root / 'old-selected')
                parent.mkdir()
                (parent / 'unrelated').write_bytes(b'keep')

        with patch.object(R.DirectoryRoot, 'write_new', swap_after_launch), self.assertRaisesRegex(ValueError, 'Directory identity changed'):
            self.invoke(names=('selected/A.olean',))
        self.assertTrue(self.launch.is_file())
        self.assertFalse(self.result.exists())
        self.assertFalse((self.root / 'old-selected/A.olean').exists())
        self.assertEqual([p.name for p in parent.iterdir()], ['unrelated'])


if __name__ == '__main__':
    unittest.main()
