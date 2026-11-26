#!/usr/bin/env python3
"""Focused new checks for namespace resolution and immutable provider reuse."""
from pathlib import Path
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
import external_runtime as X
import join_common as C

HERE = Path(__file__).absolute().parent
F = C.load_executor(HERE.parent / 'cell01-family-run-20261126/releases/p3-v2/family_run.py')


class ExternalRuntimeTests(unittest.TestCase):
    def fixture(self, root):
        source = root / 'original' / 'MathlibNt' / 'Existing.olean'
        source.parent.mkdir(parents=True)
        source.write_bytes(b'already accepted external object fixture')
        incoming = b'exact transferred old external object fixture'
        planned = [
            {'module': 'MathlibNt.Existing', 'member': 'MathlibNt/Existing.olean',
             'accepted': F.fp(source), 'source': F.fp(source), 'method': 'hardlink_existing_P3'},
            {'module': 'MathlibNt.Transferred', 'member': 'MathlibNt/Transferred.olean',
             'accepted': {'path': '/original/MathlibNt/Transferred.olean', **C.identity_bytes(incoming)},
             'method': 'exact_P1_capsule_body', 'capsule_member': 'objects/MathlibNt/Transferred.olean'},
        ]
        marker = {'schema': 'synthetic_immutable_external_provider', 'members': planned}
        return root / 'combined', marker, planned, {planned[1]['capsule_member']: incoming}, source

    def test_partial_namespace_roots_fail_but_complete_root_resolves_same_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            combined, marker, planned, blobs, source = self.fixture(root)
            partial = root / 'partial'
            (partial / 'MathlibNt').mkdir(parents=True)
            (partial / 'MathlibNt/Transferred.olean').write_bytes(next(iter(blobs.values())))
            names = [row['module'] for row in planned]
            with self.assertRaisesRegex(RuntimeError, 'Missing module in first namespace provider'):
                F.V.module_byte_context(names, [partial, source.parent.parent])
            X.materialize(F, combined, marker, planned, blobs, F.E.Frozen())
            actual = F.V.module_byte_context(names, [combined])
            expected = {row['module']: row['accepted'] for row in planned}
            self.assertEqual(len(actual), 2)
            self.assertTrue(all(F.same(row['object'], expected[row['module']]) for row in actual))

    def test_partial_destination_stops_without_installing_any_member(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            destination, marker, planned, blobs, _ = self.fixture(root)
            destination.mkdir()
            existing = destination / 'unreviewed-partial'
            existing.write_bytes(b'preserve interrupted data')
            before = existing.stat()
            with self.assertRaisesRegex(RuntimeError, 'PARTIAL_EXTERNAL_PROVIDER_REQUIRES_INSPECTION'):
                X.materialize(F, destination, marker, planned, blobs, F.E.Frozen())
            self.assertEqual(list(destination.iterdir()), [existing])
            self.assertEqual((existing.stat().st_ino, existing.stat().st_mtime_ns),
                             (before.st_ino, before.st_mtime_ns))

    def test_complete_provider_reuses_original_inodes_and_marker_without_writes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            destination, marker, planned, blobs, source = self.fixture(root)
            X.materialize(F, destination, marker, planned, blobs, F.E.Frozen())
            files = [p for p in destination.rglob('*') if p.is_file()]
            before = {p: (p.stat().st_ino, p.stat().st_mtime_ns, p.read_bytes()) for p in files}
            self.assertEqual((destination / planned[0]['member']).stat().st_ino, source.stat().st_ino)
            X.materialize(F, destination, marker, planned, blobs, F.E.Frozen())
            self.assertEqual(before, {p: (p.stat().st_ino, p.stat().st_mtime_ns, p.read_bytes()) for p in files})

    def test_complete_provider_missing_or_changed_body_never_repopulates(self):
        for operation in ('missing', 'changed'):
            with self.subTest(operation=operation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                destination, marker, planned, blobs, _ = self.fixture(root)
                X.materialize(F, destination, marker, planned, blobs, F.E.Frozen())
                target = destination / planned[1]['member']
                if operation == 'missing':
                    target.unlink()
                else:
                    target.write_bytes(b'conflicting bytes must remain untouched')
                marker_before = (destination / 'PROVIDER.json').read_bytes()
                with self.assertRaises(RuntimeError):
                    X.materialize(F, destination, marker, planned, blobs, F.E.Frozen())
                self.assertEqual((destination / 'PROVIDER.json').read_bytes(), marker_before)
                if operation == 'missing':
                    self.assertFalse(target.exists())
                else:
                    self.assertEqual(target.read_bytes(), b'conflicting bytes must remain untouched')


if __name__ == '__main__':
    unittest.main()
