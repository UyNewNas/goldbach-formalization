"""Geometry-specific source transition tests; no compiler or original suite."""
from pathlib import Path
import tempfile
import unittest
import run_geometry as geometry
import install_geometry_source as installer

ORIGINAL = Path('/tmp/p15-r5-root/P1OriginalSingletonRemainingTypeIGeometry.AK.failed.lean').read_bytes()
REPAIRED = Path('/tmp/p15-r5-root/P1OriginalSingletonRemainingTypeIGeometry.lean').read_bytes()


class GeometryInstallBoundaries(unittest.TestCase):
    def test_absent_source_is_created_from_exact_repaired_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'Geometry.lean'
            action = installer.install_exact(geometry, source, REPAIRED, None)
            self.assertEqual(action, 'EXCLUSIVE_NEW_CANONICAL_SOURCE')
            self.assertEqual(source.read_bytes(), REPAIRED)

    def test_original_source_transition_requires_preserved_exact_backup(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'Geometry.lean'
            source.write_bytes(ORIGINAL)
            with self.assertRaises(RuntimeError):
                installer.install_exact(geometry, source, REPAIRED, None)
            self.assertEqual(source.read_bytes(), ORIGINAL)
            backup = Path(temporary) / 'canonical-source-before.lean'
            backup.write_bytes(ORIGINAL)
            self.assertEqual(installer.install_exact(geometry, source, REPAIRED, backup),
                             'EXACT_AJ_SOURCE_REPLACED_BY_R_RESOLUTION_REPAIR')
            self.assertEqual(source.read_bytes(), REPAIRED)
            self.assertEqual(backup.read_bytes(), ORIGINAL)

    def test_identical_source_is_not_rewritten_and_other_bytes_are_not_replaced(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'Geometry.lean'
            source.write_bytes(REPAIRED)
            before = source.stat()
            self.assertEqual(installer.install_exact(geometry, source, REPAIRED, None),
                             'IDENTICAL_SOURCE_BEFORE_OWNER_START')
            self.assertEqual((source.stat().st_ino, source.stat().st_mtime_ns),
                             (before.st_ino, before.st_mtime_ns))
            source.write_bytes(b'unreviewed source\n')
            with self.assertRaises(RuntimeError):
                installer.install_exact(geometry, source, REPAIRED, None)
            self.assertEqual(source.read_bytes(), b'unreviewed source\n')

    def test_wrong_payload_or_symlink_cannot_install(self):
        with tempfile.TemporaryDirectory() as temporary:
            source = Path(temporary) / 'Geometry.lean'
            with self.assertRaises(RuntimeError):
                installer.install_exact(geometry, source, ORIGINAL, None)
            self.assertFalse(source.exists())
            other = Path(temporary) / 'elsewhere.lean'
            other.write_bytes(ORIGINAL)
            source.symlink_to(other)
            with self.assertRaises(RuntimeError):
                installer.install_exact(geometry, source, REPAIRED, None)
            self.assertEqual(other.read_bytes(), ORIGINAL)


if __name__ == '__main__':
    unittest.main(verbosity=2)
