"""Local byte-safety tests. These run no Lean, cloud job, or Git mutation."""
from pathlib import Path
import tempfile
import unittest

import prepare_halfopen as p


class PreparationSafety(unittest.TestCase):
    def test_real_input_partition_and_all_historical_signatures(self):
        plan = p.build_manifest()
        self.assertEqual(len(plan["modules"]), 275)
        self.assertEqual(plan["supplier_counts"],
                         {"r14_ltar": 214, "standalone_xz": 5, "ci_exact54": 54, "fresh_chronology": 1})
        self.assertEqual(plan["historical_schema_counts"], {2: 92, 3: 182})
        self.assertFalse(plan["old_records_reconstructed"])
        self.assertFalse(plan["R19_accepted"])

    def test_atomic_publish_does_not_overwrite(self):
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "objects" / "A.olean"
            p.publish_new(path, b"old exact bytes")
            with self.assertRaises(FileExistsError):
                p.publish_new(path, b"new different bytes")
            self.assertEqual(path.read_bytes(), b"old exact bytes")

    def test_existing_exact_rejects_content_drift(self):
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "A.olean"
            path.write_bytes(b"altered")
            with self.assertRaises(ValueError):
                p.existing_exact(path, p.sha(b"wanted!"), 7)

    def test_existing_exact_rejects_leaf_symlink(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "real").write_bytes(b"wanted")
            (root / "link").symlink_to(root / "real")
            with self.assertRaises(OSError):
                p.existing_exact(root / "link", p.sha(b"wanted"), 6)

    def test_publish_rejects_ancestor_symlink(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "real").mkdir()
            (root / "link").symlink_to(root / "real", target_is_directory=True)
            with self.assertRaises(OSError):
                p.publish_new(root / "link" / "A.olean", b"wanted")
            self.assertFalse((root / "real" / "A.olean").exists())

    def test_full_read_checks_size_and_sha(self):
        with tempfile.TemporaryDirectory() as raw:
            path = Path(raw) / "A.olean"
            path.write_bytes(b"wanted")
            self.assertEqual(p.read_regular(path, p.sha(b"wanted"), 6), b"wanted")
            with self.assertRaises(ValueError):
                p.read_regular(path, p.sha(b"wanted"), 5)
            with self.assertRaises(ValueError):
                p.read_regular(path, p.sha(b"other!"), 6)


if __name__ == "__main__":
    unittest.main()
