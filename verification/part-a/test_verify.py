"""Regressions for the two concrete aggregate-config review findings."""
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class AggregateConfigChecks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.project = Path(self.temporary.name) / "project"
        shutil.copytree(ROOT, self.project,
                        ignore=shutil.ignore_patterns(".git", ".lake", ".superpowers", "__pycache__"))

    def assert_rejected(self):
        result = subprocess.run([sys.executable, "verification/part-a/verify.py"],
                                cwd=self.project, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0, "modified aggregate configuration was accepted")
        self.assertIn("configuration hash mismatch", result.stderr)

    def test_rejects_extra_aggregate_declaration(self):
        path = self.project / "ImbalancedChen.lean"
        path.write_text(path.read_text() + "\ndef partAUnexpected := 1\n")
        self.assert_rejected()

    def test_rejects_disabled_default_build(self):
        path = self.project / "lakefile.toml"
        text = path.read_text()
        self.assertIn('defaultTargets = ["ImbalancedChen"]', text)
        path.write_text(text.replace('defaultTargets = ["ImbalancedChen"]', 'defaultTargets = []'))
        self.assert_rejected()


if __name__ == "__main__":
    unittest.main()
