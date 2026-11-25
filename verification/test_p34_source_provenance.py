"""Check source-only provenance without invoking Lean."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
VERIFIER = ROOT / "verification/verify_p34_cusp_normalization.py"


class SourceOnlyProvenance(unittest.TestCase):
    def setUp(self):
        self.head = self.git_output("rev-parse", "HEAD").strip()
        self.working_tree = self.git_output(
            "status", "--porcelain", "--untracked-files=all").removesuffix("\n")

    def git_output(self, *arguments):
        return subprocess.check_output(["git", *arguments], cwd=ROOT, text=True)

    def source_only(self, expected_head):
        with tempfile.TemporaryDirectory(prefix="p34-source-test-") as directory:
            result = subprocess.run(
                [sys.executable, str(VERIFIER), "--source-only", "--expected-head",
                 expected_head, "--output-dir", directory],
                cwd=ROOT, capture_output=True, text=True)
            report = json.loads((Path(directory) / "report.json").read_text())
        return result, report

    def test_wrong_head_is_rejected_and_actual_checkout_is_reported(self):
        wrong_head = self.git_output("rev-parse", "HEAD^").strip()
        result, report = self.source_only(wrong_head)
        self.assertNotEqual(result.returncode, 0, result.stdout)
        self.assertEqual(report["status"], "FAILED")
        self.assertEqual(report["expected_head"], wrong_head)
        self.assertEqual(report["head_commit"], self.head)
        self.assertEqual(report["working_tree"], self.working_tree)
        self.assertIn("differs from expected head", report["error"])

    def test_matching_head_returns_a_source_only_report_with_checkout_state(self):
        result, report = self.source_only(self.head)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(report["status"], "SOURCE_ONLY_NOT_COMPILED")
        self.assertEqual(report["head_commit"], self.head)
        self.assertEqual(report["working_tree"], self.working_tree)
        self.assertTrue(report["source_sha256"])
        self.assertEqual(
            {stage["name"]: stage["exit_code"] for stage in report["stages"]},
            {"head": 0, "working-tree": 0, "baseline-ancestor": 0})


if __name__ == "__main__":
    unittest.main()
