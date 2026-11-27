"""Regression checks for the actual consulted object and fresh run identity."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

DRIVER = Path(__file__).with_name("verify_owned.py")


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class VerificationGuards(unittest.TestCase):
    def test_changed_overlay_rejected_before_importing_audit_helpers(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            base = root / "base"
            source = base / "ImbalancedChen/Dependency.lean"
            source.parent.mkdir(parents=True)
            source.write_text("def dependency : Nat := 1\n")
            original = base / "Dependency.olean"
            original.write_bytes(b"accepted original object")
            live = root / "objects/ImbalancedChen/Dependency.olean"
            live.parent.mkdir(parents=True)
            live.write_bytes(b"substituted live object")
            lean = root / "lean"
            lean.write_bytes(b"compiler identity only; must never execute")
            checker = root / "leanchecker"
            checker.write_bytes(b"checker identity only; must never execute")
            audit = root / "P36RoundedCorrectionAudit.lean"
            audit.write_text("-- identity fixture\n")
            module = "ImbalancedChen.Dependency"
            warm = {"sources": {module: {"path": "ImbalancedChen/Dependency.lean",
                                         "sha256": digest(source)}},
                    "warm": {"accepted_report_sha256": "fixture",
                             "modules": {module: {"objects": {str(original): digest(original)}}}}}
            pins = {"modules": {}, "validation_source_sha256": {},
                    "audit_sha256": digest(audit), "checker_sha256": digest(checker)}
            pref = {"source_base": str(base), "lean_path": str(root / "objects"),
                    "compiler": {"path": str(lean), "sha256": digest(lean)}}
            for name, value in [("warm-pins.json", warm), ("OWNED_SOURCE_PINS.json", pins),
                                ("PREFLIGHT.json", pref)]:
                (root / name).write_text(json.dumps(value))
            proc = subprocess.run([sys.executable, str(DRIVER), "--root", str(root)],
                                  cwd=root, capture_output=True, text=True, timeout=10)
            self.assertNotEqual(proc.returncode, 0)
            report = json.loads((root / "acceptance/report.json").read_text())
            self.assertEqual(report["status"], "FAILED")
            self.assertIn("Changed live dependency object", report["error"])

    def test_failed_startup_cannot_leave_previous_success(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            out = root / "acceptance"
            out.mkdir()
            (out / "report.json").write_text('{"status":"VERIFIED_OWNED"}')
            proc = subprocess.run([sys.executable, str(DRIVER), "--root", str(root)],
                                  cwd=root, capture_output=True, text=True, timeout=10)
            self.assertNotEqual(proc.returncode, 0)
            report = json.loads((out / "report.json").read_text())
            self.assertNotEqual(report["status"], "VERIFIED_OWNED")
            self.assertTrue(report["verification_id"])


if __name__ == "__main__":
    unittest.main()
