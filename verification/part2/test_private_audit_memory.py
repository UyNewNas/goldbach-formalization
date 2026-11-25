"""Resource-selection receipt tests; fixture processes confer no Lean proof credit."""
from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path
import subprocess
import unittest

import test_private_audit as audit_tests
import test_private_evidence_export as export_tests


class PrivateAuditMemoryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = audit_tests.PrivateAuditTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)

    def test_default_limit_is_recorded_without_changing_the_command(self) -> None:
        receipt = self.fixture.run_audit()
        self.assertEqual(receipt["audit"].get("memory_mb"), 6144)
        self.assertEqual(receipt["audit"]["command"][1:-1], [
            "-t0", "-j1", "-M6144", "-DwarningAsError=true",
            "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"])

    def test_explicit_larger_limit_is_used_and_recorded(self) -> None:
        result = subprocess.run(
            self.fixture.launcher() + [audit_tests.MODULE, "--memory-mb", "11264"],
            cwd=self.fixture.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads((self.fixture.root / ".lake/p2-private/audit" /
                              audit_tests.MODULE / "latest.json").read_text())
        self.assertTrue(receipt["accepted"])
        self.assertEqual(receipt["audit"].get("memory_mb"), 11264)
        self.assertEqual(receipt["audit"]["command"][1:-1], [
            "-t0", "-j1", "-M11264", "-DwarningAsError=true",
            "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"])

    def test_unsupported_cli_limits_are_rejected_before_running_audit(self) -> None:
        for value in ("0", "4096", "8192", "11265", "11264.0", "true"):
            with self.subTest(value=value):
                result = subprocess.run(
                    self.fixture.launcher() + [audit_tests.MODULE, "--memory-mb", value],
                    cwd=self.fixture.root, capture_output=True, text=True)
                self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
                self.assertFalse((self.fixture.root / ".lake/p2-private/audit").exists())

    def test_resource_change_retains_an_already_valid_audit(self) -> None:
        first = self.fixture.run_audit()
        (self.fixture.root / "fail-replay").touch()
        result = subprocess.run(
            self.fixture.launcher() + [audit_tests.MODULE, "--memory-mb", "11264"],
            cwd=self.fixture.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        directory = self.fixture.root / ".lake/p2-private/audit" / audit_tests.MODULE
        second = json.loads((directory / "latest.json").read_text())
        self.assertEqual(second, first)
        self.assertEqual(second["audit"].get("memory_mb"), 6144)
        self.assertEqual(len(list(directory.glob("attempt-*"))), 1)


class PrivateAuditMemoryExportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = export_tests.PrivateEvidenceExportTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.exporter = self.fixture.exporter()
        self.directory = self.fixture.root / ".lake/p2-private/audit" / audit_tests.MODULE
        self.original = json.loads((self.directory / "latest.json").read_text())
        self.output_base = self.fixture.out

    def install_receipt(self, receipt: dict, label: str) -> None:
        receipt["input_sha256"] = self.exporter.json_digest(receipt["input_snapshot"])
        for path in [self.directory / "latest.json", *self.directory.glob("attempt-*/receipt.json")]:
            path.write_text(json.dumps(receipt))
        self.fixture.out = self.output_base.with_name(self.output_base.name + "-" + label)

    def require_v4(self) -> str:
        sha = hashlib.sha256(audit_tests.DRIVER.read_bytes()).hexdigest()
        self.assertEqual(getattr(self.exporter, "DRIVER_V4", None), sha)
        return sha

    def test_current_driver_is_registered_and_v3_bytes_are_preserved(self) -> None:
        sha = self.require_v4()
        self.assertEqual(self.exporter.DRIVER_FILES[sha], "driver-v4.py")
        old = (audit_tests.DRIVER.parents[2] /
               "docs/verification/20261125-p2-resume/audit-driver-v3.py")
        self.assertEqual(hashlib.sha256(old.read_bytes()).hexdigest(), self.exporter.DRIVER_V3)

    def test_v4_larger_limit_receipt_exports_through_all_existing_gates(self) -> None:
        sha = self.require_v4()
        # Preserve attempt 001; removing the fixture's latest pointer permits a fresh run.
        (self.directory / "latest.json").unlink()
        runner = self.fixture.fixture
        result = subprocess.run(runner.launcher() + [audit_tests.MODULE, "--memory-mb", "11264"],
                                cwd=self.fixture.root, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        receipt = json.loads((self.directory / "latest.json").read_text())
        self.assertEqual(receipt["audit"]["memory_mb"], 11264)
        self.assertEqual(receipt["audit"]["command"][3], "-M11264")
        exported = self.fixture.run_export()
        self.assertEqual(exported["accepted_module_count"], 1)
        self.assertEqual(exported["accepted_modules"][audit_tests.MODULE]["driver_sha256"], sha)

    def test_all_historical_drivers_still_accept_the_original_6144_command(self) -> None:
        for version in ("DRIVER_V1", "DRIVER_V2", "DRIVER_V3"):
            with self.subTest(version=version):
                receipt = copy.deepcopy(self.original)
                receipt["input_snapshot"]["driver_sha256"] = getattr(self.exporter, version)
                receipt["audit"].pop("memory_mb", None)
                self.install_receipt(receipt, version)
                exported = self.fixture.run_export()
                self.assertEqual(exported["accepted_module_count"], 1)
                self.assertEqual(exported["accepted_modules"][audit_tests.MODULE]["driver_sha256"],
                                 getattr(self.exporter, version))

    def test_historical_drivers_cannot_authorize_larger_or_mismatched_limits(self) -> None:
        for version in ("DRIVER_V1", "DRIVER_V2", "DRIVER_V3"):
            for command_limit in ("-M6144", "-M11264"):
                with self.subTest(version=version, command_limit=command_limit):
                    receipt = copy.deepcopy(self.original)
                    receipt["input_snapshot"]["driver_sha256"] = getattr(self.exporter, version)
                    receipt["audit"]["memory_mb"] = 11264
                    receipt["audit"]["command"][3] = command_limit
                    self.install_receipt(receipt, version + command_limit)
                    self.assertEqual(self.fixture.run_export()["accepted_module_count"], 0)

    def test_v4_requires_an_explicit_integer_from_the_allowlist(self) -> None:
        self.require_v4()
        for index, value in enumerate((None, "11264", 11264.0, True, [11264], 0, 4096, 8192, 16384)):
            with self.subTest(value=value):
                receipt = copy.deepcopy(self.original)
                if value is None:
                    receipt["audit"].pop("memory_mb", None)
                else:
                    receipt["audit"]["memory_mb"] = value
                self.install_receipt(receipt, f"invalid-{index}")
                self.assertEqual(self.fixture.run_export()["accepted_module_count"], 0)

    def test_v4_record_and_command_must_match_and_no_other_flags_can_change(self) -> None:
        self.require_v4()
        changes = [
            (11264, lambda command: command),
            (6144, lambda command: command[:3] + ["-M11264"] + command[4:]),
            (6144, lambda command: command[:4] + ["-M11264"] + command[4:]),
            (6144, lambda command: ["-DwarningAsError=false" if flag == "-DwarningAsError=true"
                                   else flag for flag in command]),
            (6144, lambda command: ["-j2" if flag == "-j1" else flag for flag in command]),
            (6144, lambda command: ["-t1" if flag == "-t0" else flag for flag in command]),
        ]
        for index, (memory, alter) in enumerate(changes):
            with self.subTest(index=index):
                receipt = copy.deepcopy(self.original)
                receipt["audit"]["memory_mb"] = memory
                receipt["audit"]["command"] = alter(receipt["audit"]["command"])
                self.install_receipt(receipt, f"command-{index}")
                self.assertEqual(self.fixture.run_export()["accepted_module_count"], 0)

    def test_unrecognized_driver_cannot_select_a_memory_limit(self) -> None:
        receipt = copy.deepcopy(self.original)
        receipt["input_snapshot"]["driver_sha256"] = "0" * 64
        receipt["audit"]["memory_mb"] = 11264
        receipt["audit"]["command"][3] = "-M11264"
        self.install_receipt(receipt, "unknown-driver")
        self.assertEqual(self.fixture.run_export()["accepted_module_count"], 0)


if __name__ == "__main__":
    unittest.main()
