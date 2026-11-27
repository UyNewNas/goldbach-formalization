#!/usr/bin/env python3
"""Real-filesystem safety checks for the exact-byte restoration helper."""
import hashlib
import importlib.util
import io
import json
from contextlib import ExitStack
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
import zipfile


SCRIPT = Path(__file__).with_name("restore_exact_runtime.py")


def digest(body):
    return hashlib.sha256(body).hexdigest()


class RestoreTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="p25-restore-test-", dir="/workspace/scratch")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.files = {}
        self.rows = {}
        self.donors = {}

    def want(self, name, body, status="missing"):
        path = self.root / "destination" / name
        expected = {"bytes": len(body), "sha256": digest(body), "role": "fixture"}
        self.files[str(path)] = expected
        self.rows[str(path)] = {"expected": expected, "status": status}
        return path

    def donor(self, body):
        path = self.root / ("donor-" + digest(body))
        path.write_bytes(body)
        self.donors[f"{len(body)}:{digest(body)}"] = {
            "bytes": len(body), "sha256": digest(body),
            "candidates": [{"path": str(path), "bytes": len(body), "sha256": digest(body)}],
        }
        return path

    def run_restore(self, *extra):
        snapshot = {"schema": "p2-winner9-qualified-native-environment-v1",
                    "compile_credit": False, "kernel_credit": False, "files": self.files}
        raw = (json.dumps(snapshot) + "\n").encode()
        self.snapshot = self.root / "snapshot.json"
        self.snapshot.write_bytes(raw)
        inventory = {"schema": "p2-runtime-readonly-inventory-v1",
                     "snapshot": {"raw_sha256": digest(raw)},
                     "files": self.rows, "donors": self.donors}
        inv = (json.dumps(inventory) + "\n").encode()
        self.inventory = self.root / "inventory.json"
        self.inventory.write_bytes(inv)
        self.out = self.root / ("report-" + str(len(list(self.root.glob("report-*")))))
        command = [sys.executable, "-B", str(SCRIPT), "--snapshot", str(self.snapshot),
                   "--snapshot-sha256", digest(raw), "--inventory", str(self.inventory),
                   "--inventory-sha256", digest(inv), "--out-dir", str(self.out), *extra]
        return subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def result(self, process):
        self.assertEqual(process.returncode, 0, process.stderr + process.stdout)
        return json.loads((self.out / "RESTORE_RESULT.json").read_text())

    def test_dry_run_does_not_create_destination(self):
        """Catches an accidental write without --apply."""
        target = self.want("new/n.bin", b"exact fixture")
        self.donor(b"exact fixture")
        report = self.result(self.run_restore())
        self.assertFalse(target.parent.exists())
        self.assertEqual(report["files"][str(target)]["status"], "ready")

    def test_restores_exact_donor_and_reports_unavailable_content(self):
        """Catches silently creating bytes for an absent donor or ignoring a valid donor."""
        target = self.want("new/n.bin", b"exact fixture")
        missing = self.want("missing.bin", b"not in the sources")
        self.donor(b"exact fixture")
        report = self.result(self.run_restore("--apply"))
        self.assertEqual(target.read_bytes(), b"exact fixture")
        self.assertFalse(missing.exists())
        self.assertEqual(report["files"][str(target)]["status"], "restored")
        self.assertEqual(report["files"][str(missing)]["status"], "missing")
        self.assertFalse(report["compile_credit"])
        self.assertFalse(report["kernel_credit"])
        self.assertFalse(report["qualification_performed"])

    def test_existing_conflict_and_symlink_parent_are_preserved(self):
        """Catches overwriting existing content or following a destination symlink."""
        conflict = self.want("conflict.bin", b"expected")
        conflict.parent.mkdir(parents=True)
        conflict.write_bytes(b"preexisting wrong bytes")
        self.donor(b"expected")
        escape = self.root / "outside"
        escape.mkdir()
        (conflict.parent / "link").symlink_to(escape, target_is_directory=True)
        linked = self.want("link/new.bin", b"expected")
        report = self.result(self.run_restore("--apply"))
        self.assertEqual(conflict.read_bytes(), b"preexisting wrong bytes")
        self.assertFalse((escape / "new.bin").exists())
        self.assertEqual(report["files"][str(conflict)]["status"], "existing_conflict")
        self.assertEqual(report["files"][str(linked)]["status"], "blocked_path")

    def test_stale_donor_bytes_are_not_installed(self):
        """Catches trusting an inventory SHA without verifying current donor contents."""
        target = self.want("new.bin", b"expected")
        donor = self.donor(b"expected")
        donor.write_bytes(b"tampered")
        report = self.result(self.run_restore("--apply"))
        self.assertFalse(target.exists())
        self.assertEqual(report["files"][str(target)]["status"], "missing")
        self.assertTrue(report["source_errors"])

    def test_stale_inventory_donor_does_not_hide_exact_receipt_fallback(self):
        """Catches skipping named donor directories merely because an old donor was listed."""
        target = self.want("new.bin", b"expected")
        self.donor(b"expected").write_bytes(b"tampered")
        receipts = self.root / "fallback"
        receipts.mkdir()
        (receipts / "original.bin").write_bytes(b"expected")
        self.result(self.run_restore("--apply", "--donor-dir", str(receipts)))
        self.assertTrue(target.is_file())
        self.assertEqual(target.read_bytes(), b"expected")

    def test_named_receipt_directory_supplies_only_matching_bytes(self):
        """Catches copying a same-sized unrelated receipt or losing renamed exact bodies."""
        target = self.want("qualification/QUALIFICATION.json", b"true receipt")
        directory = self.root / "receipts"
        directory.mkdir()
        (directory / "NATIVE_QUALIFICATION.json").write_bytes(b"true receipt")
        (directory / "wrong.json").write_bytes(b"fake receipt")
        report = self.result(self.run_restore("--apply", "--donor-dir", str(directory)))
        self.assertEqual(target.read_bytes(), b"true receipt")
        self.assertEqual(report["files"][str(target)]["status"], "restored")

    def test_inventory_pin_failure_prevents_all_writes(self):
        """Catches processing files before checking the supplied inventory digest."""
        target = self.want("new.bin", b"expected")
        self.donor(b"expected")
        process = self.run_restore("--apply", "--inventory-sha256", "0" * 64)
        self.assertNotEqual(process.returncode, 0)
        self.assertIn("input digest mismatch", process.stderr)
        self.assertFalse(target.exists())
        self.assertFalse(self.out.exists())

    def test_inventory_cannot_add_an_unlisted_destination(self):
        """Catches using inventory paths without checking the pinned snapshot allowlist."""
        target = self.want("new.bin", b"expected")
        self.donor(b"expected")
        del self.files[str(target)]
        process = self.run_restore("--apply")
        self.assertNotEqual(process.returncode, 0)
        self.assertIn("inventory/snapshot paths differ", process.stderr)
        self.assertFalse(target.exists())

    def test_verified_inner_packet_can_be_read_through_github_wrapper(self):
        """Catches reading the outer wrapper as the original packet or ignoring its index."""
        self.assertTrue(SCRIPT.is_file(), "Restoration helper has not been implemented")
        spec = importlib.util.spec_from_file_location("tested_restore", SCRIPT)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        body = b"native interface bytes"
        key = f"objects/{digest(body)}"
        index = {"schema": "p2-original-native-byte-packet-v1", "part": 1,
                 "original_artifact": {"id": 13749339878}, "request_sha256": "f" * 64,
                 "payloads": {key: {"bytes": len(body), "sha256": digest(body)}}}
        memory = io.BytesIO()
        with zipfile.ZipFile(memory, "w", compression=zipfile.ZIP_STORED) as packet:
            packet.writestr("PACKET_INDEX.json", json.dumps(index))
            packet.writestr(key, body)
        raw = memory.getvalue()
        path = self.root / "native-packet-001.zip"
        with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_STORED) as wrapper:
            wrapper.writestr("part-001.zip", raw)
        manifest = {"original_artifact": {"id": 13749339878}, "request_sha256": "f" * 64,
                    "payload_packets": [{"file": "part-001.zip", "bytes": len(raw),
                                         "sha256": digest(raw), "payload_count": 1}]}
        with ExitStack() as stack:
            sources = module.read_packets(manifest, [path], stack)
            actual = module.source_bytes(sources[(len(body), digest(body))][0], (len(body), digest(body)))
        self.assertEqual(actual, body)
        manifest["payload_packets"][0]["sha256"] = "0" * 64
        with ExitStack() as stack, self.assertRaisesRegex(ValueError, "packet digest mismatch"):
            module.read_packets(manifest, [path], stack)

    def test_original_metadata_members_are_exact_body_donors(self):
        """Catches dropping original metadata bytes that the snapshot also needs."""
        self.assertTrue(SCRIPT.is_file())
        spec = importlib.util.spec_from_file_location("tested_restore_metadata", SCRIPT)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        self.assertTrue(hasattr(module, "metadata_bodies"), "Metadata donors are missing")
        path = self.root / "part-000.zip"
        names = ["CHECKPOINT.json", "REQUEST.json", "EXPORT_MANIFEST.json",
                 "ORIGINAL_ARTIFACT_METADATA.json"]
        with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_STORED) as packet:
            for name in names:
                packet.writestr(name, ('{"name":"' + name + '"}\n').encode())
        with zipfile.ZipFile(path) as packet:
            bodies, sources = module.metadata_bodies(packet, path)
            for name in names:
                expected = ('{"name":"' + name + '"}\n').encode()
                self.assertEqual(bodies[name], expected)
                key = len(expected), digest(expected)
                self.assertEqual(module.source_bytes(sources[key][0], key), expected)


if __name__ == "__main__":
    unittest.main()
