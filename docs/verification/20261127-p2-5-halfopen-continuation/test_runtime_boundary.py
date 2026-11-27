"""Offline execution-boundary checks. No compiler, checker, cloud, or Git writes."""
from pathlib import Path
from types import SimpleNamespace
import json
import lzma
import tempfile
import unittest
from unittest.mock import patch

import prepare_halfopen as p
import run_scoped_normal as n


class RuntimeInputPlan(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = p.ROOT / (p.RESUMED + "p2-round14-context/EXTERNAL_SNAPSHOT.json.xz")
        cls.snapshot = json.loads(lzma.decompress(path.read_bytes()))

    def test_every_imported_object_native_source_and_runtime_stays_required(self):
        required, omitted = n.split_runtime_files(self.snapshot)
        self.assertEqual(len(required), 69342)
        self.assertEqual(len(omitted), 1041)
        self.assertTrue(set(self.snapshot["resolutions"].values()) <= set(required))
        self.assertTrue(all(r["source"] in required and r["object"] in required
                            for r in self.snapshot["modules"].values()))
        self.assertTrue(all(not path.endswith((".lean", ".olean", ".olean.private", ".olean.server", ".ir", ".ir.sig", ".so"))
                            for path in omitted))

    def test_setup_exception_is_only_one_exact_original_file(self):
        required, omitted = n.split_runtime_files(self.snapshot)
        self.assertIn(n.HISTORICAL_SETUP, omitted)
        other = n.HISTORICAL_SETUP + ".new"
        changed = dict(self.snapshot, files=dict(self.snapshot["files"]))
        changed["files"][other] = changed["files"][n.HISTORICAL_SETUP]
        required2, _ = n.split_runtime_files(changed)
        self.assertIn(other, required2)
        changed["files"][n.HISTORICAL_SETUP] = dict(changed["files"][n.HISTORICAL_SETUP], bytes=156)
        with self.assertRaises(ValueError):
            n.split_runtime_files(changed)

    def test_resolution_cannot_be_reclassified_as_metadata(self):
        changed = dict(self.snapshot, files=dict(self.snapshot["files"]))
        obj = next(iter(self.snapshot["resolutions"].values()))
        changed["files"][obj] = dict(changed["files"][obj], role="native-provider-receipt")
        with self.assertRaises(ValueError):
            n.split_runtime_files(changed)

    def test_original_proof_gates_remain_false(self):
        for key in ("compile_credit", "kernel_credit", "old_records_reconstructed",
                    "original_external_snapshot_verified", "R19_accepted", "P2_5_proved"):
            self.assertIs(p.CREDIT[key], False)
        self.assertEqual(n.STRICT_FLAGS, ["-t0", "-j1", "-M11264", "-DwarningAsError=true",
                                        "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000"])


class PhysicalBoundaryFailures(unittest.TestCase):
    def fixture(self, root):
        p.original_helpers(p.ROOT)
        from winner9_external_snapshot import PhysicalHashes
        snapshot = root / "snapshot.json"
        snapshot.write_bytes(b"synthetic test fixture")
        original = root / "runtime"
        (original / "Pkg").mkdir(parents=True)
        obj = original / "Pkg/M.olean"
        obj.write_bytes(b"bound")
        lean = original / "lean"
        lean.write_bytes(b"binary")
        lean.chmod(0o755)
        required = {str(obj): dict(bytes=5, sha256=p.sha(b"bound")),
                    str(lean): dict(bytes=6, sha256=p.sha(b"binary"))}
        # A local synthetic boundary tests fail-closed behavior only.
        return SimpleNamespace(
            snapshot=snapshot, snapshot_body=snapshot.read_bytes(), required=required,
            hashes=PhysicalHashes(), search=[root / "project", original],
            value=dict(resolutions={"Pkg.M": str(obj)}, packages={}),
            runtime=dict(lean=str(lean), leanchecker=str(lean)),
            plan=dict(toolchain=dict(mathlib_commit="test-pin", lean_binary_sha256=p.sha(b"binary"))),
            binding={"test_only": True}), obj

    def test_cached_physical_hash_detects_mutation(self):
        with tempfile.TemporaryDirectory() as raw:
            boundary, obj = self.fixture(Path(raw))
            with patch("run_scoped_normal.subprocess.check_output", return_value="test-pin\n"):
                self.assertEqual(n.ExecutionBoundary.verify(boundary), {"test_only": True})
                obj.write_bytes(b"drift")
                with self.assertRaises(ValueError):
                    n.ExecutionBoundary.verify(boundary)

    def test_shadowing_package_root_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            boundary, _ = self.fixture(Path(raw))
            (boundary.search[0] / "Pkg").mkdir(parents=True)
            with self.assertRaisesRegex(ValueError, "shadows"):
                n.ExecutionBoundary.verify(boundary)

    def test_unknown_runtime_companion_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            boundary, obj = self.fixture(Path(raw))
            obj.with_suffix(".ir").write_bytes(b"unexpected execution code")
            with self.assertRaisesRegex(ValueError, "Unfrozen runtime companion"):
                n.ExecutionBoundary.verify(boundary)


if __name__ == "__main__":
    unittest.main()
