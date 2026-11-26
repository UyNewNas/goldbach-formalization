"""Offline guard tests; synthetic successes never represent actual acceptance."""
import ast
import copy
import importlib.util
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

sys.dont_write_bytecode = True
FOLDER = Path(__file__).resolve().parent
ROOT = FOLDER.parents[3]
RUNNER = FOLDER / "run_typed_pulling.py"
spec = importlib.util.spec_from_file_location("typed_pulling_candidate", RUNNER)
R = importlib.util.module_from_spec(spec)
spec.loader.exec_module(R)

class DormantScopeTests(unittest.TestCase):
    def test_dormant_main_never_mutates(self):
        with patch.object(R.Path, "is_dir", side_effect=AssertionError("filesystem reached")), \
             patch.object(R.subprocess, "check_output", side_effect=AssertionError("process reached")), \
             patch.object(R.Path, "mkdir", side_effect=AssertionError("mutation reached")):
            with self.assertRaisesRegex(RuntimeError, "successful v6"):
                R.main()

    def test_missing_hash_rejected_even_if_review_flag_true(self):
        with patch.object(R, "V6_ARTIFACTS_REVIEWED", True):
            with self.assertRaises(RuntimeError): R.require_workflow_ready()

    def test_hash_does_not_replace_actual_review(self):
        with patch.object(R, "V6_RESULT_SHA", "1" * 64):
            with self.assertRaises(RuntimeError): R.require_workflow_ready()

    def test_actual_failed005_is_not_v6_success(self):
        previous = json.loads((ROOT / "docs/verification/20261126-p2-5-resumed/consumer-attempt005/RESULT.json").read_bytes())
        with self.assertRaises(RuntimeError): R.validate_v6_result(previous, previous)

    def test_exact_four_six_scope(self):
        manifest = json.loads((FOLDER / "RUNNER_MANIFEST.json").read_bytes())
        graph = R.validate_manifest(manifest)
        self.assertEqual(len(graph), 10)
        self.assertEqual(set(graph), set(R.FRESH_MODULES) | set(R.KNOWN_OBJECTS))
        self.assertEqual(len(R.FRESH_MODULES), 4)
        self.assertEqual(len(R.KNOWN_OBJECTS), 6)
        self.assertFalse(any("Literal96" in name or "TypedGeometry" in name for name in graph))

    def test_legacy_outer_actual_acceptance_is_bound(self):
        outer = json.loads((ROOT / R.LOCAL_LEGACY_OUTER).read_bytes())
        R.validate_private_outer(outer)
        bad = copy.deepcopy(outer)
        bad["compile_records"][R.INPUT]["object_sha256"] = "0" * 64
        with self.assertRaises(RuntimeError): R.validate_private_outer(bad)

    def test_fourteen_input_binding_cannot_be_dropped(self):
        outer = json.loads((ROOT / R.LOCAL_LEGACY_OUTER).read_bytes())
        outer["original_input_fresh_data_to_object_bound"] = False
        with self.assertRaises(RuntimeError): R.validate_private_outer(outer)

    def test_extra_source_rejected(self):
        manifest = json.loads((FOLDER / "RUNNER_MANIFEST.json").read_bytes())
        manifest["source_graph"]["ImbalancedChen.Unrelated"] = copy.deepcopy(next(iter(manifest["source_graph"].values())))
        with self.assertRaises(RuntimeError): R.validate_manifest(manifest)

    def test_stale_candidate_hash_rejected(self):
        manifest = json.loads((FOLDER / "RUNNER_MANIFEST.json").read_bytes())
        manifest["source_graph"][R.FRESH_MODULES[-1]]["source_sha256"] = "0" * 64
        with self.assertRaises(RuntimeError): R.validate_manifest(manifest)

    def test_original_disk_requirements(self):
        self.assertEqual(R.MIN_INITIAL_FREE_BYTES, 1024**3)
        self.assertEqual(R.GATE_WORKING_HEADROOM_BYTES, 256 * 1024**2)

if __name__ == "__main__": unittest.main(verbosity=2)
