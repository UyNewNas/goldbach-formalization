"""Local validator tests; never execute or emit a Lean controller."""
import ast
import base64
import hashlib
import json
import inspect
from pathlib import Path
import tempfile
import unittest

try:
    import build_v5 as builder
except ModuleNotFoundError:
    builder = None


class BuilderTests(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(builder, "v5 builder has not been implemented")

    def test_pinned_bytes_reject_tampering(self):
        row = {"bytes": 3, "sha256": "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad", "base64": "YWJj"}
        self.assertEqual(builder.decode_pinned(row), b"abc")
        row["base64"] = "YWJk"
        with self.assertRaises(builder.BuildError):
            builder.decode_pinned(row)

    def test_pinned_bytes_reject_missing_payload(self):
        with self.assertRaises(builder.BuildError):
            builder.decode_pinned({"bytes": 0, "sha256": hashlib.sha256(b"").hexdigest()})

    def test_probe_requires_parent_bound_completed_bytes(self):
        self.assertTrue(hasattr(builder, "authenticate_probe"), "completed probe authority gate is missing")
        raw = (builder.PACKET / "PROBE_RESULT.json").read_bytes()
        self.assertEqual(builder.authenticate_probe(raw), raw)
        with self.assertRaises(builder.BuildError):
            builder.authenticate_probe(raw + b" ")

    def test_canonical_runtime_file_cannot_bypass_authority_with_payload(self):
        self.assertTrue(hasattr(builder, "decode_runtime_file"), "canonical runtime authority gate is missing")
        raw = b"different"
        row = {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest(), "base64": base64.b64encode(raw).decode()}
        with self.assertRaises(builder.BuildError):
            builder.decode_runtime_file(row, b"known original")
        self.assertEqual(builder.decode_runtime_file(row, raw), raw)

    def test_prior_request_requires_exact_reviewed_command(self):
        self.assertTrue(hasattr(builder, "authenticate_prior_request"), "complete prior request authority gate is missing")
        raw = (builder.PRIOR / "ACTUAL_REQUEST.json").read_bytes()
        builder.authenticate_prior_request(raw)
        request = json.loads(raw)
        lines = request["command"].splitlines()
        lines[-2] = "pass"
        request["command"] = "\n".join(lines) + "\n"
        with self.assertRaises(builder.BuildError):
            builder.authenticate_prior_request((json.dumps(request, indent=2) + "\n").encode())

    def test_guard_chain_accepts_exact_contiguous_slices(self):
        old = b'{"tool":"lean","input_args":["--version"]}\n'
        first = b'{"tool":"lake","input_args":["env","python3"]}\n'
        second = b'{"tool":"lean","input_args":["--stdin"]}\n'
        rows = [
            {"guard_log_start": len(old), "guard_log_end": len(old + first), "guarded_commands": [json.loads(first)], "forbidden_source_calls": []},
            {"guard_log_start": len(old + first), "guard_log_end": len(old + first + second), "guarded_commands": [json.loads(second)], "forbidden_source_calls": []},
        ]
        self.assertEqual(builder.validate_guard_chain(old, old + first + second, rows), 2)

    def test_guard_chain_rejects_unattributed_tail_and_source_call(self):
        old = b'{"tool":"lean","input_args":["--version"]}\n'
        appended = b'{"tool":"lean","input_args":["--stdin"]}\n'
        rec = {"guard_log_start": len(old), "guard_log_end": len(old + appended), "guarded_commands": [json.loads(appended)], "forbidden_source_calls": []}
        with self.assertRaises(builder.BuildError):
            builder.validate_guard_chain(old, old + appended + b'{}\n', [rec])
        source = b'{"tool":"lean","input_args":["Supplier.lean"]}\n'
        rec = {"guard_log_start": len(old), "guard_log_end": len(old + source), "guarded_commands": [json.loads(source)], "forbidden_source_calls": []}
        with self.assertRaises(builder.BuildError):
            builder.validate_guard_chain(old, old + source, [rec])

    def test_guard_chain_rejects_rewritten_original_prefix(self):
        with self.assertRaises(builder.BuildError):
            builder.validate_guard_chain(b'{}\n', b'{"changed":true}\n', [])

    def candidate(self, path, revision="abc", count=2):
        return {"path": path, "resolved": path, "exists": True, "is_symlink": False, "lib_exists": True,
                "git": {"toplevel": {"exit_code": 0, "stdout": path}, "HEAD": {"exit_code": 0, "stdout": revision}},
                "historical_facets_present_by_metadata": count, "historical_facets_missing_by_metadata": 0}

    def test_provider_selection_rejects_same_revision_wrong_root(self):
        original = "/accepted/batteries"
        alternate = "/other/batteries"
        record = {"manifest_revision": "abc", "historical_facet_count": 2, "historical_roots": [original], "candidates": [self.candidate(alternate)]}
        with self.assertRaises(builder.BuildError):
            builder.select_historical_provider("batteries", record)
        record["candidates"].append(self.candidate(original))
        self.assertEqual(builder.select_historical_provider("batteries", record)["path"], original)

    def test_provider_selection_rejects_missing_facets_and_wrong_head(self):
        path = "/accepted/aesop"
        candidate = self.candidate(path)
        record = {"manifest_revision": "abc", "historical_facet_count": 2, "historical_roots": [path], "candidates": [candidate]}
        candidate["historical_facets_missing_by_metadata"] = 1
        candidate["historical_facets_present_by_metadata"] = 1
        with self.assertRaises(builder.BuildError):
            builder.select_historical_provider("aesop", record)
        candidate.update(historical_facets_missing_by_metadata=0, historical_facets_present_by_metadata=2)
        candidate["git"]["HEAD"]["stdout"] = "wrong"
        with self.assertRaises(builder.BuildError):
            builder.select_historical_provider("aesop", record)

    def test_main_only_gate_accepts_main_change_rejects_helper_change(self):
        original = "PIN = 7\ndef helper():\n return 1\ndef main():\n return helper()\nmain()\n"
        changed = original.replace("return helper()", "return helper() + 2")
        self.assertEqual(builder.validate_main_only(original, changed), ["helper"])
        with self.assertRaises(builder.BuildError):
            builder.validate_main_only(original, changed.replace("return 1", "return 9"))

    def test_recorded_path_rejects_frozen_old_view_alias(self):
        previous = {"batteries": "/old/batteries"}
        selected = {"batteries": "/accepted/batteries"}
        token = str(builder.V4_VIEW / "batteries/.lake/build/lib/lean")
        with self.assertRaises(builder.BuildError):
            builder.reusable_path_tokens([token], previous, selected)
        builder.reusable_path_tokens([".lake/packages/batteries/.lake/build/lib/lean"], previous, selected)

    def test_recorded_path_rejects_parent_traversal_in_receiver_alias(self):
        previous = {"batteries": "/old/batteries"}
        selected = {"batteries": "/accepted/batteries"}
        token = str(builder.ROOT / ".lake/packages") + "/../packages-mathlib-resume-v4/batteries/.lake/build/lib/lean"
        with self.assertRaises(builder.BuildError):
            builder.reusable_path_tokens([token], previous, selected)

    def test_missing_probe_never_creates_output_directory(self):
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent) as td:
            directory = Path(td)
            output = directory / "no-output"
            with self.assertRaises(builder.BuildError):
                builder.build(directory / "missing.json", output)
            self.assertFalse(output.exists())

    def reviewed_prefix_fixture(self):
        source = (builder.OLD / "postimage.py").read_text()
        changed = source.replace("rec=stage(label,runprefix+['lake','env','leanchecker'", "rec=stage(label,viewprefix+['leanchecker'", 1)
        changed = changed.replace("rec=stage(label,runprefix+['lake','env','lean'", "rec=stage(label,viewprefix+['lean'", 1)
        changed = changed.replace("process=stage(label,runprefix+['lake','env','lean'", "process=stage(label,viewprefix+['lean'", 1)
        changed = changed.replace("normal_cmd=runprefix+['lake','env','lean'", "normal_cmd=viewprefix+['lean'", 1)
        return source, changed

    def test_reviewed_delta_allows_exact_three_prefix_changes(self):
        self.assertTrue(hasattr(builder, "validate_reviewed_delta"), "reviewed three-prefix normalization is missing")
        original, changed = self.reviewed_prefix_fixture()
        result = builder.validate_reviewed_delta(original, changed)
        self.assertEqual(result["normalized_prefix_helpers"], ["actual_inputs", "full_owned", "named_kernel"])

    def test_reviewed_delta_rejects_validation_body_or_audit_prefix_changes(self):
        self.assertTrue(hasattr(builder, "validate_reviewed_delta"), "reviewed three-prefix normalization is missing")
        original, changed = self.reviewed_prefix_fixture()
        weakened = changed.replace("assert digest==known['identity']['sha256']", "assert True or digest==known['identity']['sha256']")
        with self.assertRaises(builder.BuildError):
            builder.validate_reviewed_delta(original, weakened)
        wrong_audit = changed.replace("stage('runtime-final-audit',runprefix+", "stage('runtime-final-audit',viewprefix+")
        with self.assertRaises(builder.BuildError):
            builder.validate_reviewed_delta(original, wrong_audit)
        weakened_main = changed.replace("assert bound_after==bound_before", "assert bound_after>=0")
        with self.assertRaises(builder.BuildError):
            builder.validate_reviewed_delta(original, weakened_main)

    def test_missing_cache_probe_never_emits_a_controller(self):
        self.assertIn("cache_probe_path", inspect.signature(builder.build).parameters, "cache evidence gate is missing")
        with tempfile.TemporaryDirectory(dir=Path(__file__).parent) as td:
            output = Path(td) / "no-output"
            with self.assertRaisesRegex(builder.BuildError, "CACHE_PROBE_RESULT"):
                builder.build(builder.PACKET / "PROBE_RESULT.json", output, cache_probe_path=Path(td) / "CACHE_PROBE_RESULT.json")
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
