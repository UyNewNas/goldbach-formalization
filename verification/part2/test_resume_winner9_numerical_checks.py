#!/usr/bin/env python3
"""Small offline regressions for resume boundaries; never invoke Lean or GitHub."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import resume_winner9_numerical_checks as R


class ResumeBoundaries(unittest.TestCase):
    def test_exact_page_and_check_slots(self):
        self.assertEqual(R.slot_target(14, "00"), R.I.PREFIX + "NumericalPage0224")
        self.assertEqual(R.slot_target(43, "01"), R.I.PREFIX + "NumericalPage0689")
        self.assertIsNone(R.slot_target(43, "02"))
        self.assertEqual(R.slot_target(43, "check"), R.I.PREFIX + "NumericalCheck43")
        for bad in (None, "16", "-1", "0/../1"):
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                R.slot_target(14, bad)

    def manifest(self, module):
        pages = {module: R.I.binding(module)} if "NumericalPage" in module else {}
        return {"accepted_modules": {module: {}}, "accepted_module_count": 1,
                "unselected_modules": [], "rejected_candidates": [], "duplicate_owned_declarations": [],
                "coverage": {"numerical_pages": {"bindings": pages, "accepted_bound_pages": len(pages),
                    "covered_rows": sum(item["row_count"] for item in pages.values())}},
                "transitive_axiom_counts": {"propext": 1}}

    def test_single_page_export_never_uses_block_minus_one_rule(self):
        for suffix in ("NumericalPage0224", "NumericalPage0689", "NumericalCheck43"):
            module = R.I.PREFIX + suffix
            good = self.manifest(module)
            R.export_gate(good, [module])
            for key, changed in (("unselected_modules", [module]), ("rejected_candidates", ["bad"]),
                                 ("accepted_module_count", 0), ("transitive_axiom_counts", {"sorryAx": 1})):
                value = copy.deepcopy(good); value[key] = changed
                with self.subTest(module=module, key=key), self.assertRaises(ValueError):
                    R.export_gate(value, [module])
        module = R.I.PREFIX + "NumericalPage0224"
        value = self.manifest(module)
        value["coverage"]["numerical_pages"]["bindings"][module]["first_ordinal"] += 1
        with self.assertRaises(ValueError):
            R.export_gate(value, [module])
        self.assertEqual(self.manifest(R.I.PREFIX + "NumericalPage0689")["coverage"]["numerical_pages"]["covered_rows"], 2)

    def test_public_metadata_is_exact(self):
        item = dict(R.I.FIXED_BOOTSTRAP)
        metadata = {"id": item["artifact_id"], "name": item["artifact_name"], "expired": False,
                    "size_in_bytes": item["zip_bytes"], "digest": "sha256:" + item["zip_sha256"],
                    "workflow_run": {"id": int(item["run_id"]), "head_sha": item["commit"]}}
        R.check_metadata(metadata, item)
        for key, value in (("id", 1), ("expired", True), ("size_in_bytes", 0), ("digest", "sha256:bad")):
            bad = copy.deepcopy(metadata); bad[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                R.check_metadata(bad, item)
        bad = copy.deepcopy(metadata); bad["workflow_run"]["head_sha"] = "0" * 40
        with self.assertRaises(ValueError):
            R.check_metadata(bad, item)

    def test_completed_replay_requires_original_snapshot_and_bytes(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); log = root / "replay.log"; log.write_bytes(b"stock replay success\n")
            module = R.I.PREFIX + "NumericalPage0224"
            frozen = {"project": {module: {"object": "/original/file.olean"}}, "toolchain": {"pin": "fixed"},
                      "lean_binary_sha256": "lean", "leanchecker_sha256": "checker"}
            receipt = {"replay_binding": R.A.replay_context(frozen), "replay": {
                "exit_code": 0, "inputs_unchanged": True, "command": [R.A.LEANCHECKER, "--verbose", module],
                "log": "replay.log", "log_sha256": R.sha(log)}}
            with patch.object(R, "ROOT", root):
                self.assertTrue(R.replay_reusable(module, receipt, frozen))
                moved = copy.deepcopy(frozen); moved["project"][module]["object"] = "/another/file.olean"
                self.assertFalse(R.replay_reusable(module, receipt, moved))
                log.write_bytes(b"changed\n")
                self.assertFalse(R.replay_reusable(module, receipt, frozen))

    def test_unplanned_preserved_compilation_blocks_rerun(self):
        current = {"run_id": "900", "run_attempt": 2, "commit": "new"}
        artifact = {"id": 999, "name": "p210-resume-compiled-14-00-900-1", "expired": False}
        with patch.object(R, "producer", return_value=current), patch.object(R, "api", return_value={"artifacts": [artifact]}):
            with self.assertRaises(ValueError):
                R.refuse_unplanned(14, {"recovery_inputs": []})
            R.refuse_unplanned(14, {"recovery_inputs": [{"artifact_id": 999}]})
            artifact["name"] = "p210-resume-compiled-14-00-900-2"
            R.refuse_unplanned(14, {"recovery_inputs": []})

    def test_check_missing_predecessor_never_invokes_compile(self):
        with tempfile.TemporaryDirectory() as temporary, patch.object(R, "guard", return_value={}), \
             patch.object(R, "slot_dir", return_value=Path(temporary)), patch.object(R, "output"), \
             patch.object(R, "verify_target", side_effect=ValueError("missing page")), patch.object(R, "timed") as run:
            with self.assertRaisesRegex(ValueError, "missing page"):
                R.compile_slot(14, "check")
            run.assert_not_called()

    def test_existing_compilation_never_invokes_compile(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            (directory / "state.json").write_text(json.dumps({"gates": {"strict_compile": True}, "accepted": False}))
            with patch.object(R, "guard", return_value={}), patch.object(R, "slot_dir", return_value=directory), \
                 patch.object(R, "verify_target"), patch.object(R, "output") as out, patch.object(R, "timed") as run:
                R.compile_slot(14, "0")
                run.assert_not_called()
                self.assertIn(unittest.mock.call(c_ready=True, accepted=False), out.call_args_list)

    def test_locator_exception_is_only_top_level(self):
        record = {"object": "/original/file", "command": ["lean", "-o", "/original/file"],
                  "closure_signature": "fixed", "attempts": [{"command": ["lean", "-o", "/original/file"]}]}
        moved = dict(record, object="/receiver/file")
        self.assertEqual(R.without_locator(record), R.without_locator(moved))
        changed = copy.deepcopy(moved); changed["command"][-1] = "/receiver/file"
        self.assertNotEqual(R.without_locator(record), R.without_locator(changed))

    def test_accepted_receipt_skips_auditor_and_only_exports(self):
        module = R.I.PREFIX + "NumericalPage0224"
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); directory = root / "slot"; directory.mkdir()
            registry = root / "records.json"; registry.write_bytes(b"{}\n")
            receipt = directory / "selected-receipt.json"; receipt.write_bytes(b'{"accepted":true}\n')
            state = {"gates": dict(R.I.GATES), "audit_origin": {"reuse": "relocated", "receipt_sha256": R.sha(receipt)}, "accepted": False}
            R.write(directory / "state.json", state)
            manifest = self.manifest(module); manifest["accepted_modules"][module]["receipt_sha256"] = R.sha(receipt)
            R.write(directory / "evidence/manifest.json", manifest)
            with patch.object(R, "slot_dir", return_value=directory), patch.object(R, "REGISTRY", registry), \
                 patch.object(R, "guard", return_value={}), patch.object(R, "verify_target", return_value={}), \
                 patch.object(R, "validate_receipt"), patch.object(R, "capture"), patch.object(R, "output"), \
                 patch.object(R, "timed", return_value=(0, "exported")) as run:
                R.audit_export(14, "0")
                self.assertEqual([call.args[2] for call in run.call_args_list], ["export"])
                self.assertTrue(R.read(directory / "state.json")["accepted"])

    def test_failed_owned_audit_keeps_successful_replay_checkpoint(self):
        module = R.I.PREFIX + "NumericalPage0224"
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary); directory = root / "slot"; directory.mkdir()
            registry = root / "records.json"; registry.write_bytes(b"{}\n")
            private = root / "private"
            latest = private / "audit" / module / "latest.json"
            R.write(latest, {"accepted": False, "replay": {"exit_code": 0, "inputs_unchanged": True}})
            R.write(directory / "state.json", {"gates": dict(R.I.GATES, owned_declarations_and_axioms=False),
                                                "audit_origin": None, "accepted": False})
            with patch.object(R, "slot_dir", return_value=directory), patch.object(R, "REGISTRY", registry), \
                 patch.object(R, "PRIVATE", private), patch.object(R, "guard", return_value={}), \
                 patch.object(R, "verify_target", return_value={}), patch.object(R, "replay_reusable", return_value=True), \
                 patch.object(R, "freeze_success"), patch.object(R, "capture") as capture, patch.object(R, "output"), \
                 patch.object(R, "timed", return_value=(1, "AUDIT " + module)) as run:
                with self.assertRaisesRegex(ValueError, "Owned audit not complete"):
                    R.audit_export(14, "0")
                self.assertEqual([call.args[2] for call in run.call_args_list], ["audit"])
                capture.assert_called_once_with(14, module, "progress")
                state = R.read(directory / "state.json")
                self.assertTrue(state["gates"]["stock_leanchecker"])
                self.assertFalse(state["gates"]["owned_declarations_and_axioms"])
                self.assertFalse(state["accepted"])


if __name__ == "__main__":
    unittest.main()
