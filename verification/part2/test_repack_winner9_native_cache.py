#!/usr/bin/env python3
"""Negative provenance checks and a synthetic byte-only export round trip."""
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

import repack_winner9_native_cache as carrier


OLD = "/home/runner/work/_temp/t01-project"


class Fixture:
    def __init__(self):
        self.payloads = {}
        self.cp = {"schema": "t01-coherent-build-checkpoint-v3", "runtime_audit_valid": True,
                   "all_dependency_source_pins_valid": True, "source_commit": carrier.ARTIFACT["producer_commit"],
                   "run_id": str(carrier.ARTIFACT["run_id"]), "run_attempt": "1",
                   "runtime_state": {"root": OLD}, "files": {}, "actual_import_sources": {},
                   "all_guarded_package_compilations": [], "modules": [], "packages": []}

    def record(self, path, data):
        digest = carrier.digest(data)
        member = "objects/" + digest
        self.payloads[member] = data
        row = {"original_path": path, "resolved_path": path, "bytes": len(data),
               "sha256": digest, "payload": member, "mode": 0o644}
        self.cp["files"][path] = row
        return row

    def module(self, name, source=b"import Mathlib.Data.Nat.Basic\n", classification=None):
        package = carrier.package_for(name)
        root = OLD if package == "project" else OLD + "/.lake/packages/" + package
        relative = name.replace(".", "/")
        source_row = self.record(root + "/" + relative + ".lean", source)
        facets = []
        for directory, suffix in [("lib/lean", ".olean"), ("lib/lean", ".ilean"),
                                  ("lib/lean", ".trace"), ("ir", ".c"), ("ir", ".setup.json")]:
            path = root + "/.lake/build/" + directory + "/" + relative + suffix
            facets.append(self.record(path, (name + ":fixture:" + suffix).encode()))
        setup = next(f for f in facets if f["original_path"].endswith(".setup.json"))
        row = {"module": name, "source": source_row, "setup": setup, "facet_files": facets,
               "classification": classification or (carrier.PROJECT_CLASSIFIED if package == "project" else carrier.CLASSIFIED),
               "lake_completed_trace": True, "output_bound_command": True,
               "missing_actual_import_artifacts": [], "missing_expected_direct_imports": [],
               "observed_output_descriptor_contradiction": False, "completed_guarded_compile_candidate": True,
               "required_output_parts": [f["original_path"] for f in facets if f["original_path"].endswith((".olean", ".ilean", ".c"))],
               "actual_import_map_sha256": "0" * 64,
               "command": {"tool": "lean", "command": ["fixture-only-never-run"], "cwd": OLD},
               "guarded_source_commands": [{"tool": "lean", "command": ["fixture-only-never-run"], "cwd": OLD}]}
        if package == "project":
            self.cp["modules"].append(row)
        else:
            row["package"] = package
            self.cp["all_guarded_package_compilations"].append(row)
        self.cp["actual_import_sources"][name] = {"package": package, "source": source_row}
        selected = {"package": package, "source_path": relative + ".lean",
                    "source_sha256": carrier.digest(source), "git_blob_sha1": carrier.blob_sha(source),
                    "source_bytes": len(source), "direct_imports": carrier.source_imports(source.decode())}
        return row, selected


class RepackTests(unittest.TestCase):
    def test_changed_source_is_not_a_cache_candidate(self):
        fixture = Fixture()
        _, wanted = fixture.module("MathlibNt.Example")
        wanted["source_sha256"] = "f" * 64
        selected, omitted, payloads, _ = carrier.select_payloads(fixture.cp, {"requested": {"MathlibNt.Example": wanted}})
        self.assertFalse(selected)
        self.assertFalse(payloads)
        self.assertEqual(omitted["MathlibNt.Example"], "NO_SOURCE_MATCHING_ORIGINAL_GUARDED_ROW")

    def test_project_selection_does_not_export_unrequested_theorems(self):
        fixture = Fixture()
        _, wanted = fixture.module("ImbalancedChen.Required")
        other, _ = fixture.module("ImbalancedChen.Unrelated")
        selected, _, payloads, _ = carrier.select_payloads(fixture.cp, {"requested": {"ImbalancedChen.Required": wanted}})
        self.assertEqual(set(selected), {"ImbalancedChen.Required"})
        self.assertNotIn(other["facet_files"][0]["payload"], payloads)
        self.assertEqual(selected["ImbalancedChen.Required"]["original_record_collection"], "modules")

    def test_architect_quarantine_is_carried_without_acceptance(self):
        fixture = Fixture()
        _, wanted = fixture.module("Architect.Command", classification=carrier.ARCHITECT_QUARANTINE)
        selected, _, _, _ = carrier.select_payloads(fixture.cp, {"requested": {"Architect.Command": wanted}})
        row = selected["Architect.Command"]
        self.assertEqual(row["original_classification"], carrier.ARCHITECT_QUARANTINE)
        self.assertTrue(row["separate_architect_leaf_qualification_required"])
        self.assertFalse(row["cache_acceptance"])
        self.assertFalse(row["compile_credit"])
        self.assertFalse(row["kernel_credit"])

    def test_other_quarantined_rows_are_not_exported(self):
        fixture = Fixture()
        _, wanted = fixture.module("MathlibNt.Incomplete", classification=carrier.ARCHITECT_QUARANTINE)
        selected, omitted, payloads, _ = carrier.select_payloads(fixture.cp, {"requested": {"MathlibNt.Incomplete": wanted}})
        self.assertFalse(selected)
        self.assertFalse(payloads)
        self.assertIn(carrier.ARCHITECT_QUARANTINE, omitted["MathlibNt.Incomplete"])

    def test_original_global_receipt_disagreement_is_rejected(self):
        fixture = Fixture()
        row, wanted = fixture.module("MathlibNt.Required")
        fixture.cp["files"][row["source"]["original_path"]] = {**row["source"], "sha256": "f" * 64}
        with self.assertRaisesRegex(ValueError, "Global/original"):
            carrier.select_payloads(fixture.cp, {"requested": {"MathlibNt.Required": wanted}})

    def test_conflicting_setup_pointer_is_rejected(self):
        fixture = Fixture()
        row, wanted = fixture.module("MathlibNt.Required")
        row["setup"] = {**row["setup"], "sha256": "f" * 64, "payload": "objects/" + "f" * 64}
        with self.assertRaisesRegex(ValueError, "Global/original"):
            carrier.select_payloads(fixture.cp, {"requested": {"MathlibNt.Required": wanted}})

    def test_other_module_facet_is_rejected(self):
        fixture = Fixture()
        row, wanted = fixture.module("MathlibNt.Required")
        unrelated, _ = fixture.module("MathlibNt.Unrelated")
        row["facet_files"].append(unrelated["facet_files"][0])
        with self.assertRaisesRegex(ValueError, "another module"):
            carrier.select_payloads(fixture.cp, {"requested": {"MathlibNt.Required": wanted}})

    def test_payload_tampering_is_rejected(self):
        fixture = Fixture()
        row = fixture.record(OLD + "/x", b"original")
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "original.zip"
            with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_STORED) as archive:
                archive.writestr(row["payload"], b"tampered")
            with zipfile.ZipFile(path) as archive:
                with self.assertRaisesRegex(ValueError, "SHA changed"):
                    carrier.read_payload(archive, row)

    def test_unbounded_single_packet_and_unsafe_member_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "cannot fit"):
            carrier.partition({"objects/" + "a" * 64: {"bytes": carrier.PART_LIMIT}})
        with tempfile.TemporaryDirectory() as directory:
            with zipfile.ZipFile(Path(directory) / "test.zip", "w") as archive:
                with self.assertRaisesRegex(ValueError, "Unsafe"):
                    carrier.zip_write(archive, "../outside", b"x")

    def test_pending_request_and_changed_artifact_are_rejected(self):
        with self.assertRaisesRegex(ValueError, "not finalized"):
            carrier.validate_request({"schema": carrier.SCHEMA, "status": "PENDING_ACTUAL_SOURCE_CENSUS"})
        metadata = {"id": carrier.ARTIFACT["id"], "expired": False,
                    "size_in_bytes": carrier.ARTIFACT["bytes"], "digest": "sha256:" + "0" * 64,
                    "workflow_run": {"id": carrier.ARTIFACT["run_id"], "head_sha": carrier.ARTIFACT["producer_commit"]}}
        with self.assertRaisesRegex(ValueError, "metadata differs"):
            carrier.validate_remote_metadata(metadata)

    def test_synthetic_export_preserves_bytes_and_grants_no_credit(self):
        fixture = Fixture()
        template = json.loads(Path(__file__).with_name("winner9_native_cache_request.json").read_text())
        projects = carrier.ROOTS + [f"ImbalancedChen.Fixture{i:03}" for i in range(242)]
        natives = [f"MathlibNt.Fixture{i:02}" for i in range(21)]
        names = projects + natives
        requested = {}
        for name in names:
            imports = names[1:] if name == names[0] else ["Mathlib.Data.Nat.Basic"]
            source = ("\n".join("import " + dep for dep in imports) + "\n").encode()
            requested[name] = {"package": carrier.package_for(name), "source_path": name.replace(".", "/") + ".lean",
                               "source_sha256": carrier.digest(source), "source_bytes": len(source),
                               "git_blob_sha1": carrier.blob_sha(source), "direct_imports": imports}
            if name in (names[0], natives[0]):
                fixture.module(name, source)
        fixture.cp["packages"] = [{"name": name, **row, "pin_matches": True, "tracked_sources_clean": True}
                                  for name, row in template["locked_packages"].items()]
        request = {**template, "status": carrier.READY, "requested": requested, "direct_native_roots": natives,
                   "source_census": {"sha256": "a" * 64, "script_sha256": carrier.CENSUS_SCRIPT_SHA,
                                     "status": "SOURCE_GRAPH_COMPLETE_CACHE_ACCEPTANCE_PENDING",
                                     "project_source_count": 247, "native_source_count": 21}}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            archive_path = root / "fixture.zip"
            cp_bytes = carrier.encoded(fixture.cp)
            with zipfile.ZipFile(archive_path, "w", compression=zipfile.ZIP_STORED) as archive:
                carrier.zip_write(archive, "CHECKPOINT.json", cp_bytes)
                for name, data in fixture.payloads.items():
                    carrier.zip_write(archive, name, data)
            fixture_anchor = {**carrier.ARTIFACT, "bytes": archive_path.stat().st_size,
                              "sha256": carrier.file_sha(archive_path), "checkpoint_bytes": len(cp_bytes),
                              "checkpoint_sha256": carrier.digest(cp_bytes)}
            request["artifact"] = fixture_anchor
            request_path, metadata_path = root / "request.json", root / "metadata.json"
            request_path.write_bytes(carrier.encoded(request))
            metadata_path.write_bytes(carrier.encoded({"id": fixture_anchor["id"], "expired": False,
                "size_in_bytes": fixture_anchor["bytes"], "digest": "sha256:" + fixture_anchor["sha256"],
                "workflow_run": {"id": fixture_anchor["run_id"], "head_sha": fixture_anchor["producer_commit"]}}))
            with patch.object(carrier, "ARTIFACT", fixture_anchor):
                carrier.repack(archive_path, request_path, metadata_path, root / "packets")
            with zipfile.ZipFile(root / "packets/part-000.zip") as archive:
                self.assertEqual(archive.read("CHECKPOINT.json"), cp_bytes)
                manifest = json.loads(archive.read("EXPORT_MANIFEST.json"))
                self.assertEqual(manifest["exported_module_count"], 2)
                self.assertFalse(manifest["cache_acceptance"])
                self.assertFalse(manifest["compile_credit"])
                self.assertFalse(manifest["kernel_credit"])
            with zipfile.ZipFile(root / "packets/part-001.zip") as archive:
                for name, original in fixture.payloads.items():
                    self.assertEqual(archive.read(name), original)


if __name__ == "__main__":
    unittest.main()
