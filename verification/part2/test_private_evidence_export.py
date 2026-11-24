"""Evidence packaging tests; fixture processes provide no Lean proof credit."""
from __future__ import annotations

import contextlib
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tarfile
import unittest

import test_private_audit as audit_tests
import winner9_external_snapshot as native_env
from test_private_external_snapshot import NativeFixture


EXPORTER = Path(__file__).with_name("export_winner9_private_evidence.py")


class PrivateEvidenceExportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = audit_tests.PrivateAuditTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.fixture.run_audit()
        self.root = self.fixture.root
        self.out = self.fixture.fixture.base / "export"

    def exporter(self):
        self.assertTrue(EXPORTER.is_file(), "The evidence exporter is not implemented")
        spec = importlib.util.spec_from_file_location("winner9_export_test", EXPORTER)
        module = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(module)
        module.LEAN = self.fixture.fixture.runner.LEAN
        module.LEANCHECKER = str(self.fixture.checker)
        module.MATHLIB = self.fixture.fixture.runner.MATHLIB
        module.PIN = self.fixture.fixture.runner.PIN
        return module

    def run_export(self, extra_args: list[str] | None = None) -> dict:
        module = self.exporter()
        previous_dir, previous_args = Path.cwd(), sys.argv
        try:
            os.chdir(self.root)
            sys.argv = [str(EXPORTER), "--output-dir", str(self.out), "--split", "module", *(extra_args or [])]
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(module.main(), 0)
            return json.loads((self.out / "manifest.json").read_text())
        finally:
            os.chdir(previous_dir)
            sys.argv = previous_args

    def test_packages_only_verified_modules_and_never_objects(self) -> None:
        (self.root / ".lake/p2-private/benchstable-diagnostic.json").write_text(
            json.dumps({"module": "ImbalancedChen.Diagnostic", "exit_code": 0}))
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 1)
        self.assertEqual(result["owned_declaration_count"], 2)
        self.assertFalse(result["full_p2_complete"])
        self.assertFalse(result["coverage"]["geometry"]["complete"])
        self.assertEqual(len(result["packages"]), 2)
        names = []
        for package in result["packages"]:
            with tarfile.open(package["path"], "r:gz") as stream:
                names.extend(stream.getnames())
        self.assertFalse(any(".olean" in Path(name).suffixes for name in names))
        self.assertTrue(any(name.endswith("types.txt") for name in names))
        self.assertTrue(any(name.endswith("benchstable-diagnostic.json") for name in names))

    def test_unbound_native_cache_requires_explicit_extra_evidence(self) -> None:
        private = self.root / ".lake/p2-private"
        candidates = [private / "native-cache/staged/checkpoint.json",
                      private / "diagnostics/native-cache/unqualified.json"]
        for path in candidates:
            path.parent.mkdir(parents=True)
            path.write_bytes(b'{ "fixture_only": true, "qualified": false }\r\n')
        ordinary = private / "native-cache-summary.json"
        ordinary.write_text('{"fixture_only":true}\n')
        result = self.run_export()
        origins = {item["origin"] for item in result["files"].values()}
        self.assertTrue(all(str(path) not in origins for path in candidates))
        self.assertIn(str(ordinary), origins)
        self.assertEqual(result["external_snapshots"], {})
        self.assertEqual(result["accepted_module_count"], 1)
        self.assertEqual(result["owned_declaration_count"], 2)

        self.out = self.out.with_name("export-explicit")
        explicit = self.run_export(["--extra-evidence", str(private / "native-cache")])
        origins = {item["origin"] for item in explicit["files"].values()}
        self.assertIn(str(candidates[0]), origins)
        self.assertNotIn(str(candidates[1]), origins)
        self.assertEqual(explicit["accepted_module_count"], result["accepted_module_count"])
        self.assertEqual(explicit["owned_declaration_count"], result["owned_declaration_count"])

    def test_changed_project_dependency_is_not_counted(self) -> None:
        (self.root / "ImbalancedChen/Dep.lean").write_text("changed after acceptance\n")
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 0)
        self.assertTrue(result["rejected_candidates"])

    def test_unaccepted_latest_does_not_hide_valid_immutable_v1_receipt(self) -> None:
        exporter = self.exporter()
        directory = self.root / ".lake/p2-private/audit/ImbalancedChen.Page"
        receipt_path = directory / "attempt-001/receipt.json"
        receipt = json.loads(receipt_path.read_text())
        receipt["input_snapshot"]["driver_sha256"] = exporter.DRIVER_V1
        receipt["input_sha256"] = exporter.json_digest(receipt["input_snapshot"])
        receipt_path.write_text(json.dumps(receipt))
        (directory / "latest.json").write_text(json.dumps({"module": "ImbalancedChen.Page", "accepted": False}))
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 1)
        self.assertEqual(result["accepted_modules"]["ImbalancedChen.Page"]["driver_sha256"], exporter.DRIVER_V1)
        self.assertTrue(any(name.endswith("attempt-001/replay.log") for name in result["files"]))

    def test_changed_audit_artifact_is_not_counted(self) -> None:
        (self.root / ".lake/p2-private/audit/ImbalancedChen.Page/attempt-001/types.txt").write_text("changed")
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 0)

    def test_last_numerical_page_covers_two_rows_only(self) -> None:
        exporter = self.exporter()
        module = "ImbalancedChen.P2Winner9NumericalPage0689"
        source = (EXPORTER.parents[2] / "docs/source-only/20261124-p2-winner9/ImbalancedChen/P2Winner9NumericalPage0689.lean").read_text()
        declarations = [{"name": module + ".checked", "type":
            "ImbalancedChen.P2Winner9SeedArchiveChecks.Checked "
            "ImbalancedChen.P2Winner9SelectedArchiveChecker.checkSelected "
            "ImbalancedChen.P2Winner9CompleteSeedBlock43.pages"}]
        result = exporter.page_binding(module, source, declarations)
        self.assertEqual(result["first_ordinal"], 11024)
        self.assertEqual(result["row_count"], 2)

    def native_receipt(self, trace: bytes | None = None, *, in_native_cache: bool = False):
        native = NativeFixture(self.fixture.fixture, self.fixture.checker)
        if in_native_cache:
            directory = self.root / ".lake/p2-private/native-cache/qualified"
            directory.mkdir(parents=True)
            for field in ("path", "provider", "qualification"):
                previous = getattr(native, field)
                current = directory / previous.name
                previous.rename(current)
                setattr(native, field, current)
            native.write()
        if trace is not None:
            trace_path = native.path.with_name("native-original.trace")
            trace_path.write_bytes(trace)
            snapshot = json.loads(native.path.read_text())
            snapshot.pop("context_signature")
            snapshot["files"][str(trace_path)] = {
                "sha256": hashlib.sha256(trace).hexdigest(), "bytes": len(trace), "role": "original-trace"}
            snapshot["context_signature"] = native_env.signature(snapshot)
            native.path.write_text(json.dumps(snapshot, indent=2) + "\n")
        self.fixture.fixture.run_runner(extra_args=native.args())
        receipt = self.fixture.run_audit(extra_args=native.args())
        self.assertTrue(receipt["accepted"])
        return native, receipt

    def test_native_snapshot_and_provider_texts_are_retained_without_objects(self) -> None:
        native, receipt = self.native_receipt()
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 1)
        self.assertEqual(result["accepted_modules"]["ImbalancedChen.Page"]["external_snapshot"],
                         receipt["input_snapshot"]["external_snapshot"])
        self.assertTrue(result["external_snapshots"])
        exported_origins = {item["origin"] for item in result["files"].values()}
        self.assertTrue({str(native.path), str(native.provider), str(native.qualification), str(native.source)} <= exported_origins)
        self.assertNotIn(str(native.obj), exported_origins)

    def test_original_json_trace_is_archived_without_changing_bytes(self) -> None:
        raw = '{ "fixture_only": true, "label": "原始追踪", "escaped": "\\u03bb" }\r\n'.encode("utf-8")
        native, receipt = self.native_receipt(raw, in_native_cache=True)
        unbound = native.path.with_name("unqualified-candidate.json")
        unbound.write_text('{"fixture_only":true,"qualified":false}\n')
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 1)
        self.assertEqual(result["accepted_modules"]["ImbalancedChen.Page"]["external_snapshot"],
                         receipt["input_snapshot"]["external_snapshot"])
        origin = str(native.path.with_name("native-original.trace"))
        context = next(iter(result["external_snapshots"].values()))
        name = context["text_artifact_map"][origin]
        self.assertTrue(name.endswith("native-original.trace.json"))
        self.assertEqual(result["files"][name]["origin"], origin)
        self.assertEqual(result["files"][name]["sha256"], hashlib.sha256(raw).hexdigest())
        expected = {name: raw, context["snapshot_archive"]: native.path.read_bytes()}
        for path in (native.provider, native.qualification):
            archived = context["text_artifact_map"][str(path)]
            self.assertEqual(result["files"][archived]["origin"], str(path))
            self.assertEqual(result["files"][archived]["sha256"], hashlib.sha256(path.read_bytes()).hexdigest())
            expected[archived] = path.read_bytes()
        self.assertNotIn(str(unbound), {item["origin"] for item in result["files"].values()})
        payloads = {archived: [] for archived in expected}
        for package in result["packages"]:
            with tarfile.open(package["path"], "r:gz") as stream:
                for archived in expected:
                    if archived in stream.getnames():
                        payloads[archived].append(stream.extractfile(archived).read())
        self.assertEqual(payloads, {archived: [data] for archived, data in expected.items()})

    def test_original_trace_with_invalid_utf8_is_rejected(self) -> None:
        self.native_receipt(b'{"fixture_only":true,"invalid":"\xff"}')
        with self.assertRaisesRegex(ValueError, "Original trace must be UTF-8 JSON"):
            self.run_export()

    def test_original_trace_with_invalid_json_is_rejected(self) -> None:
        self.native_receipt(b'UTF-8 text that is not JSON\n')
        with self.assertRaisesRegex(ValueError, "Original trace must be UTF-8 JSON"):
            self.run_export()

    def test_changed_native_object_is_not_counted(self) -> None:
        native, _ = self.native_receipt()
        native.obj.write_bytes(b"changed after accepted native audit")
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 0)
        self.assertTrue(any("External physical input changed" in item["reason"] for item in result["rejected_candidates"]))

    def test_legacy_driver_receipt_cannot_be_retrofitted_with_native_context(self) -> None:
        _, receipt = self.native_receipt()
        exporter = self.exporter()
        directory = self.root / ".lake/p2-private/audit/ImbalancedChen.Page"
        for path in [directory / "latest.json", *directory.glob("attempt-*/receipt.json")]:
            current = json.loads(path.read_text())
            if "external_snapshot" in current.get("input_snapshot", {}):
                current["input_snapshot"]["driver_sha256"] = exporter.DRIVER_V1
                current["input_sha256"] = exporter.json_digest(current["input_snapshot"])
                path.write_text(json.dumps(current))
        result = self.run_export()
        self.assertEqual(result["accepted_module_count"], 0)


if __name__ == "__main__":
    unittest.main()
