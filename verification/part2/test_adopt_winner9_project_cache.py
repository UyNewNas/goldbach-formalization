"""Test cache-record adoption transactions with fixture bytes, never Lean credit."""
from __future__ import annotations

import contextlib
from copy import deepcopy
import io
import json
from pathlib import Path
import sys
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import adopt_winner9_project_cache as adopt
import test_private_cache_binding as cache_tests
from test_private_external_snapshot import NativeFixture
from winner9_external_snapshot import PhysicalHashes


class ProjectAdoptionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = cache_tests.ProofCacheBindingTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.native = NativeFixture(self.fixture)
        self.fixture.run_runner(extra_args=self.native.args())
        records = self.fixture.records()
        original_page = records.pop("ImbalancedChen.Page")
        self.fixture.write_records(records)
        self.stage = self.fixture.base / "stage"
        stem = self.stage / "candidates/project/.lake/build/lib/lean/ImbalancedChen/Page"
        stem.parent.mkdir(parents=True)
        self.obj = Path(original_page["object"])
        Path(str(stem) + ".olean").write_bytes(self.obj.read_bytes())
        self.obj.unlink()
        self.trace, self.setup = self.stage / "Page.trace", self.stage / "Page.setup.json"
        self.trace.write_text('{"synthetic_fixture":true}\n')
        self.setup.write_text('{"synthetic_fixture":true}\n')
        requested = {}
        for name in ("ImbalancedChen.Dep", "ImbalancedChen.Mid", "ImbalancedChen.Page"):
            source = self.fixture.root / (name.replace(".", "/") + ".lean")
            requested[name] = {"package": "project", "source_path": str(source.relative_to(self.fixture.root)),
                               "source_sha256": self.fixture.runner.digest(source),
                               "direct_imports": self.fixture.runner.parsed_source_imports(source.read_text())}
        request = {"requested": requested, "locked_packages": {"mathlib": {"rev": self.fixture.runner.PIN}}}
        (self.stage / "REQUEST.json").write_text(json.dumps(request))
        selected = {"ImbalancedChen.Page": {"source": {"sha256": original_page["source_sha256"]},
                                           "original_classification": adopt.carrier.PROJECT_CLASSIFIED,
                                           "original_guarded_row_index": 0}}
        self.q = SimpleNamespace(project=self.fixture.root, private_lib=self.fixture.cache / "lib",
                                 stage=self.stage, request=request, selected=selected,
                                 census={"topological_order": list(requested)},
                                 lean=Path(self.fixture.runner.LEAN), hashes=PhysicalHashes(),
                                 paths=[self.native.lib, self.native.sysroot / "lib/lean"],
                                 original=lambda name: ({"actual_import_map_sha256": "fixture-original-map"},
                                                        {"dynlibs": [], "plugins": []}, self.setup, self.trace),
                                 inputs=lambda *args, **kwargs: ({"dynlibs": [], "plugins": []}, {}),
                                 recheck=lambda: None)
        self.original_registry = self.fixture.records_path.read_bytes()

    def run_adoption(self) -> dict:
        previous = sys.argv
        try:
            sys.argv = [str(Path(adopt.__file__)), "--stage", str(self.stage), "--external-snapshot", str(self.native.path)]
            with patch.object(adopt, "Qualification", return_value=self.q), contextlib.redirect_stdout(io.StringIO()) as out:
                self.assertEqual(adopt.main(), 0)
            return json.loads(out.getvalue().splitlines()[-1])
        finally:
            sys.argv = previous

    def test_source_import_qualified_candidate_gets_a_new_historical_record(self) -> None:
        summary = self.run_adoption()
        self.assertEqual(summary["adopted"], 1)
        row = self.fixture.records()["ImbalancedChen.Page"]
        self.assertEqual(row["cache_schema"], 3)
        self.assertFalse(row["new_strict_compile"])
        self.assertEqual(row["external_check"]["status"], "PASSED_BATCH_PRE_POST")
        self.assertEqual(row["closure_signature"], self.fixture.runner.closure_signature(row))
        self.assertEqual(self.fixture.run_runner(extra_args=self.native.args())["reused"], 3)

    def test_missing_original_guarded_row_cannot_upgrade_a_record(self) -> None:
        self.q.selected = {}
        self.assertEqual(self.run_adoption()["adopted"], 0)
        self.assertNotIn("ImbalancedChen.Page", self.fixture.records())
        self.assertFalse(self.obj.exists())

    def test_an_existing_different_object_is_retained(self) -> None:
        self.obj.write_bytes(b"different existing object")
        self.assertEqual(self.run_adoption()["adopted"], 0)
        self.assertNotIn("ImbalancedChen.Page", self.fixture.records())
        self.assertEqual(self.obj.read_bytes(), b"different existing object")

    def test_mutated_project_source_cannot_publish_provisional_records(self) -> None:
        def mutate():
            (self.fixture.root / "ImbalancedChen/Page.lean").write_text("import ImbalancedChen.Mid\ndef changedSource := 17\n")
        self.q.recheck = mutate
        with self.assertRaisesRegex(ValueError, "Source/object differs"):
            self.run_adoption()
        self.assertEqual(self.fixture.records_path.read_bytes(), self.original_registry)

    def test_failed_late_evidence_copy_cannot_publish_a_successful_record(self) -> None:
        original_copy = adopt.atomic_missing
        def fail_trace(path, raw, expected):
            if path.name.endswith(".trace.json"):
                raise OSError("fixture failure copying the original trace")
            return original_copy(path, raw, expected)
        with patch.object(adopt, "atomic_missing", side_effect=fail_trace):
            self.assertEqual(self.run_adoption()["adopted"], 0)
        self.assertEqual(self.fixture.records_path.read_bytes(), self.original_registry)
        self.assertNotIn("ImbalancedChen.Page", self.fixture.records())


if __name__ == "__main__":
    unittest.main()
