"""Regression tests for proof-cache provenance, using a tiny compiler fixture.

The fixture only stands in for the external Lean process. The production
runner, filesystem, dependency scheduling, Git baseline and records are real.
These tests grant no Lean proof credit.
"""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest


RUNNER = Path(__file__).with_name("run_winner9_private_checks.py")


class ProofCacheBindingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.baseline = self.base / "baseline"
        self.root = self.base / "verification"
        for root in (self.baseline, self.root):
            (root / "ImbalancedChen").mkdir(parents=True)
        dep_source = "def baselineValue : Nat := 0\n"
        for root in (self.baseline, self.root):
            (root / "ImbalancedChen/Dep.lean").write_text(dep_source)
        (self.root / "ImbalancedChen/Mid.lean").write_text("import ImbalancedChen.Dep\n")
        (self.root / "ImbalancedChen/Page.lean").write_text("import ImbalancedChen.Mid\n")
        for args in (["init", "-q"], ["add", "ImbalancedChen/Dep.lean"],
                     ["-c", "user.name=Cache Test", "-c", "user.email=cache@example.invalid",
                      "commit", "-qm", "cache fixture"]):
            subprocess.run(["git", *args], cwd=self.baseline, check=True, capture_output=True)
        baseline_lib = self.baseline / ".lake/build/lib/lean/ImbalancedChen"
        baseline_lib.mkdir(parents=True)
        (baseline_lib / "Dep.olean").write_bytes(b"accepted baseline object")
        compiler = self.base / "compiler-fixture"
        compiler.write_text("""#!/usr/bin/env python3
import hashlib, pathlib, sys
if '--version' in sys.argv:
    print('Lean (proof-cache regression fixture)')
    raise SystemExit(0)
obj = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])
source = pathlib.Path(sys.argv[-1])
# Mid intentionally has stable object bytes across dependency changes.
body = source.read_bytes() if source.stem == 'Dep' else source.stem.encode()
obj.write_bytes(hashlib.sha256(body).digest())
mutation = pathlib.Path('change-dependency-during-page')
if source.stem == 'Page' and mutation.exists():
    pathlib.Path(mutation.read_text()).write_bytes(b'changed by the compiler fixture')
if source.stem == 'Mid' and pathlib.Path('expire-budget-after-mid').exists():
    pathlib.Path('budget-expired').touch()
""")
        compiler.chmod(0o755)
        spec = importlib.util.spec_from_file_location("private_cache_runner_test", RUNNER)
        self.runner = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(self.runner)
        self.runner.LEAN = str(compiler)
        self.runner.BASELINE = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=self.baseline, text=True).strip()
        self.runner.MATHLIB = str(self.baseline)
        self.runner.PIN = self.runner.BASELINE
        self.cache = self.root / ".lake/p2-private"
        self.records_path = self.cache / "records.json"

    def run_runner(self, expected_exit: int = 0, extra_args: list[str] | None = None) -> dict:
        previous_dir, previous_args = Path.cwd(), sys.argv
        try:
            os.chdir(self.root)
            sys.argv = [str(RUNNER), "ImbalancedChen.Page", "--baseline-root", str(self.baseline)]
            sys.argv.extend(extra_args or [])
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                try:
                    result = self.runner.main()
                except SystemExit as error:
                    self.fail(f"Runner exited before returning its status summary: {error}")
            self.assertEqual(result, expected_exit, output.getvalue())
            return json.loads(output.getvalue().splitlines()[-1])
        finally:
            os.chdir(previous_dir)
            sys.argv = previous_args

    def records(self) -> dict:
        return json.loads(self.records_path.read_text())

    def write_records(self, records: dict) -> None:
        self.records_path.write_text(json.dumps(records))

    def make_probe(self, *, remove: tuple[str, ...] = ()) -> None:
        records = self.records()
        page = records.pop("ImbalancedChen.Page")
        for key in remove:
            page.pop(key, None)
        (self.cache / "probe-records.json").write_text(json.dumps({"page": page}))
        self.write_records(records)

    def test_legacy_probe_without_dependency_snapshot_is_not_adopted(self) -> None:
        self.run_runner()
        self.make_probe(remove=("deps", "dependency_signatures", "closure_signature"))
        self.assertEqual(self.run_runner()["reused"], 2)

    def test_probe_with_changed_direct_dependency_is_not_rebound(self) -> None:
        self.run_runner()
        self.make_probe()
        probes_path = self.cache / "probe-records.json"
        probes = json.loads(probes_path.read_text())
        probes["page"]["deps"]["ImbalancedChen.Mid"] = "0" * 64
        probes_path.write_text(json.dumps(probes))
        self.assertEqual(self.run_runner()["reused"], 2)

    def test_transitive_change_invalidates_page_even_when_mid_object_is_identical(self) -> None:
        self.run_runner()
        old_mid = self.records()["ImbalancedChen.Mid"]["object_sha256"]
        (self.root / "ImbalancedChen/Dep.lean").write_text("def baselineValue : Nat := 1\n")
        result = self.run_runner()
        self.assertEqual(self.records()["ImbalancedChen.Mid"]["object_sha256"], old_mid)
        self.assertEqual(result["reused"], 0)
        self.assertEqual(len(self.records()["ImbalancedChen.Page"]["attempts"]), 2)

    def test_old_absolute_object_path_cannot_validate_wrong_current_object(self) -> None:
        self.run_runner()
        records = self.records()
        page = records["ImbalancedChen.Page"]
        current = Path(page["object"])
        old = self.base / "historical-page.olean"
        shutil.copy2(current, old)
        page["object"] = str(old)
        current.write_bytes(b"wrong object in the actual import path")
        self.write_records(records)
        self.assertEqual(self.run_runner()["reused"], 2)

    def test_matching_probe_does_not_overwrite_valid_compiler_record(self) -> None:
        self.run_runner()
        records = self.records()
        records["ImbalancedChen.Page"]["provenance"] = "direct private compilation"
        (self.cache / "probe-records.json").write_text(json.dumps({"page": records["ImbalancedChen.Page"]}))
        self.write_records(records)
        self.assertEqual(self.run_runner()["reused"], 3)
        self.assertEqual(self.records()["ImbalancedChen.Page"]["provenance"], "direct private compilation")

    def test_matching_probe_with_complete_frozen_signatures_can_be_reused(self) -> None:
        self.run_runner()
        self.make_probe()
        self.assertEqual(self.run_runner()["reused"], 3)

    def test_compiler_mutating_transitive_dependency_object_cannot_earn_credit(self) -> None:
        (self.root / "change-dependency-during-page").write_text(
            ".lake/p2-private/lib/ImbalancedChen/Dep.olean")
        self.assertEqual(self.run_runner(expected_exit=1)["failed_or_blocked"], ["ImbalancedChen.Page"])
        self.assertEqual(self.records()["ImbalancedChen.Page"]["exit_code"], 125)
        self.assertFalse(self.records()["ImbalancedChen.Page"]["new_strict_compile"])

    def test_compiler_mutating_transitive_dependency_source_cannot_earn_credit(self) -> None:
        (self.root / "change-dependency-during-page").write_text("ImbalancedChen/Dep.lean")
        self.assertEqual(self.run_runner(expected_exit=1)["failed_or_blocked"], ["ImbalancedChen.Page"])
        self.assertEqual(self.records()["ImbalancedChen.Page"]["exit_code"], 125)
        self.assertFalse(self.records()["ImbalancedChen.Page"]["new_strict_compile"])

    def test_zero_budget_preserves_pending_without_starting_compilation(self) -> None:
        result = self.run_runner(expected_exit=2, extra_args=["--time-budget-seconds", "0"])
        self.assertEqual(result["status"], "partial")
        self.assertEqual(result["pending"], ["ImbalancedChen.Mid", "ImbalancedChen.Page"])
        self.assertEqual(result["successful_closure"], 1)
        self.assertFalse(result["complete"])
        self.assertEqual(list(self.records()), ["ImbalancedChen.Dep"])
        self.assertFalse((self.cache / "lib/ImbalancedChen/Mid.olean").exists())
        self.assertFalse((self.cache / "lib/ImbalancedChen/Page.olean").exists())

    def test_zero_budget_still_reuses_the_entire_valid_cache(self) -> None:
        self.run_runner()
        result = self.run_runner(extra_args=["--time-budget-seconds", "0"])
        self.assertEqual(result.get("status"), "complete")
        self.assertEqual(result["pending"], [])
        self.assertEqual(result["reused"], 3)
        self.assertTrue(result["complete"])

    def test_default_budget_completes_the_uncached_closure(self) -> None:
        result = self.run_runner()
        self.assertEqual(result.get("status"), "complete")
        self.assertEqual(result["pending"], [])
        self.assertEqual(result["successful_closure"], 3)
        self.assertIsNone(result["time_budget_seconds"])

    def test_budget_expiry_drains_running_module_before_reporting_pending(self) -> None:
        (self.root / "expire-budget-after-mid").touch()
        self.runner.time = SimpleNamespace(monotonic=lambda:
            10.0 if (self.root / "budget-expired").exists() else 0.0)
        result = self.run_runner(expected_exit=2, extra_args=["--time-budget-seconds", "5"])
        self.assertEqual(result["pending"], ["ImbalancedChen.Page"])
        self.assertEqual(result["successful_closure"], 2)
        self.assertEqual(self.records()["ImbalancedChen.Mid"]["exit_code"], 0)
        self.assertTrue((self.cache / "lib/ImbalancedChen/Mid.olean").is_file())
        self.assertFalse((self.cache / "lib/ImbalancedChen/Page.olean").exists())


if __name__ == "__main__":
    unittest.main()
