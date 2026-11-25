"""Compiler-free donor reuse tests with real temporary files and Git source bytes."""
from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import p24_prepare_diagnostic_donor as prepare

SCRIPTS = Path(__file__).resolve().parent
STATUS = "DIAGNOSTIC_ONLY_NOT_PROOF_ACCEPTANCE"


def record(path):
    raw = path.read_bytes()
    return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}


def put(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(raw)
    return path


def write_json(path, obj):
    put(path, (json.dumps(obj, indent=2) + "\n").encode())


class Fixture:
    def __init__(self, directory, distinct_external=False):
        self.tmp = Path(directory)
        self.root = self.tmp / "project"
        self.donor = self.tmp / "base-donor"
        self.previous = self.tmp / "previous-diagnostic"
        self.out = self.root / "private-donor"
        self.toolchain = self.tmp / "toolchain"
        self.base = put(self.root / "ImbalancedChen/Base.lean", b"def base : Nat := 1\n")
        self.passed = put(self.root / "ImbalancedChen/Pass.lean",
                          b"import ImbalancedChen.Base\nimport Mathlib.MockExternal\ndef passed : Nat := base\n")
        for source in (self.base, self.passed):
            put(self.donor / source.relative_to(self.root), source.read_bytes())
        self.base_object = put(self.donor / ".lake/build/lib/lean/ImbalancedChen/Base.olean", b"BASE-object")
        self.old_base_object = put(self.previous / "lib/ImbalancedChen/Base.olean", b"BASE-object")
        self.pass_object = put(self.previous / "lib/ImbalancedChen/Pass.olean", b"fresh-PASS-object")
        self.pass_server = put(self.previous / "lib/ImbalancedChen/Pass.olean.server", b"fresh-PASS-server")
        self.current_external = put(self.donor / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/MockExternal.olean",
                                    b"external-B" if distinct_external else b"external-A")
        old_donor = self.tmp / "old-donor" if distinct_external else self.donor
        self.old_external = put(old_donor / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib/MockExternal.olean", b"external-A")
        external_source = put(old_donor / ".lake/packages/mathlib/Mathlib/MockExternal.lean", b"prelude\ndef external : Nat := 1\n")
        self.lean = put(self.toolchain / "bin/lean", b"fixture compiler bytes: never executed")
        lib_lean = put(self.toolchain / "lib/libLean.so", b"fixture runtime bytes")
        init_object = put(self.toolchain / "lib/lean/Init.olean", b"fixture Init object")
        init_source = put(self.toolchain / "src/lean/Init.lean", b"prelude\n")
        inputs = {str(p): record(p) for p in (self.base, self.passed, self.old_base_object, self.old_external)}
        self.row = {"status": STATUS, "exit_code": 0, "compiler_exit_code": 0,
                    "source_sha256": record(self.passed)["sha256"], "inputs_unchanged": True,
                    "inputs_before": inputs, "inputs_after": inputs,
                    "project_dependency_modules": ["ImbalancedChen.Base"],
                    "output_facets": {str(p): record(p) for p in (self.pass_object, self.pass_server)},
                    "compile_credit": False, "kernel_credit": False}
        write_json(self.previous / "RECORDS.json", {"ImbalancedChen.Pass": self.row})
        write_json(self.previous / "SUMMARY.json", {"status": STATUS, "current_inputs_stable": True,
                   "compile_credit": False, "kernel_credit": False})
        external_files = {str(p): record(p) for p in (self.old_external, external_source, self.lean, lib_lean, init_object, init_source)}
        external_modules = {
            "Mathlib.MockExternal": {"object": str(self.old_external), "source": str(external_source)},
            "Init": {"object": str(init_object), "source": str(init_source)},
        }
        write_json(self.previous / "EXTERNAL_INPUTS_BEFORE.json", {"status": STATUS, "files": external_files,
                   "modules": external_modules})
        write_json(self.previous / "EXTERNAL_INPUTS_AFTER.json", {"status": STATUS, "files": external_files,
                   "equal_to_before": True})
        self.runtime = {"status": STATUS, "lean": str(self.lean), "lean_sha256": record(self.lean)["sha256"],
                        "lean_sysroot": str(self.toolchain), "version": "fixture only",
                        "mathlib_commit": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
                        "script_sha256": hashlib.sha256((SCRIPTS / "p24_diagnostic_compile.py").read_bytes()).hexdigest(),
                        "lean_path": os.pathsep.join(map(str, [self.previous / "lib",
                            old_donor / ".lake/packages/mathlib/.lake/build/lib/lean", self.toolchain / "lib/lean"]))}
        write_json(self.previous / "RUNTIME.json", self.runtime)
        commands = (["git", "init", "-q"], ["git", "add", "ImbalancedChen"],
                    ["git", "-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "fixture sources"])
        for command in commands:
            subprocess.run(command, cwd=self.root, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        self.commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=self.root, text=True).strip()

    def run(self, fail_second_output_copy=False):
        argv = ["prepare", "ImbalancedChen.Pass", "--project-root", str(self.root), "--donor-root", str(self.donor),
                "--previous-output", str(self.previous), "--source-commit", self.commit, "--out", str(self.out)]
        original_copy = prepare.shutil.copyfile

        def copying(source, target, *args, **kwargs):
            if fail_second_output_copy and Path(source) == self.pass_server:
                raise OSError("injected second output copy failure")
            return original_copy(source, target, *args, **kwargs)

        # All file IO remains real; only a specific IO failure is injected.
        with patch.object(sys, "argv", argv), patch.object(prepare.shutil, "copyfile", copying), contextlib.redirect_stdout(io.StringIO()):
            prepare.main()
        return json.loads((self.out / "DIAGNOSTIC_DONOR.json").read_text())

    def consumer_plan(self, toolchain=None):
        return subprocess.run([sys.executable, "-B", str(SCRIPTS / "p24_diagnostic_compile.py"), "ImbalancedChen.Pass",
                               "--project-root", str(self.root), "--donor-root", str(self.out),
                               "--toolchain-root", str(toolchain or self.toolchain), "--plan-only"],
                              text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


class DiagnosticDonorTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="p24-diagnostic-donor-test-")
        self.addCleanup(self.directory.cleanup)
        self.fixture = Fixture(self.directory.name)

    def assert_skipped(self, receipt):
        self.assertEqual(receipt["earlier_diagnostic_outputs_reused"], {})
        self.assertIn("ImbalancedChen.Pass", receipt["earlier_outputs_not_reused"])
        self.assertFalse(receipt["proof_acceptance"])
        self.assertFalse(receipt["compile_credit"])
        self.assertFalse(receipt["kernel_credit"])

    def test_exact_previous_pass_and_dependencies_are_reused_without_credit(self):
        f = self.fixture
        receipt = f.run()
        self.assertEqual(sorted(receipt["earlier_diagnostic_outputs_reused"]), ["ImbalancedChen.Pass"])
        self.assertEqual((f.out / ".lake/build/lib/lean/ImbalancedChen/Pass.olean").read_bytes(), b"fresh-PASS-object")
        self.assertEqual((f.out / ".lake/build/lib/lean/ImbalancedChen/Pass.olean.server").read_bytes(), b"fresh-PASS-server")
        for key in ("proof_acceptance", "compile_credit", "kernel_credit"):
            self.assertFalse(receipt[key])
        plan = f.consumer_plan()
        self.assertEqual(plan.returncode, 0, plan.stderr)
        self.assertEqual(json.loads(plan.stdout)["source_import_ancestor_matched_diagnostic_candidates"],
                         ["ImbalancedChen.Base", "ImbalancedChen.Pass"])

    def test_changed_current_source_skips_previous_pass(self):
        f = self.fixture
        f.passed.write_bytes(f.passed.read_bytes() + b"-- changed source\n")
        self.assert_skipped(f.run())

    def test_changed_current_project_object_skips_previous_pass(self):
        f = self.fixture
        f.base_object.write_bytes(b"different-BASE-object")
        self.assert_skipped(f.run())

    def test_additional_project_facet_skips_previous_pass(self):
        f = self.fixture
        put(f.donor / ".lake/build/lib/lean/ImbalancedChen/Base.ir", b"new-IR")
        self.assert_skipped(f.run())

    def test_changed_original_output_skips_previous_pass(self):
        f = self.fixture
        f.pass_object.write_bytes(b"changed-output")
        self.assert_skipped(f.run())

    def test_changed_original_external_input_cannot_publish_reusable_donor(self):
        f = self.fixture
        f.old_external.write_bytes(b"changed-external")
        with self.assertRaises((ValueError, RuntimeError)):
            f.run()
        self.assertFalse((f.out / "DIAGNOSTIC_DONOR.json").exists())

    def test_different_new_external_tree_rejects_unchanged_old_snapshot(self):
        with tempfile.TemporaryDirectory(prefix="p24-diagnostic-donor-tree-") as directory:
            f = Fixture(directory, distinct_external=True)
            self.assertNotEqual(f.old_external.read_bytes(), f.current_external.read_bytes())
            with self.assertRaises((ValueError, RuntimeError)):
                f.run()
            self.assertFalse((f.out / "DIAGNOSTIC_DONOR.json").exists())

    def test_failed_second_output_copy_is_rejected_before_consumer_plan(self):
        f = self.fixture
        with self.assertRaisesRegex(OSError, "injected second output copy failure"):
            f.run(fail_second_output_copy=True)
        self.assertFalse((f.out / "DIAGNOSTIC_DONOR.json").exists())
        self.assertTrue((f.out / ".lake/build/lib/lean/ImbalancedChen/Pass.olean").exists())
        plan = f.consumer_plan()
        self.assertNotEqual(plan.returncode, 0, plan.stdout)
        self.assertIn("incomplete", plan.stderr.lower())

    def test_added_external_loadable_facet_cannot_hide_behind_old_file_hashes(self):
        f = self.fixture
        put(Path(str(f.old_external) + ".private"), b"unrecorded-private-facet")
        with self.assertRaises((ValueError, RuntimeError)):
            f.run()
        self.assertFalse((f.out / "DIAGNOSTIC_DONOR.json").exists())

    def test_consumer_rejects_different_toolchain_before_plan(self):
        f = self.fixture
        f.run()
        other = f.tmp / "other-toolchain"
        put(other / "bin/lean", f.lean.read_bytes())
        (other / "lib/lean").mkdir(parents=True)
        plan = f.consumer_plan(toolchain=other)
        self.assertNotEqual(plan.returncode, 0, plan.stdout)
        self.assertIn("toolchain", plan.stderr.lower())


if __name__ == "__main__":
    unittest.main()
