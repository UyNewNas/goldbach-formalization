"""Exercise the audit driver with fixture executables, never claiming Lean credit."""
from __future__ import annotations

import contextlib
import importlib.util
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

import test_private_cache_binding as cache_tests


DRIVER = Path(__file__).with_name("run_winner9_private_audit.py")
MODULE = "ImbalancedChen.Page"


class PrivateAuditTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = cache_tests.ProofCacheBindingTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        compiler = Path(self.fixture.runner.LEAN)
        text = compiler.read_text()
        insertion = """
if 'audit' in source.parts:
    import re
    target = re.search(r'let moduleName := `([^\\s]+)', source.read_text()).group(1)
    fixture = pathlib.Path('audit-fixture-' + target + '.log')
    print((fixture if fixture.exists() else pathlib.Path('audit-fixture.log')).read_text())
    mutation = pathlib.Path('mutate-during-audit')
    if mutation.exists():
        pathlib.Path(mutation.read_text()).write_bytes(b'changed during audit')
    raise SystemExit(0)
"""
        # Audit invocations do not request an output .olean.
        text = text.replace("obj = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])\n", "")
        text = text.replace("source = pathlib.Path(sys.argv[-1])\n",
                            "source = pathlib.Path(sys.argv[-1])\n" + insertion +
                            "obj = pathlib.Path(sys.argv[sys.argv.index('-o') + 1])\n")
        compiler.write_text(text)
        self.fixture.run_runner()
        self.checker = self.fixture.base / "leanchecker-fixture"
        self.checker.write_text("""#!/usr/bin/env python3
import pathlib, sys
print('fixture replay', sys.argv[-1])
raise SystemExit(1 if pathlib.Path('fail-replay').exists() else 0)
""")
        self.checker.chmod(0o755)
        self.names = ["ImbalancedChen.Page.first", "_private.ImbalancedChen.Page.0.second"]
        self.declarations = [{"name": name, "module": MODULE, "unsafe": False,
                              "partial": False, "axiom": False, "type": "Eq Nat Nat.zero Nat.zero",
                              "axioms": ["propext"]} for name in self.names]
        self.write_audit()

    def write_audit(self) -> None:
        lines = ["P0_QUEUE_IMPORTS " + json.dumps(["ImbalancedChen.Dep", "ImbalancedChen.Mid", MODULE]),
                 "P0_QUEUE_INVENTORY " + json.dumps({"module": MODULE, "serialized": self.names,
                                                      "environment": self.names})]
        lines += ["P0_QUEUE_DECL " + json.dumps(record) for record in self.declarations]
        (self.root / "audit-fixture.log").write_text("\n".join(lines) + "\n")

    def run_audit(self, expected_exit: int = 0, extra_args: list[str] | None = None) -> dict:
        self.assertTrue(DRIVER.is_file(), "The audit driver is not implemented")
        spec = importlib.util.spec_from_file_location("winner9_audit_test", DRIVER)
        driver = importlib.util.module_from_spec(spec)
        assert spec.loader is not None
        spec.loader.exec_module(driver)
        driver.LEAN = self.fixture.runner.LEAN
        driver.LEANCHECKER = str(self.checker)
        driver.MATHLIB = self.fixture.runner.MATHLIB
        driver.PIN = self.fixture.runner.PIN
        previous_dir, previous_args = Path.cwd(), sys.argv
        try:
            os.chdir(self.root)
            sys.argv = [str(DRIVER), MODULE]
            sys.argv.extend(extra_args or [])
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                result = driver.main()
            self.assertEqual(result, expected_exit, output.getvalue())
            path = self.root / ".lake/p2-private/audit" / MODULE / "latest.json"
            return json.loads(path.read_text())
        finally:
            os.chdir(previous_dir)
            sys.argv = previous_args

    def test_complete_owned_inventory_and_replay_are_both_required(self) -> None:
        receipt = self.run_audit()
        self.assertTrue(receipt["accepted"])
        self.assertEqual(receipt["replay"]["exit_code"], 0)
        self.assertEqual(receipt["audit"]["declaration_count"], 2)
        self.assertEqual(receipt["audit"]["axiom_counts"], {"propext": 2})

    def test_another_modules_declaration_is_rejected(self) -> None:
        self.declarations[1]["module"] = "ImbalancedChen.Dep"
        self.write_audit()
        self.assertFalse(self.run_audit(expected_exit=1)["accepted"])

    def test_missing_owned_declaration_is_rejected(self) -> None:
        self.declarations.pop()
        self.write_audit()
        self.assertFalse(self.run_audit(expected_exit=1)["accepted"])

    def test_forbidden_transitive_axiom_is_rejected(self) -> None:
        self.declarations[0]["axioms"] = ["sorryAx"]
        self.write_audit()
        self.assertFalse(self.run_audit(expected_exit=1)["accepted"])

    def test_unsafe_partial_and_axiom_flags_are_each_rejected(self) -> None:
        for flag in ("unsafe", "partial", "axiom"):
            with self.subTest(flag=flag):
                self.declarations[0][flag] = True
                self.write_audit()
                self.assertFalse(self.run_audit(expected_exit=1)["accepted"])
                self.declarations[0][flag] = False

    def test_failed_replay_never_becomes_audit_acceptance(self) -> None:
        (self.root / "fail-replay").touch()
        receipt = self.run_audit(expected_exit=1)
        self.assertFalse(receipt["accepted"])
        self.assertEqual(receipt["replay"]["exit_code"], 1)
        self.assertNotIn("audit", receipt)

    def test_source_change_during_audit_rejects_successful_processes(self) -> None:
        (self.root / "mutate-during-audit").write_text("ImbalancedChen/Dep.lean")
        receipt = self.run_audit(expected_exit=1)
        self.assertFalse(receipt["accepted"])
        self.assertEqual(receipt["replay"]["exit_code"], 0)
        self.assertEqual(receipt["audit"]["exit_code"], 0)

    def test_verified_receipt_is_reused_without_duplicate_replay(self) -> None:
        first = self.run_audit()
        (self.root / "fail-replay").touch()
        second = self.run_audit()
        self.assertTrue(second["accepted"])
        self.assertEqual(second["replay"]["log"], first["replay"]["log"])

    def launcher(self) -> list[str]:
        code = f"""
import sys
sys.path.insert(0, {str(DRIVER.parent)!r})
import run_winner9_private_audit as driver
driver.LEAN = {self.fixture.runner.LEAN!r}
driver.LEANCHECKER = {str(self.checker)!r}
driver.MATHLIB = {self.fixture.runner.MATHLIB!r}
driver.PIN = {self.fixture.runner.PIN!r}
raise SystemExit(driver.main())
"""
        return [sys.executable, "-c", code]

    def test_disjoint_workers_preserve_separate_summaries(self) -> None:
        module = "ImbalancedChen.Mid"
        name = module + ".first"
        lines = ["P0_QUEUE_IMPORTS " + json.dumps(["ImbalancedChen.Dep", module]),
                 "P0_QUEUE_INVENTORY " + json.dumps({"module": module, "serialized": [name], "environment": [name]}),
                 "P0_QUEUE_DECL " + json.dumps(dict(self.declarations[0], name=name, module=module))]
        (self.root / ("audit-fixture-" + module + ".log")).write_text("\n".join(lines) + "\n")
        processes = [subprocess.Popen(self.launcher() + [target, "--summary-name", summary],
                                      cwd=self.root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                     for target, summary in ((MODULE, "worker-a.json"), (module, "worker-b.json"))]
        outcomes = [(process, process.communicate()[0]) for process in processes]
        for process, output in outcomes:
            self.assertEqual(process.returncode, 0, output)
        audit_root = self.root / ".lake/p2-private/audit"
        for target, summary in ((MODULE, "worker-a.json"), (module, "worker-b.json")):
            result = json.loads((audit_root / summary).read_text())
            self.assertTrue(result["all_accepted"])
            self.assertEqual(list(result["modules"]), [target])
        self.assertFalse((audit_root / "summary.json").exists())

    def test_summary_name_cannot_escape_audit_directory(self) -> None:
        result = subprocess.run(self.launcher() + [MODULE, "--summary-name", "../../escaped.json"],
                                cwd=self.root, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.root / ".lake/escaped.json").exists())


if __name__ == "__main__":
    unittest.main()
