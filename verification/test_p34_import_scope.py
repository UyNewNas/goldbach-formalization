"""Regression checks for valid Lean import syntax that evades line regexes."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
from verify_p34_cusp_normalization import ROOT, validate_import_paths


class ParsedImportScope(unittest.TestCase):
    def setUp(self):
        self.external = ((Path(os.environ["LEAN_SYSROOT"]) / "lib/lean").resolve(),)
        self.phase = (ROOT / ".lake/build/lib/lean/ImbalancedChen/Part3CuspPhaseCore.olean").resolve()
        self.gamma = (ROOT / ".lake/build/lib/lean/ImbalancedChen/Part3Gamma0ActualCusps.olean").resolve()

    def parsed(self, source):
        with tempfile.TemporaryDirectory(prefix="p34-import-test-", dir=ROOT / ".lake") as directory:
            path = Path(directory) / "Header.lean"
            path.write_text(source)
            return subprocess.check_output(["lean", "--deps", str(path)], cwd=ROOT, text=True)

    def test_indented_import_is_rejected_without_fresh_object(self):
        parsed = self.parsed(" import ImbalancedChen.Part3CuspPhaseCore\n")
        with self.assertRaisesRegex(RuntimeError, "not freshly rebuilt or locked"):
            validate_import_paths(parsed, set(), self.external)

    def test_second_same_line_import_is_rejected(self):
        parsed = self.parsed("import ImbalancedChen.Part3CuspPhaseCore "
                             "import ImbalancedChen.Part3Gamma0ActualCusps\n")
        with self.assertRaisesRegex(RuntimeError, "not freshly rebuilt or locked"):
            validate_import_paths(parsed, {self.phase}, self.external)

    def test_both_forms_accept_only_the_complete_fresh_set(self):
        parsed = self.parsed(" import ImbalancedChen.Part3CuspPhaseCore "
                             "import ImbalancedChen.Part3Gamma0ActualCusps\n")
        result = validate_import_paths(parsed, {self.phase, self.gamma}, self.external)
        self.assertIn(str(self.phase), result)
        self.assertIn(str(self.gamma), result)


if __name__ == "__main__":
    unittest.main()
