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
    @classmethod
    def setUpClass(cls):
        cls.external = ((Path(os.environ["LEAN_SYSROOT"]) / "lib/lean").resolve(),)
        storage = ROOT / ".lake"
        storage.mkdir(exist_ok=True)
        fixture = tempfile.TemporaryDirectory(prefix="p34-import-test-", dir=storage)
        cls.addClassCleanup(fixture.cleanup)
        cls.directory = Path(fixture.name).resolve()
        # Replace Lake's search path so the fixtures cannot find project objects.
        cls.env = dict(os.environ, LEAN_PATH=str(cls.directory))
        cls.first = cls.directory / "P34ImportFirst.olean"
        cls.second = cls.directory / "P34ImportSecond.olean"
        for object_path in (cls.first, cls.second):
            source = object_path.with_suffix(".lean")
            source.write_text(f"def {source.stem.lower()} : Nat := 1\n")
            subprocess.run(
                ["lean", "-DwarningAsError=true", "-o", object_path.name, source.name],
                cwd=cls.directory, env=cls.env, check=True)

    def parsed(self, source):
        path = self.directory / "Header.lean"
        path.write_text(source)
        return subprocess.check_output(
            ["lean", "--deps", path.name], cwd=self.directory, env=self.env, text=True)

    def test_indented_import_is_rejected_without_fresh_object(self):
        parsed = self.parsed(" import P34ImportFirst\n")
        with self.assertRaises(RuntimeError) as error:
            validate_import_paths(parsed, set(), self.external)
        self.assertEqual(str(error.exception),
                         "Dependency was not freshly rebuilt or locked: " + str(self.first))

    def test_second_same_line_import_is_rejected(self):
        parsed = self.parsed("import P34ImportFirst import P34ImportSecond\n")
        with self.assertRaises(RuntimeError) as error:
            validate_import_paths(parsed, {self.first}, self.external)
        self.assertEqual(str(error.exception),
                         "Dependency was not freshly rebuilt or locked: " + str(self.second))

    def test_both_forms_accept_only_the_complete_fresh_set(self):
        parsed = self.parsed(" import P34ImportFirst import P34ImportSecond\n")
        result = validate_import_paths(parsed, {self.first, self.second}, self.external)
        self.assertIn(str(self.first), result)
        self.assertIn(str(self.second), result)


if __name__ == "__main__":
    unittest.main()
