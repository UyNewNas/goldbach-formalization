"""Regression cases for source/import snapshots used by the P2 proof gate."""
from pathlib import Path
import unittest

from inspect_winner9_owner_native import imports, source_tokens


class SourceImportsTests(unittest.TestCase):
    def test_original_pure_json_reader(self):
        root = Path(__file__).resolve().parents[2]
        source = root / "ImbalancedChen/P2OriginalSaving19SourceJson.lean"
        self.assertEqual(imports(source.read_text()), ["Lean"])

    def test_character_quotes_do_not_open_strings(self):
        source = "import Lean\ndef quote : Char := '\"'\nimport Std\n"
        self.assertEqual(imports(source), ["Lean", "Std"])
        self.assertEqual(source_tokens(source).count("\n"), source.count("\n"))

    def test_escaped_characters_and_identifier_primes(self):
        source = r'''import Lean
def slash : Char := '\\'
def quote : Char := '\''
def newline : Char := '\n'
def f' (x : Nat) := x
#check f' 'a'
import Std
'''
        self.assertEqual(imports(source), ["Lean", "Std"])

    def test_comments_and_strings_cannot_add_imports(self):
        source = '''/- nested /- import Hidden.One -/ comment -/
import Lean
def text := "import Hidden.Two\nimport Hidden.Three"
-- import Hidden.Four
private meta import Std
'''
        self.assertEqual(imports(source), ["Lean", "Std"])

    def test_unterminated_comments_and_strings_still_fail(self):
        for source in ['import Lean\n/- unfinished', 'import Lean\ndef x := "unfinished']:
            with self.subTest(source=source), self.assertRaises(ValueError):
                imports(source)


if __name__ == "__main__":
    unittest.main()
