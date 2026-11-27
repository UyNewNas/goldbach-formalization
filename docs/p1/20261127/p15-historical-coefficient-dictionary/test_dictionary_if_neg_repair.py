"""New proof-delta and original-failure bindings only; no Lean or old tests."""
from pathlib import Path
from types import SimpleNamespace
import copy
import importlib.util
import json
import os
import unittest
from unittest.mock import Mock, patch

HERE = Path(__file__).resolve().parent
def load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module
p = load('dictionary_if_neg_probe_under_review', 'probe_dictionary.py')
s = load('dictionary_if_neg_stager_under_review', 'stage_dictionary.py')


class DictionaryIfNegRepair(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = Path(os.environ.get('P15_ORIGINAL_DICTIONARY',
            str(HERE.parent / 'new/P1OriginalHistoricalCoefficientDictionary.lean'))).read_bytes()
        cls.repaired = (HERE / 'P1OriginalHistoricalCoefficientDictionary.lean').read_bytes()
        cls.failed_raw = Path(os.environ.get('P15_FAILED_DICTIONARY_RESULT',
            '/tmp/p15-r5-root/AM_FAILED_DICTIONARY_RESULT.json')).read_bytes()
        if p.raw_fp(cls.failed_raw) != p.FAILED_PROBE_FP:
            raise RuntimeError('actual AM failed result fixture differs')
        cls.failed = json.loads(cls.failed_raw)

    def context(self, row=None, fingerprint=None):
        tree = Mock(return_value={'original_AM_file': {'bytes': 1, 'sha256': '0' * 64}})
        c = SimpleNamespace(g=SimpleNamespace(regular_fingerprint=lambda helpers, path: fingerprint or p.FAILED_PROBE_FP),
            ag=SimpleNamespace(api=SimpleNamespace(read_json=lambda path: row or self.failed)),
            readers={'ag': SimpleNamespace(tree_inventory=tree)})
        return c, tree

    def test_exact_28_byte_proof_delta_and_all_other_bytes_unchanged(self):
        p.require_corrected_source(self.original, self.repaired)
        s.require_corrected_source(self.original, self.repaired)
        old = b'    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient]\n'
        new = b'    simp [roughMaskDelta, attachedMobius, hnew, hold, signAttachedCoefficient] <;>\n      split_ifs <;> rfl\n'
        self.assertEqual(len(self.repaired) - len(self.original), 28)
        self.assertEqual(self.repaired.replace(new, old), self.original)
        self.assertEqual(self.original.count(old), 1)

    def test_statement_or_selector_change_is_rejected(self):
        for changed in (self.repaired.replace(b'{a b :', b'{a c :', 1),
                        self.repaired.replace(b'signAttachedCoefficient', b'otherCoefficient', 1)):
            with self.assertRaisesRegex(RuntimeError, 'exact proof-only'):
                p.require_corrected_source(self.original, changed)

    def test_actual_AM_failed_result_and_entire_AM_tree_are_bound(self):
        c, tree = self.context()
        result = p.failed_probe_snapshot(c, self.failed['scope'])
        self.assertEqual(result['compiler_job'], 'job_b852fda8ce794982b7938d5f29b5a9a8')
        self.assertEqual(result['result']['sha256'], p.FAILED_PROBE_FP['sha256'])
        tree.assert_called_once_with(p.PROBE_ROOT / p.AM)

    def test_failed_result_cannot_be_relabelled_success_or_another_source(self):
        for key, value in [('exit_code', 0), ('probe_passed', True), ('preservation_passed', False),
                           ('original_dependency_acceptance_preparation_completed', False)]:
            row = copy.deepcopy(self.failed); row[key] = value
            c, tree = self.context(row=row)
            with self.subTest(key=key), self.assertRaisesRegex(RuntimeError, 'original AM failure'):
                p.failed_probe_snapshot(c, self.failed['scope'])
            tree.assert_not_called()
        row = copy.deepcopy(self.failed); row['source_origin']['sha256'] = p.SOURCE_FP['sha256']
        c, _ = self.context(row=row)
        with self.assertRaisesRegex(RuntimeError, 'original AM failure'):
            p.failed_probe_snapshot(c, self.failed['scope'])

    def test_original_failed_bytes_are_required_even_for_matching_parsed_fields(self):
        c, tree = self.context(fingerprint={'bytes': 88801, 'sha256': 'f' * 64})
        with self.assertRaisesRegex(RuntimeError, 'result differs'):
            p.failed_probe_snapshot(c, self.failed['scope'])
        tree.assert_not_called()

    def test_full_failed_tree_changes_are_visible_to_before_after_equality(self):
        c, tree = self.context()
        before = p.failed_probe_snapshot(c, self.failed['scope'])
        tree.return_value = {'original_AM_file': {'bytes': 2, 'sha256': '1' * 64}}
        after = p.failed_probe_snapshot(c, self.failed['scope'])
        self.assertNotEqual(before, after)

    def test_stager_pins_repaired_source_and_new_probe(self):
        self.assertEqual(s.SCRIPT_FP, s.fp((HERE / 'probe_dictionary.py').read_bytes()))
        self.assertEqual(s.SOURCE_FP, p.SOURCE_FP)
        self.assertEqual(s.ORIGINAL_SOURCE_FP, p.ORIGINAL_SOURCE_FP)
        self.assertEqual(s.ORIGINAL_ORIGIN, p.ORIGINAL_ORIGIN)
        self.assertEqual(s.ORIGIN, p.ORIGIN)


if __name__ == '__main__':
    unittest.main(verbosity=2)
