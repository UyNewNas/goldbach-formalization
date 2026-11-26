"""Offline round-7 provenance and incremental-scope regression checks."""
from pathlib import Path
import copy
import hashlib
import json
import shutil
import sys
import tempfile
import types
import unittest

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]


def load(path, name):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


class Round7Guards(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.prepare = load(PACKAGE / 'prepare_p2_round7.py', 'p25_prepare_test')
        cls.runner, cls.graph, cls.targets, cls.previous = cls.prepare.context()
        cls.prior_selection = json.loads((ROOT / cls.runner.ROUND6_SELECTION).read_bytes())
        # Descriptor-only fixtures exercise gate rejection, not Lean acceptance.
        rows = []
        for name in cls.runner.EXPECTED_REPAIRS:
            before = cls.graph['modules'][name]['sha256']
            rows.append({'module': name, 'source': name.replace('.', '/') + '.lean',
                         'before_sha256': before,
                         'after_sha256': hashlib.sha256((name + ':guard-test').encode()).hexdigest(),
                         'imports_unchanged': True, 'options_unchanged': True})
        cls.selection = {'changed_modules': rows,
                         'changed_audit_targets': [r['module'] for r in rows if r['module'] in cls.targets['modules']],
                         'changed_dependency_only_modules': [r['module'] for r in rows if r['module'] not in cls.targets['modules']]}

    def test_actual_prior_receipt_and_pins(self):
        self.assertEqual(self.prepare.digest(self.prepare.RECEIPT.read_bytes()), self.runner.PRIOR_RESULT_SHA)
        self.assertEqual(self.previous['source_commit'], self.runner.PREVIOUS)
        self.runner.validate_previous_result(self.previous, self.graph['roots'], self.targets['modules'], self.prior_selection)
        self.assertEqual(self.runner.MIN_FREE_BYTES, 1073741824)
        self.assertEqual(self.runner.PRIOR_OUT, '.lake/p25-followup-repairs-attempt006')
        self.assertEqual(self.runner.NEW_OUT, '.lake/p25-followup-repairs-attempt007')

    def test_four_repairs_preserve_377_modules_and_69_owned_targets(self):
        updated, ordered = self.runner.validated_graph(self.graph, self.targets, self.selection)
        changed = {name for name in updated['modules']
                   if updated['modules'][name]['sha256'] != self.graph['modules'][name]['sha256']}
        self.assertEqual(changed, set(self.runner.EXPECTED_REPAIRS))
        self.assertEqual(len(updated['modules']), 377)
        self.assertEqual(updated['roots'], self.graph['roots'])
        self.assertEqual(len(ordered), 69)
        self.assertEqual(set(ordered), set(self.targets['modules']))
        self.assertEqual(ordered[:1], self.selection['changed_audit_targets'])

    def test_failed_dependency_chain_contains_all_repairs_and_no_prior_passes(self):
        affected = set(self.prepare.affected_modules(self.graph, self.runner.EXPECTED_REPAIRS))
        self.assertEqual(affected, set(self.previous['compile_summary']['failed_or_blocked']))
        self.assertEqual(len(self.graph['modules']) - len(affected), 339)
        accepted = {name for name, row in self.previous['audit_summary']['modules'].items() if row['accepted']}
        self.assertEqual(len(accepted), 45)
        self.assertFalse(affected & accepted)
        self.assertEqual(len(set(self.targets['modules']) & affected), 24)

    def test_rejects_wrong_repair_identity_preimage_imports_or_options(self):
        for mutation in ['missing', 'duplicate', 'foreign', 'preimage', 'unchanged', 'imports', 'options']:
            bad = copy.deepcopy(self.selection)
            rows = bad['changed_modules']
            if mutation == 'missing':
                rows.pop()
            elif mutation == 'duplicate':
                rows[1] = copy.deepcopy(rows[0])
            elif mutation == 'foreign':
                rows[0]['module'] = 'ImbalancedChen.P4AOriginalFull87PrefixBinding'
            elif mutation == 'preimage':
                rows[0]['before_sha256'] = '0' * 64
            elif mutation == 'unchanged':
                rows[0]['after_sha256'] = rows[0]['before_sha256']
            else:
                rows[0][mutation + '_unchanged'] = False
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                self.runner.validated_graph(self.graph, self.targets, bad)

    def test_rejects_stale_or_incomplete_prior_receipt(self):
        for mutation in ['origin', 'normal', 'owned', 'pending', 'postflight', 'prior_source']:
            bad = copy.deepcopy(self.previous)
            if mutation == 'origin':
                bad['source_commit'] = '0' * 40
            elif mutation == 'normal':
                bad['compile_summary']['successful_closure'] = 330
            elif mutation == 'owned':
                bad['audit_summary']['accepted'] = 41
            elif mutation == 'pending':
                bad['compile_summary']['pending'] = ['ImbalancedChen.P4AOriginalFull87Ownership']
            elif mutation == 'postflight':
                bad['external_after_matches'] = False
            else:
                bad['changed_sources'][0]['after_sha256'] = '0' * 64
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                self.runner.validate_previous_result(bad, self.graph['roots'], self.targets['modules'], self.prior_selection)

    def test_incomplete_candidate_set_cannot_generate_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            package = Path(directory)
            with self.assertRaisesRegex(RuntimeError, 'Candidate pair is not complete'):
                self.prepare.build_selection(self.runner, self.graph, self.targets, self.previous, package=package)
            self.assertEqual(list(package.iterdir()), [])

    def test_original_option_commands_remain_bound(self):
        sys.path.insert(0, str(ROOT / 'verification/part2'))
        from inspect_winner9_owner_native import source_tokens
        source = 'ImbalancedChen/P4AOriginalFull87Ownership.lean'
        before = (PACKAGE / 'before' / source).read_text()
        after = (PACKAGE / 'after' / source).read_text()
        extract = lambda text: self.prepare.option_commands(source_tokens(text))
        self.assertEqual(extract(before), ['set_option maxHeartbeats 0 in'] * 3)
        self.assertEqual(extract(before), extract(after))
        selection = self.prepare.build_selection(self.runner, self.graph, self.targets, self.previous)
        self.assertEqual(len(selection['changed_modules']), 4)
        self.assertTrue(all(row['options_unchanged'] for row in selection['changed_modules']))

    def test_actual_option_value_change_is_still_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            package = Path(directory)
            shutil.copytree(PACKAGE / 'before', package / 'before')
            shutil.copytree(PACKAGE / 'after', package / 'after')
            candidate = package / 'after/ImbalancedChen/P4AOriginalFull87Ownership.lean'
            text = candidate.read_text()
            self.assertIn('set_option maxHeartbeats 0 in', text)
            candidate.write_text(text.replace('set_option maxHeartbeats 0 in',
                                              'set_option maxHeartbeats 1 in', 1))
            with self.assertRaisesRegex(RuntimeError, 'Candidate options changed'):
                self.prepare.build_selection(self.runner, self.graph, self.targets, self.previous, package=package)


if __name__ == '__main__':
    unittest.main()
