#!/usr/bin/env python3
"""Actual full-inventory regression for optional original P3 source locators."""
from pathlib import Path
import ast
import json
import sys
import unittest

sys.dont_write_bytecode = True
import join_common as C
import prepare_family_p3 as P

HERE = Path(__file__).absolute().parent
INVENTORY = HERE.parent / 'supplier-join-20261126'
F = C.load_executor(HERE.parent / 'cell01-family-run-20261126/releases/p3-v2/family_run.py')
PRESENT = json.loads(C.checked_local(INVENTORY / 'P3_PRESENT_FINAL.json', C.expected('P3_present')))['suppliers']
MISSING = json.loads(C.checked_local(INVENTORY / 'P3_MISSING_FINAL.json', C.expected('P3_missing')))['missing']


def current_inventory_protection(present, missing):
    # Evaluate only the two actual production root-collection expressions.
    # This avoids any stage creation, installer call, cloud access or old-chain replay.
    main = next(node for node in ast.parse(Path(P.__file__).read_text()).body
                if isinstance(node, ast.FunctionDef) and node.name == 'main')
    expressions = [node.value for node in main.body if isinstance(node, ast.AugAssign)
                   and isinstance(node.target, ast.Name) and node.target.id == 'protected'
                   and any(isinstance(n, ast.Name) and n.id in {'present_prior', 'missing_prior'}
                           for n in ast.walk(node.value))]
    if len(expressions) != 2:
        raise RuntimeError('Expected both original inventory protection expressions')
    scope = {'Path': Path, 'F': F, 'present_prior': present, 'missing_prior': missing}
    return [path for expression in expressions
            for path in eval(compile(ast.Expression(expression), '<actual-inventory-protection>', 'eval'), scope)]


class NullableInventoryTests(unittest.TestCase):
    def test_all602_present_and189_missing_records_protect_every_real_provider(self):
        self.assertEqual((len(PRESENT), len(MISSING)), (602, 189))
        self.assertEqual(sum(row.get('p3_exact_source') is not None for row in MISSING), 166)
        self.assertEqual(sum('p3_exact_source' in row and row['p3_exact_source'] is None for row in MISSING), 12)
        self.assertEqual(sum('p3_exact_source' not in row for row in MISSING), 11)
        try:
            actual = current_inventory_protection(PRESENT, MISSING)
        except TypeError as error:
            self.fail('Complete immutable inventory cannot collect protected roots: ' + str(error))
        expected = [Path(row[role]['path']).parent for row in PRESENT for role in ('source', 'object')]
        expected += [Path(row['p3_exact_source']['path']).parent for row in MISSING
                     if isinstance(row.get('p3_exact_source'), dict)]
        self.assertEqual(len(actual), 1370)
        self.assertEqual(actual, expected)

    def test_null_locator_cannot_return_an_unavailable_source_as_a_provider(self):
        with self.assertRaisesRegex(RuntimeError, 'explicit already-inventoried P3 source locator'):
            P.missing_source(F, 'ImbalancedChen.Uninventoried', {'source_body_included': False},
                             {'p3_exact_source': None, 'source_missing': False}, Path('/unused-capsule'))

    def test_malformed_nonnull_locator_is_rejected_at_both_read_sites(self):
        value = {'p3_exact_source': {'bytes': 1, 'sha256': '0' * 64}, 'source_missing': False}
        with self.assertRaises(RuntimeError):
            P.missing_source(F, 'ImbalancedChen.Uninventoried', {'source_body_included': False},
                             value, Path('/unused-capsule'))
        with self.assertRaises(RuntimeError):
            current_inventory_protection([], [value])

    def test_all175_existing_source_locators_preserve_original_selected_identity(self):
        request = json.loads((INVENTORY / 'P1_CAPSULE_REQUEST_v2.json').read_text())
        requested = {row['module']: row for row in request['items']}
        existing, fallback = 0, 0
        for row in MISSING:
            item = requested[row['module']]
            if item['include_source_body']:
                continue
            selected = P.missing_source(F, row['module'],
                                        {'source_body_included': False, 'source': item['source']},
                                        row, Path('/unused-capsule'))
            self.assertTrue(F.same(selected, item['source']))
            if row.get('p3_exact_source') is not None:
                existing += 1
                self.assertEqual(selected, row['p3_exact_source'])
            else:
                fallback += 1
                self.assertIn(row['module'], {'ImbalancedChen.P2OriginalSaving19Cell01Row%03dFinite' % n
                                             for n in range(98, 107)})
                self.assertTrue(Path(selected['path']).is_relative_to(C.OLD / 'cell01-rest-finite-v2/project'))
        self.assertEqual((existing, fallback), (166, 9))


if __name__ == '__main__':
    unittest.main()
