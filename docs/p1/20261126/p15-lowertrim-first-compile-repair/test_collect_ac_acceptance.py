#!/usr/bin/env python3
"""Minimal local checks against frozen actual AC RESULT/WORKER scopes.

No environment collection, cloud call, Lean execution, or old proof test is run.
"""
from pathlib import Path
from types import ModuleType
import copy
import json
import sys
import unittest

sys.dont_write_bytecode = True
BASE = Path('/tmp/p15-ac-actual')
path = BASE / 'collect_ac_acceptance.py'
c = ModuleType('fixed_AC_collector_local_tests')
c.__file__ = str(path)
exec(compile(path.read_bytes(), str(path), 'exec'), c.__dict__)
LOWERTRIM = 'ImbalancedChen.P5OriginalSingletonLowerTrimPaid'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
rows = []
for index in (0, 1):
    raw = (BASE / ('attempt-%05d-RESULT.json' % index)).read_bytes()
    result = json.loads(raw)
    worker = {k: v for k, v in result.items()
              if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    worker_raw = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
    rows.append((result, worker, raw, worker_raw))


class FixedACTests(unittest.TestCase):
    def test_both_actual_result_worker_byte_pins(self):
        meta = json.loads((BASE / 'ACTUAL_AC_METADATA.json').read_bytes())
        for index, (_, _, raw, worker_raw) in enumerate(rows):
            pins = c.PINNED['runs'][index]['pins']
            self.assertEqual(c.raw_fp(raw), pins['RESULT.json'])
            self.assertEqual(c.raw_fp(worker_raw), pins['WORKER_RESULT.json'])
            self.assertEqual(pins, {name: c.pin(row) for name, row in
                meta['runs']['attempt-%05d' % index].items()})

    def test_actual_first_and_later_scope_status(self):
        self.assertTrue(c.validate_scope(rows[0][0], rows[0][1], c.PINNED['runs'][0]['scope']))
        self.assertFalse(c.validate_scope(rows[1][0], rows[1][1], c.PINNED['runs'][1]['scope']))
        self.assertEqual(rows[1][0]['targets'][1], LOWERTRIM)
        self.assertEqual(len(rows[1][0]['targets'][2:]), 3)
        self.assertEqual(list(rows[1][0]['failures']), [LOWERTRIM])
        self.assertNotIn('final_stock_readiness', rows[1][0])
        self.assertEqual(len(rows[1][0]['original_supplier_acceptance_bindings']), 26)
        self.assertIn(MEAN, rows[1][0]['original_supplier_acceptance_bindings'])
        self.assertEqual(set(rows[0][0]['original_supplier_acceptance_bindings']), {ENDPOINT, MEAN})

    def test_synthesis_accepting_run_and_same_AC_reuse(self):
        runs = [(row[0], {}, {}) for row in rows]
        self.assertEqual(c.accepting_runs(runs), {c.SYNTHESIS: 0})
        self.assertEqual(rows[0][0]['acceptance_bindings'][c.SYNTHESIS],
                         rows[1][0]['acceptance_bindings'][c.SYNTHESIS])
        binding = rows[0][0]['acceptance_bindings'][c.SYNTHESIS]
        self.assertEqual(len(binding['source_plus_five_outputs']), 6)
        self.assertEqual(len(binding['all_observed_target_artifacts']), 21)

    def test_actual_28_counts_112_111_and_failed_lowertrim_21_slots(self):
        meta = json.loads((BASE / 'ACTUAL_AC_METADATA.json').read_bytes())
        owner = c.PINNED['owners'][c.SYNTHESIS]
        self.assertEqual((owner['owned_count'], owner['public_count']), (28, 28))
        self.assertEqual(owner['source'], c.pin(meta['accepted_owners'][c.SYNTHESIS]['source']))
        self.assertEqual(owner['audit_result'], c.pin(meta['accepted_owners'][c.SYNTHESIS]['audit_result']))
        self.assertEqual(owner['owner_live_source_closure_count'], 112)
        self.assertEqual((c.PINNED['current_read_live_source_count'],
                          c.PINNED['current_read_preserved_dependency_count']), (112, 111))
        self.assertEqual(set(c.PINNED['failed_artifact_observations']), {LOWERTRIM})
        slots = c.PINNED['failed_artifact_observations'][LOWERTRIM]
        self.assertEqual(len(slots), 21)
        self.assertEqual([p for p, value in slots.items() if value is not None],
                         ['.lake/build/ir/ImbalancedChen/P5OriginalSingletonLowerTrimPaid.setup.json'])

    def test_later_failure_cannot_be_promoted(self):
        for field, value in (('worker_exit_code', 0), ('all_selected_owners_accepted', True),
                             ('final_stock_readiness', rows[0][0]['final_stock_readiness'])):
            result = copy.deepcopy(rows[1][0]); result[field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                c.validate_scope(result, rows[1][1], c.PINNED['runs'][1]['scope'])

    def test_failure_and_accepted_prefix_cannot_be_changed(self):
        for field, value in (('failures', {}),
                             ('accepted_owners', rows[1][0]['targets'][:2])):
            result = copy.deepcopy(rows[1][0]); result[field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                c.validate_scope(result, rows[1][1], c.PINNED['runs'][1]['scope'])

    def test_reuse_cannot_be_rebound_to_later_run(self):
        result = copy.deepcopy(rows[1][0])
        result['acceptance_bindings'][c.SYNTHESIS]['source_plus_five_outputs'] = {}
        with self.assertRaises(RuntimeError):
            c.accepting_runs([(rows[0][0], {}, {}), (result, {}, {})])

    def test_original_first_target_identity_is_fixed(self):
        result = copy.deepcopy(rows[0][0]); result['targets'] = [LOWERTRIM]
        with self.assertRaises(RuntimeError):
            c.accepting_runs([(result, {}, {}), (rows[1][0], {}, {})])


if __name__ == '__main__':
    unittest.main(verbosity=2)
