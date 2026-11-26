#!/usr/bin/env python3
"""Eight narrow local checks against actual AE RESULT/WORKER and metadata.

No environment collection, cloud call, Lean execution, or old proof test is run.
The pure flat-summary check supplies a minimal public-view fixture; it does not
claim to have read runtime context, stock command files, or six receipt files.
"""
from pathlib import Path
from types import ModuleType
import ast
import copy
import json
import sys
import unittest

sys.dont_write_bytecode = True
BASE = Path('/tmp/p15-ae-actual')
path = BASE / 'collect_ae_acceptance.py'
c = ModuleType('fixed_AE_collector_local_tests')
c.__file__ = str(path)
exec(compile(path.read_bytes(), str(path), 'exec'), c.__dict__)
ATLASTRIM = 'ImbalancedChen.P1OriginalSingletonAtlasTrim'
RESERVE = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
ROUGH = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
SYNTHESIS = 'ImbalancedChen.P5OriginalSharpPrimeSynthesis'
MEAN = 'ImbalancedChen.P5PrimeDivisorMeanCorrection'
ENDPOINT = 'ImbalancedChen.P5OriginalPrimeEndpointLogPayment'
meta_raw = (BASE / 'ACTUAL_AE_METADATA.json').read_bytes()
meta = json.loads(meta_raw)
manifest_raw = Path('/tmp/p15-entrypoint-ae/SOURCE_MANIFEST.json').read_bytes()
manifest = json.loads(manifest_raw)
graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
rows = []
for index in (0, 1):
    raw = (BASE / ('attempt-%05d-RESULT.json' % index)).read_bytes()
    result = json.loads(raw)
    worker = {k: v for k, v in result.items()
              if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    worker_raw = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
    rows.append((result, worker, raw, worker_raw))


def source_closure(modules):
    seen, todo = set(), list(modules)
    while todo:
        module = todo.pop()
        if module not in seen:
            seen.add(module)
            todo.extend(graph[module])
    return seen


class FixedAETests(unittest.TestCase):
    def test_both_actual_result_worker_byte_pins(self):
        self.assertEqual(c.raw_fp(meta_raw), {
            'bytes': 13520,
            'sha256': '6145eb2f0ebb8e1d6d3d0968e711d93478705bf01f44c08906eaa9ea74955fed'})
        self.assertEqual(c.PINNED, json.loads((BASE / 'FROZEN_AE_COLLECTOR_INPUTS.json').read_bytes()))
        for index, (_, _, raw, worker_raw) in enumerate(rows):
            pins = c.PINNED['runs'][index]['pins']
            self.assertEqual(c.raw_fp(raw), pins['RESULT.json'])
            self.assertEqual(c.raw_fp(worker_raw), pins['WORKER_RESULT.json'])
            self.assertEqual(pins, {name: c.pin(row) for name, row in
                meta['runs']['attempt-%05d' % index].items()})
            for stem in ('CONTEXT', 'GIT'):
                self.assertEqual(pins[stem + '_BEFORE.json'], pins[stem + '_AFTER.json'])

    def test_actual_first_and_later_partial_scope_status(self):
        self.assertTrue(c.validate_scope(rows[0][0], rows[0][1], c.PINNED['runs'][0]['scope']))
        self.assertFalse(c.validate_scope(rows[1][0], rows[1][1], c.PINNED['runs'][1]['scope']))
        self.assertEqual(rows[0][0]['targets'], [c.LOWERTRIM])
        self.assertEqual(rows[1][0]['targets'], [c.LOWERTRIM, ATLASTRIM, RESERVE, ROUGH])
        self.assertEqual(rows[1][0]['accepted_owners'], [c.LOWERTRIM, ATLASTRIM])
        self.assertEqual(rows[1][0]['reused_complete_selected_owners'], [c.LOWERTRIM])
        self.assertEqual(list(rows[1][0]['failures']), [RESERVE])
        self.assertEqual(rows[1][0]['targets'][len(rows[1][0]['accepted_owners']) + 1:], [ROUGH])
        self.assertNotIn('final_stock_readiness', rows[1][0])
        self.assertNotIn('final_stock_readiness', rows[1][1])
        self.assertEqual([row[0]['selected_live_source_count'] for row in rows], [119, 157])
        self.assertEqual(set(rows[0][0]['original_supplier_acceptance_bindings']),
                         {ENDPOINT, MEAN, SYNTHESIS})
        self.assertEqual(len(rows[1][0]['original_supplier_acceptance_bindings']), 27)

    def test_distinct_accepting_runs_and_partial_public_identity(self):
        self.assertEqual(c.accepting_runs([(row[0], {}, {}) for row in rows]),
                         {c.LOWERTRIM: 0, ATLASTRIM: 1})
        self.assertEqual(rows[0][0]['acceptance_bindings'][c.LOWERTRIM],
                         rows[1][0]['acceptance_bindings'][c.LOWERTRIM])
        self.assertNotIn(ATLASTRIM, rows[0][0]['acceptance_bindings'])
        runs = []
        for index, (result, _, _, _) in enumerate(rows):
            n = len(result['accepted_owners'])
            complete = result['all_selected_owners_accepted']
            public = {k: result[k] for k in ('targets', 'accepted_owners',
                'reused_complete_selected_owners', 'worker_exit_code', 'all_selected_owners_accepted')}
            public.update(
                compiler_job=c.PINNED['runs'][index]['compiler_job'],
                original_run=str(c.ROOT / c.AE / 'runs' / ('attempt-%05d' % index)),
                # Requested order is a fixture field here; runtime read_run checks the actual context.
                original_requested_targets=result['targets'],
                original_live_source_count=result['selected_live_source_count'],
                failed_modules=list(result['failures']),
                not_accepted_modules=result['targets'][n:],
                not_started_modules=[] if complete else result['targets'][n + 1:],
                dispatch_error=result.get('dispatch_error'),
                original_final_stock_readiness={'recorded': complete},
                evidence_bindings=meta['runs']['attempt-%05d' % index])
            runs.append((result, {}, public))
        common = {'source_commit': c.AE, 'selected_owners_revalidated': [c.LOWERTRIM, ATLASTRIM],
                  'current_read_live_source_count': 153, 'current_read_preserved_dependency_count': 151}
        summaries = {}
        for module, index in ((c.LOWERTRIM, 0), (ATLASTRIM, 1)):
            owner = {**c.PINNED['owners'][module], 'later_same_AE_reuse_run':
                     runs[1][2]['original_run'] if index == 0 else None}
            summaries[module] = c.flat_summary(runs, index, module, owner, common)
            binding = rows[index][0]['acceptance_bindings'][module]
            self.assertEqual(len(binding['source_plus_five_outputs']), 6)
            self.assertEqual(len(binding['all_observed_target_artifacts']), 21)
        lower, atlas = summaries[c.LOWERTRIM], summaries[ATLASTRIM]
        self.assertEqual(lower['original_run'], 'runs/attempt-00000')
        self.assertEqual(lower['original_group_live_closure_count'], 119)
        self.assertTrue(lower['original_group_all_selected_owners_accepted'])
        self.assertTrue(lower['original_final_stock_readiness']['recorded'])
        self.assertEqual(lower['later_same_source_reuse'], runs[1][2])
        self.assertEqual(atlas['original_run'], 'runs/attempt-00001')
        self.assertEqual(atlas['compiler_job'], 'job_698d39e25f9d4800a912dc27a0bfe84b')
        self.assertEqual(atlas['original_group_live_closure_count'], 157)
        self.assertFalse(atlas['original_group_all_selected_owners_accepted'])
        self.assertEqual(atlas['original_group_failed_modules'], [RESERVE])
        self.assertEqual(atlas['original_group_not_started_modules'], [ROUGH])
        self.assertFalse(atlas['original_final_stock_readiness']['recorded'])
        self.assertIsNone(atlas['later_same_source_reuse'])
        self.assertEqual(atlas['owners'][ATLASTRIM]['owned_count'], 11)
        self.assertEqual(atlas['owners'][ATLASTRIM]['public_count'], 9)

    def test_actual_counts_joint_scope_failed_slots_and_ten_extra_pins(self):
        self.assertEqual(c.raw_fp(manifest_raw), c.MANIFEST_FP)
        self.assertEqual(len(manifest['previously_accepted_targets']), 14)
        for module, index, owned, public, own_scope in (
                (c.LOWERTRIM, 0, 10, 10, 119), (ATLASTRIM, 1, 11, 9, 153)):
            owner = c.PINNED['owners'][module]
            self.assertEqual((owner['accepting_run_index'], owner['owned_count'], owner['public_count']),
                             (index, owned, public))
            self.assertEqual(owner['source'], c.pin(meta['accepted_owners'][module]['source']))
            self.assertEqual(owner['audit_result'], c.pin(meta['accepted_owners'][module]['audit_result']))
            self.assertEqual(owner['owner_live_source_closure_count'], own_scope)
            self.assertEqual(len(source_closure([module])), own_scope)
        active = source_closure(c.PINNED['owners'])
        self.assertEqual((len(active), len(active - set(c.PINNED['owners']))), (153, 151))
        self.assertEqual((c.PINNED['current_read_live_source_count'],
                          c.PINNED['current_read_preserved_dependency_count']), (153, 151))
        self.assertEqual(len(set(rows[1][0]['original_supplier_acceptance_bindings']) & active), 25)
        self.assertEqual(set(c.PINNED['failed_artifact_observations']), {RESERVE})
        slots = c.PINNED['failed_artifact_observations'][RESERVE]
        self.assertEqual(len(slots), 21)
        self.assertEqual([p for p, value in slots.items() if value is not None],
                         ['.lake/build/ir/ImbalancedChen/P5OriginalPrimeAtlasReserveBranches.setup.json'])
        updater = Path('/tmp/p15-lowertrim-repair/apply_lowertrim_repair.py').read_bytes()
        inherited = ast.literal_eval(next(n.value for n in ast.parse(updater).body
            if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and
                t.id == 'INHERITED_EXTRA_PINS' for t in n.targets)))
        self.assertEqual(len(inherited), 5)
        expected = dict(inherited)
        install = meta['lowertrim_install']
        expected[install['path']] = c.pin(install)
        failure = meta['failures'][RESERVE]
        for name in ('source', 'normal_metadata', 'diagnostic_log_binding'):
            value = failure[name]
            expected[value['path']] = c.pin(value)
        for p, value in failure['artifact_slots'].items():
            if value is not None:
                expected[p] = c.pin(value)
        self.assertEqual(len(expected), 10)
        self.assertEqual(c.PINNED['extra_pins'], expected)

    def test_later_failure_cannot_be_promoted(self):
        for field, value in (('worker_exit_code', 0), ('all_selected_owners_accepted', True),
                             ('final_stock_readiness', rows[0][0]['final_stock_readiness'])):
            result = copy.deepcopy(rows[1][0]); result[field] = value
            with self.subTest(field=field), self.assertRaises(RuntimeError):
                c.validate_scope(result, rows[1][1], c.PINNED['runs'][1]['scope'])

    def test_failure_and_accepted_prefix_cannot_be_changed(self):
        for field, value in (('failures', {}),
                             ('accepted_owners', rows[1][0]['targets'][:3]),
                             ('accepted_owners', [c.LOWERTRIM])):
            result = copy.deepcopy(rows[1][0]); result[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(RuntimeError):
                c.validate_scope(result, rows[1][1], c.PINNED['runs'][1]['scope'])

    def test_original_reuse_and_new_owner_origin_cannot_be_rebound(self):
        for mutation in ('change_lower_binding', 'drop_lower_reuse', 'make_atlas_a_reuse'):
            result = copy.deepcopy(rows[1][0])
            if mutation == 'change_lower_binding':
                result['acceptance_bindings'][c.LOWERTRIM]['source_plus_five_outputs'] = {}
            elif mutation == 'drop_lower_reuse':
                result['reused_complete_selected_owners'] = []
            else:
                result['reused_complete_selected_owners'].append(ATLASTRIM)
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                c.accepting_runs([(rows[0][0], {}, {}), (result, {}, {})])

    def test_original_first_target_identity_is_fixed(self):
        result = copy.deepcopy(rows[0][0]); result['targets'] = [ATLASTRIM]
        with self.assertRaises(RuntimeError):
            c.accepting_runs([(result, {}, {}), (rows[1][0], {}, {})])


if __name__ == '__main__':
    unittest.main(verbosity=2)
