#!/usr/bin/env python3
"""Eight frozen AG collector checks against actual successful run0/run1 evidence.

ACTUAL_EXPECTATIONS is frozen from real AG metadata and both original results.
No runtime collector, original proof suite, compiler, or cloud operation is called.
The pure flat-summary fixture does not claim local reads of runtime receipt files.
"""
from pathlib import Path
from types import ModuleType
import copy
import json
import sys
import unittest

sys.dont_write_bytecode = True
ACTUAL_EXPECTATIONS = {'metadata_fp': {'bytes': 8931,
                 'sha256': '522ee024c75812f1481ade2d19e036e7ff221b708dd5ef75815106665212373a'},
 'run_complete': [True, True],
 'owner_origins': {'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': 0,
                   'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime': 1},
 'owners': {'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches': {'owned_count': 13,
                                                                   'public_count': 13,
                                                                   'own_source_closure': 140},
            'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime': {'owned_count': 6,
                                                                  'public_count': 6,
                                                                  'own_source_closure': 144}},
 'joint_scope': {'sources': 144, 'dependencies': 142, 'historical_suppliers': 24},
 'installer_metadata_key': 'reservebranches_install'}
if not isinstance(ACTUAL_EXPECTATIONS, dict):
    raise SystemExit('HOLD: actual AG tasks, metadata, installer and owner expectations are unbound')

BASE = Path('/tmp/p15-ag-actual')
path = BASE / 'collect_ag_acceptance.py'
c = ModuleType('fixed_AG_collector_local_tests')
c.__file__ = str(path)
exec(compile(path.read_bytes(), str(path), 'exec'), c.__dict__)
if not isinstance(c.PINNED, dict):
    raise SystemExit('HOLD: actual AG collector PINNED is not frozen')
ROUGH = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
meta_raw = (BASE / 'ACTUAL_AG_METADATA.json').read_bytes()
meta = json.loads(meta_raw)
manifest_raw = Path('/tmp/p15-entrypoint-ag/SOURCE_MANIFEST.json').read_bytes()
manifest = json.loads(manifest_raw)
graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
slots = json.loads((BASE / 'REQUIRED_ACTUAL_INPUTS.json').read_bytes())
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


class FixedAGTests(unittest.TestCase):
    def test_actual_result_worker_and_metadata_byte_pins(self):
        self.assertEqual(c.raw_fp(meta_raw), ACTUAL_EXPECTATIONS['metadata_fp'])
        self.assertEqual(c.PINNED, json.loads((BASE / 'FROZEN_AG_COLLECTOR_INPUTS.json').read_bytes()))
        for index, (_, _, raw, worker_raw) in enumerate(rows):
            pins = c.PINNED['runs'][index]['pins']
            self.assertEqual(c.raw_fp(raw), pins['RESULT.json'])
            self.assertEqual(c.raw_fp(worker_raw), pins['WORKER_RESULT.json'])
            self.assertEqual(pins, {name: c.pin(value) for name, value in
                meta['runs']['attempt-%05d' % index].items()})
            for stem in ('CONTEXT', 'GIT'):
                self.assertEqual(pins[stem + '_BEFORE.json'], pins[stem + '_AFTER.json'])

    def test_actual_first_later_scope_and_terminal_status(self):
        for index, (result, worker, _, _) in enumerate(rows):
            self.assertIs(c.validate_scope(result, worker, c.PINNED['runs'][index]['scope']),
                          ACTUAL_EXPECTATIONS['run_complete'][index])
            summary = meta['original_first_summary' if index == 0 else 'original_later_summary']
            self.assertTrue(all(result[key] == value for key, value in summary.items()))
            self.assertEqual('final_stock_readiness' in result,
                             ACTUAL_EXPECTATIONS['run_complete'][index])
        self.assertEqual(rows[0][0]['targets'], [c.RESERVEBRANCHES])
        self.assertEqual(rows[1][0]['targets'], [c.RESERVEBRANCHES, ROUGH])
        self.assertEqual([row[0]['selected_live_source_count'] for row in rows], [140, 144])
        self.assertEqual([len(row[0]['original_supplier_acceptance_bindings']) for row in rows], [21, 24])

    def test_actual_accepting_runs_reuse_and_public_group_identity(self):
        origins = c.accepting_runs([(row[0], {}, {}) for row in rows])
        self.assertEqual(origins, ACTUAL_EXPECTATIONS['owner_origins'])
        runs = []
        for index, (result, _, _, _) in enumerate(rows):
            n = len(result['accepted_owners']); complete = result['all_selected_owners_accepted']
            public = {key: result[key] for key in ('targets', 'accepted_owners',
                'reused_complete_selected_owners', 'worker_exit_code', 'all_selected_owners_accepted')}
            public.update(compiler_job=c.PINNED['runs'][index]['compiler_job'],
                original_run=str(c.ROOT / c.AG / 'runs' / ('attempt-%05d' % index)),
                # Fixture order only; real read_run checks the original requested context.
                original_requested_targets=result['targets'],
                original_live_source_count=result['selected_live_source_count'],
                failed_modules=list(result['failures']), not_accepted_modules=result['targets'][n:],
                not_started_modules=[] if complete else result['targets'][n + 1:],
                dispatch_error=result.get('dispatch_error'),
                original_final_stock_readiness={'recorded': complete},
                evidence_bindings=meta['runs']['attempt-%05d' % index])
            runs.append((result, {}, public))
        for module, index in origins.items():
            reused_later = index == 0 and module in rows[1][0]['reused_complete_selected_owners']
            owner = {**c.PINNED['owners'][module], 'later_same_AG_reuse_run':
                     runs[1][2]['original_run'] if reused_later else None}
            public = c.flat_summary(runs, index, module, owner, {'source_commit': c.AG})
            self.assertEqual(public['original_run'], 'runs/attempt-%05d' % index)
            self.assertEqual(public['compiler_job'], c.PINNED['runs'][index]['compiler_job'])
            self.assertEqual(public['original_group_live_closure_count'], rows[index][0]['selected_live_source_count'])
            self.assertIs(public['original_group_all_selected_owners_accepted'], ACTUAL_EXPECTATIONS['run_complete'][index])
            self.assertEqual(public['original_group_failed_modules'], list(rows[index][0]['failures']))
            self.assertEqual(public['original_final_stock_readiness']['recorded'], ACTUAL_EXPECTATIONS['run_complete'][index])
            self.assertEqual(public['later_same_source_reuse'], runs[1][2] if reused_later else None)
            binding = rows[index][0]['acceptance_bindings'][module]
            self.assertEqual(len(binding['source_plus_five_outputs']), 6)
            self.assertEqual(len(binding['all_observed_target_artifacts']), 21)

    def test_actual_owner_counts_joint_scope_failures_and_external_extras(self):
        self.assertEqual(c.raw_fp(manifest_raw), c.MANIFEST_FP)
        self.assertEqual(len(manifest['previously_accepted_targets']), 16)
        self.assertEqual(set(c.PINNED['owners']), set(ACTUAL_EXPECTATIONS['owner_origins']))
        for module, owner in c.PINNED['owners'].items():
            observed = meta['accepted_owners'][module]
            expected = ACTUAL_EXPECTATIONS['owners'][module]
            self.assertEqual((owner['owned_count'], owner['public_count']),
                             (observed['owned_count'], observed['public_count']))
            self.assertEqual((owner['owned_count'], owner['public_count']),
                             (expected['owned_count'], expected['public_count']))
            self.assertEqual(owner['accepting_run_index'], observed['first_accepting_run_index'])
            self.assertEqual(owner['source'], c.pin(observed['source']))
            self.assertEqual(owner['audit_result'], c.pin(observed['audit_result']))
            self.assertEqual(owner['owner_live_source_closure_count'], expected['own_source_closure'])
            self.assertEqual(len(source_closure([module])), expected['own_source_closure'])
        active = source_closure(c.PINNED['owners'])
        scope = ACTUAL_EXPECTATIONS['joint_scope']
        self.assertEqual((len(active), len(active - set(c.PINNED['owners']))),
                         (scope['sources'], scope['dependencies']))
        self.assertEqual((c.PINNED['current_read_live_source_count'], c.PINNED['current_read_preserved_dependency_count']),
                         (scope['sources'], scope['dependencies']))
        self.assertEqual(len(set(rows[1][0]['original_supplier_acceptance_bindings']) & active),
                         scope['historical_suppliers'])
        inherited = slots['extra_evidence_slots']['six_inherited_external_pins']
        self.assertEqual(len(inherited), 6)
        expected_extras = {**inherited,
            **slots['extra_evidence_slots']['original_AE_Reserve_failed_command_log_pins']}
        install = meta[ACTUAL_EXPECTATIONS['installer_metadata_key']]
        expected_extras[install['path']] = c.pin(install)
        remaining_failed = set(meta['failures']) - set(c.PINNED['owners'])
        self.assertEqual(set(c.PINNED['failed_artifact_observations']), remaining_failed)
        for module in remaining_failed:
            failed = meta['failures'][module]
            wanted_slots = {str(Path(p).relative_to(c.PROJECT)): c.pin(v) if v is not None else None
                            for p, v in failed['artifact_slots'].items()}
            self.assertEqual(c.PINNED['failed_artifact_observations'][module], wanted_slots)
            self.assertEqual(len(wanted_slots), 21)
            for key in ('source', 'normal_metadata', 'diagnostic_log_binding'):
                value = failed[key]; expected_extras[value['path']] = c.pin(value)
            for p, value in failed['artifact_slots'].items():
                if value is not None:
                    expected_extras[p] = c.pin(value)
        self.assertEqual(c.PINNED['extra_pins'], expected_extras)

    def test_terminal_and_final_stock_cannot_be_changed(self):
        for index, (original, worker, _, _) in enumerate(rows):
            for field, value in (('worker_exit_code', 1 - original['worker_exit_code']),
                                 ('all_selected_owners_accepted', not original['all_selected_owners_accepted'])):
                result = copy.deepcopy(original); result[field] = value
                with self.subTest(run=index, field=field), self.assertRaises(RuntimeError):
                    c.validate_scope(result, worker, c.PINNED['runs'][index]['scope'])
            result = copy.deepcopy(original)
            if 'final_stock_readiness' in result:
                del result['final_stock_readiness']
            else:
                result['final_stock_readiness'] = {}
            with self.subTest(run=index, field='stock'), self.assertRaises(RuntimeError):
                c.validate_scope(result, worker, c.PINNED['runs'][index]['scope'])

    def test_failure_and_accepted_prefix_cannot_be_changed(self):
        for index, (original, worker, _, _) in enumerate(rows):
            altered = original['accepted_owners'][:-1] if original['accepted_owners'] else original['targets'][:1]
            for field, value in (('failures', {'ImbalancedChen.UnexpectedOwner': 'changed'}),
                                 ('accepted_owners', altered)):
                result = copy.deepcopy(original); result[field] = value
                with self.subTest(run=index, field=field), self.assertRaises(RuntimeError):
                    c.validate_scope(result, worker, c.PINNED['runs'][index]['scope'])

    def test_accepting_origin_and_reused_binding_cannot_be_rebound(self):
        for module, index in ACTUAL_EXPECTATIONS['owner_origins'].items():
            results = [copy.deepcopy(row[0]) for row in rows]
            results[index]['reused_complete_selected_owners'].append(module)
            with self.subTest(owner=module, change='fake_reuse'), self.assertRaises(RuntimeError):
                c.accepting_runs([(r, {}, {}) for r in results])
        for module in rows[1][0]['reused_complete_selected_owners']:
            result = copy.deepcopy(rows[1][0])
            result['acceptance_bindings'][module]['source_plus_five_outputs'] = {}
            with self.subTest(owner=module, change='binding'), self.assertRaises(RuntimeError):
                c.accepting_runs([(rows[0][0], {}, {}), (result, {}, {})])

    def test_original_first_target_identity_is_fixed(self):
        result = copy.deepcopy(rows[0][0]); result['targets'] = [ROUGH]
        with self.assertRaises(RuntimeError):
            c.accepting_runs([(result, {}, {}), (rows[1][0], {}, {})])


if __name__ == '__main__':
    unittest.main(verbosity=2)
