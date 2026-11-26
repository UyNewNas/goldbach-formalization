#!/usr/bin/env python3
"""Only the new fixed AE dual-owner adapter; no old suite, cloud, Git, or Lean.

Actual RESULT and reconstructed WORKER bytes are pinned to actual metadata.
The retained control-flow fixture explicitly mocks unavailable context/command/
log bytes and the generic audit operation. It checks pin arguments and semantics,
and does not assert a fresh filesystem or kernel validation.
"""
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch
import copy
import hashlib
import json
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path('/tmp/p15-entrypoint-ag')
ACTUAL = Path('/tmp/p15-ae-actual')
path = ROOT / 'run_selected.py'
g = ModuleType('AG_new_dual_AE_adapter_tests'); g.__file__ = str(path)
exec(compile(path.read_bytes(), str(path), 'exec'), g.__dict__)
L, A = g.AE_LOWERTRIM_MODULE, g.AE_ATLASTRIM_MODULE
R = 'ImbalancedChen.P5OriginalPrimeAtlasReserveBranches'
P = 'ImbalancedChen.P1OriginalSingletonAtlasRoughPrime'
MODULES = [L, A]
INDEX = {L: 0, A: 1}
priors = g.AE_PREVIOUSLY_ACCEPTED_TARGETS
names = {L: 'LOWERTRIM_AE_PUBLIC_ACCEPTANCE', A: 'ATLASTRIM_AE_PUBLIC_ACCEPTANCE'}
public_raws = {m: (ACTUAL / (names[m] + '.json')).read_bytes() for m in MODULES}
publics = {m: json.loads(raw) for m, raw in public_raws.items()}
metadata = json.loads((ACTUAL / 'ACTUAL_AE_METADATA.json').read_bytes())
manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_bytes())
graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
sources = {m: row['sha256'] for m, row in manifest['project_sources'].items()}
old_driver = Path('/tmp/p15-entrypoint-ae/run_selected.py').read_bytes()
rows = []
for i in (0, 1):
    raw = (ACTUAL / ('attempt-%05d-RESULT.json' % i)).read_bytes()
    result = json.loads(raw)
    worker = {k: v for k, v in result.items()
              if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    rows.append((result, worker, raw, (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()))


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(value):
    return {k: value[k] for k in ('bytes', 'sha256')}


def closure(gra, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module); pending.extend(gra[module])
    return seen


class DualAEPriorTests(unittest.TestCase):
    def scope(self, module, public=None, original=None, worker=None):
        index = INDEX[module]
        g.require_ae_prior_scope(module, priors[module], publics[module] if public is None else public,
            rows[index][0] if original is None else original, rows[index][1] if worker is None else worker)

    def test_actual_two_owner_scopes_counts_and_original_runs(self):
        for module, expected in [(L, (10, 10, 119, 'runs/attempt-00000', 0)),
                                 (A, (11, 9, 153, 'runs/attempt-00001', 1))]:
            with self.subTest(module=module):
                self.scope(module)
                p = priors[module]
                self.assertEqual((p['owned_count'], p['public_count'], p['live_source_closure_count'],
                                  p['historical_group']['run'], g.AE_PRIOR_RUNS[module]['exit_code']), expected)
                self.assertEqual(publics[module]['selected_owners_revalidated'], MODULES)
        self.assertEqual(g.AE_PRIOR_RUNS[A]['failed'], [R])
        self.assertEqual(g.AE_PRIOR_RUNS[A]['not_started'], [P])
        self.assertEqual(g.AE_PRIOR_RUNS[A]['accepted'], [L, A])
        self.assertEqual(g.AE_PRIOR_RUNS[A]['reused'], [L])

    def test_actual_run_bytes_and_fixed_receipt_context_pins(self):
        for i, (_, _, raw, worker_raw) in enumerate(rows):
            pins = metadata['runs']['attempt-%05d' % i]
            self.assertEqual(fp(raw), pin(pins['RESULT.json']))
            self.assertEqual(fp(worker_raw), pin(pins['WORKER_RESULT.json']))
        self.assertEqual([len(row[0]['original_supplier_acceptance_bindings']) for row in rows], [3, 27])
        for module in MODULES:
            mutations = [
                lambda p: p['original_result'].__setitem__('sha256', '0' * 64),
                lambda p: p['original_worker_result'].__setitem__('sha256', '0' * 64),
                lambda p: p['owners'][module]['receipt_bindings']['owned_exports'].__setitem__('sha256', '0' * 64),
                lambda p: p['original_context_pairs']['CONTEXT']['before'].__setitem__('sha256', '0' * 64),
            ]
            for index, mutate in enumerate(mutations):
                public = copy.deepcopy(publics[module]); mutate(public)
                with self.subTest(module=module, mutation=index), self.assertRaises(ValueError):
                    self.scope(module, public=public)

    def test_source_closures_selection_and_real_next_scope_inactivity(self):
        s = SimpleNamespace(h=SimpleNamespace(closure=closure))
        for module in MODULES:
            g.ae_prior_source_binding(s, graph, sources, module, priors[module])
            with self.subTest(module=module, negative='source'), self.assertRaises(ValueError):
                g.ae_prior_source_binding(s, graph, {**sources, module: '0' * 64}, module, priors[module])
            with self.subTest(module=module, negative='closure'), self.assertRaises(ValueError):
                g.ae_prior_source_binding(s, {**graph, module: []}, sources, module, priors[module])
            with self.subTest(module=module, negative='new selection'), self.assertRaises(ValueError):
                g.selection([module])
        for selected, count, deps, hist in [([R], 140, 139, 21), ([R, P], 144, 142, 24)]:
            active = closure(graph, selected)
            self.assertEqual((len(active), len(active - set(selected)), len(active | set(manifest['targets']))),
                             (count, deps, 152))
            historical = set(manifest['previously_accepted_targets']) | set(manifest['accepted_suppliers'])
            self.assertEqual(len(active & historical), hist)
            self.assertFalse(active & set(MODULES))
            spec = SimpleNamespace(active=active, selected=set(selected))
            with patch.object(g, 'retained_read', side_effect=AssertionError('inactive prior was read')), \
                 patch.object(g, 'retained_owner', side_effect=AssertionError('inactive prior was audited')):
                for module in MODULES:
                    with self.assertRaises(ValueError):
                        g.retained_ae_prior_target(s, spec, module)

    def test_joint_read_identity_counts_paths_and_reuse_fields_reject_changes(self):
        for module in MODULES:
            mutations = [
                lambda p: p.__setitem__('source_commit', g.SOURCE_ANCHOR),
                lambda p: p.__setitem__('original_run', 'runs/attempt-00001' if module == L else 'runs/attempt-00000'),
                lambda p: p.__setitem__('selected_owners_revalidated', [module]),
                lambda p: p.__setitem__('current_read_live_source_count', 119),
                lambda p: p.__setitem__('current_read_preserved_dependency_count', 152),
                lambda p: p['owners'][module].__setitem__('owner_live_source_closure_count', 153 if module == L else 119),
                lambda p: p['owners'][module].__setitem__('owned_count', 11 if module == L else 10),
                lambda p: p['owners'][module].__setitem__('public_count', 9 if module == L else 11),
                lambda p: p['owners'][module].__setitem__('receipt_rebound_to_current_commit', True),
                lambda p: p['owners'][module]['receipt_paths'].__setitem__('normal', '/wrong/NORMAL_PASS.json'),
                lambda p: p['owners'][module].__setitem__('later_same_AE_reuse_run', None if module == L else 'fake-run'),
                lambda p: p.__setitem__('later_same_source_reuse', None if module == L else g.AE_PRIOR_LATER_REUSE),
            ]
            for index, mutate in enumerate(mutations):
                public = copy.deepcopy(publics[module]); mutate(public)
                with self.subTest(module=module, mutation=index), self.assertRaises(ValueError):
                    self.scope(module, public=public)

    def test_first_final_stock_and_later_partial_failure_are_distinct(self):
        first = copy.deepcopy(rows[0][0]); first.pop('final_stock_readiness')
        with self.assertRaises((ValueError, KeyError)):
            self.scope(L, original=first)
        later, worker = copy.deepcopy(rows[1][0]), copy.deepcopy(rows[1][1])
        later['final_stock_readiness'] = worker['final_stock_readiness'] = rows[0][0]['final_stock_readiness']
        with self.assertRaises(ValueError):
            self.scope(A, original=later, worker=worker)
        for mutation in ('promoted', 'failure_removed'):
            later, worker = copy.deepcopy(rows[1][0]), copy.deepcopy(rows[1][1])
            if mutation == 'promoted':
                later['worker_exit_code'] = 0; later['all_selected_owners_accepted'] = True
            else:
                later['failures'] = {}; worker['failures'] = {}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.scope(A, original=later, worker=worker)

    def test_retained_reads_both_fixed_runs_audits_only_requested_active_owner(self):
        for module in MODULES:
            with self.subTest(module=module):
                self.retained(module)

    def test_cross_run_reuse_pins_source_plus_five_and_full21_reject_changes(self):
        for module in MODULES:
            for corrupt in ('reuse_binding', 'first_result_pin', 'later_worker_pin', 'full21', 'source_plus_five'):
                with self.subTest(module=module, corrupt=corrupt), self.assertRaises(ValueError):
                    self.retained(module, corrupt)

    def retained(self, module, corrupt=None):
        prior = priors[module]
        base = Path(prior['historical_group']['evidence_root']) / prior['source_commit']
        catalog, calls = {}, []
        for index, (result0, worker0, raw0, worker_raw0) in enumerate(rows):
            result, worker = copy.deepcopy(result0), copy.deepcopy(worker0)
            if index == 1 and corrupt == 'reuse_binding':
                result['acceptance_bindings'][L]['source_plus_five_outputs'] = {}
                worker['acceptance_bindings'][L]['source_plus_five_outputs'] = {}
            run = base / ('runs/attempt-%05d' % index)
            bindings = metadata['runs']['attempt-%05d' % index]
            result_raw = raw0 if result == result0 else json.dumps(result).encode()
            worker_raw = worker_raw0 if worker == worker0 else json.dumps(worker).encode()
            catalog[str(run / 'RESULT.json')] = (result_raw, pin(bindings['RESULT.json']))
            catalog[str(run / 'WORKER_RESULT.json')] = (worker_raw, pin(bindings['WORKER_RESULT.json']))
            for stem in ('CONTEXT', 'GIT'):
                for phase in ('BEFORE', 'AFTER'):
                    name = stem + '_' + phase + '.json'
                    catalog[str(run / name)] = (('opaque fixed ' + str(run) + stem).encode(), pin(bindings[name]))
            catalog[str(run / 'executed-driver.py')] = (old_driver, pin(prior['historical_group']['driver']))
        stock, public_stock = rows[0][0]['final_stock_readiness'], publics[L]['original_final_stock_readiness']
        # Original stock command ordering and context/log bytes are not read by
        # this local fixture. Check their actual required pins and parsed values.
        command_raw = (json.dumps(stock, indent=2, sort_keys=True) + '\n').encode()
        catalog[public_stock['command']['path']] = (command_raw, pin(public_stock['command']))
        catalog[public_stock['log']['path']] = (b'opaque original stock log', pin(public_stock['log']))
        binding = rows[INDEX[module]][0]['acceptance_bindings'][module]
        expected = binding['all_observed_target_artifacts']
        self.assertEqual(set(expected), set(g.artifact_paths(module)))
        artifacts, snapshot = copy.deepcopy(expected), copy.deepcopy(binding['source_plus_five_outputs'])
        if corrupt == 'full21':
            artifacts[next(iter(artifacts))] = {'bytes': 1, 'sha256': '0' * 64}
        if corrupt == 'source_plus_five':
            snapshot = {}
        # Isolated active-owner invocation; actual next AG selections are tested
        # above and contain neither new prior. LowerTrim's own closure excludes
        # AtlasTrim, which must still have only its fixed old records read here.
        spec = SimpleNamespace(manifest=copy.deepcopy(manifest), graph=graph, sources=sources,
            active=closure(graph, [module]), selected=set(), retained_inputs={}, dependency_pins={},
            supplier_evidence={}, historical_groups={}, historical_owners={})

        def snap(project, queried):
            self.assertEqual(project, g.PROJECT); self.assertEqual(queried, module)
            calls.append('snapshot:' + queried)
            return snapshot

        s = SimpleNamespace(h=SimpleNamespace(closure=closure,
            guard=lambda lane, argv: stock['argv'] if lane == 0 and
                argv == ['lake', '--no-build', 'build', '+' + L + ':olean'] else self.fail('unexpected guarded command')),
            d=SimpleNamespace(snapshot=snap))

        def retained_read(s_, spec_, path_, expected_pin=None):
            raw, declared = catalog[str(path_)]
            if expected_pin != declared:
                raise ValueError('adapter requested a different original receipt pin: ' + str(path_))
            calls.append(str(path_)); spec_.retained_inputs[str(path_)] = declared
            return raw

        def published(ref):
            for owner_module in MODULES:
                if ref == priors[owner_module]['historical_group']['public_evidence']:
                    raw = public_raws[owner_module]
                    self.assertEqual(fp(raw), pin(ref))
                    return raw
            self.assertEqual(ref, priors[L]['historical_group']['driver'])
            self.assertEqual(fp(old_driver), pin(ref))
            return old_driver

        def module_artifacts(s_, queried):
            self.assertEqual(queried, module)
            calls.append('artifacts:' + queried)
            return artifacts

        def audited(s_, shadow, queried, validate_live=False):
            self.assertEqual(queried, module); self.assertTrue(validate_live)
            self.assertEqual(shadow.manifest['accepted_supplier_groups'][prior['group']], prior['historical_group'])
            spec.supplier_evidence[module] = {
                'source_commit': prior['source_commit'],
                'selected_supplier_live_closure_count': prior['live_source_closure_count'],
                'original_group_worker_exit_code': INDEX[module],
                'owned_count': prior['owned_count'], 'public_count': prior['public_count'],
                'audit_plan': {'path': publics[module]['owners'][module]['receipt_paths']['audit_plan']}}
            calls.append('audit:' + module)
            return 'original:' + module

        scopes = copy.deepcopy(g.AE_PRIOR_RUNS)
        if corrupt == 'first_result_pin':
            scopes[L]['result']['sha256'] = '0' * 64
        if corrupt == 'later_worker_pin':
            scopes[A]['worker']['sha256'] = '0' * 64
        with patch.object(g, 'AE_PRIOR_RUNS', scopes), patch.object(g, 'retained_read', retained_read), \
             patch.object(g, 'published_binding', published), patch.object(g, 'module_artifacts', module_artifacts), \
             patch.object(g, 'retained_owner', audited):
            self.assertEqual(g.retained_ae_prior_target(s, spec, module), 'original:' + module)
        self.assertEqual(spec.dependency_pins[module], expected)
        self.assertEqual([x for x in calls if x.startswith('audit:')], ['audit:' + module])
        for index in (0, 1):
            run = base / ('runs/attempt-%05d' % index)
            for name in ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
                         'GIT_BEFORE.json', 'GIT_AFTER.json', 'executed-driver.py'):
                self.assertIn(str(run / name), calls)
        self.assertIn(public_stock['command']['path'], calls)
        self.assertIn(public_stock['log']['path'], calls)


if __name__ == '__main__':
    unittest.main(verbosity=2)
