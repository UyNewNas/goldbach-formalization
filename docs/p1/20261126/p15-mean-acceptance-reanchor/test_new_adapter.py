#!/usr/bin/env python3
"""New Endpoint@Y adapter checks only; no cloud, Lean, or old-proof execution.

RESULT and reconstructed WORKER byte pins are checked against actual evidence.
The retained-adapter control-flow fixture mocks runtime reads and generic audit;
it does not claim fresh runtime, filesystem, receipt, or Lean acceptance.
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
ROOT = Path('/tmp/p15-entrypoint-aa')
ACTUAL = Path('/tmp/p15-y-actual')
path = ROOT/'run_selected.py'
y = ModuleType('AA_new_adapter_tests'); y.__file__ = str(path)
exec(compile(path.read_bytes(), str(path), 'exec'), y.__dict__)
ENDPOINT, MEAN = y.ENDPOINT_Y_MODULE, y.ENDPOINT_Y_FAILED_MEAN
prior = y.ENDPOINT_Y_PREVIOUSLY_ACCEPTED_TARGETS[ENDPOINT]
public_raw = (ACTUAL/'ENDPOINT_Y_PUBLIC_ACCEPTANCE.json').read_bytes()
public = json.loads(public_raw)
metadata = json.loads((ACTUAL/'ACTUAL_Y_METADATA.json').read_bytes())
manifest = json.loads((ROOT/'SOURCE_MANIFEST.json').read_bytes())
graph = {m: row['imports'] for m, row in manifest['project_sources'].items()}
sources = {m: row['sha256'] for m, row in manifest['project_sources'].items()}
old_driver = Path('/tmp/p15-entrypoint-y/run_selected.py').read_bytes()
rows = []
for index in (0, 1):
    raw = (ACTUAL/('attempt-%05d-RESULT.json' % index)).read_bytes()
    result = json.loads(raw)
    worker = {k: v for k, v in result.items()
              if k not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    rows.append((result, worker, raw, (json.dumps(worker, indent=2, sort_keys=True)+'\n').encode()))


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def pin(value):
    return {k: value[k] for k in ('bytes', 'sha256')}


def closure(g, roots):
    seen, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module not in seen:
            seen.add(module); pending.extend(g[module])
    return seen


class NewAdapterTests(unittest.TestCase):
    def scope(self, p=public, first=None, worker=None):
        y.require_endpoint_y_prior_scope(ENDPOINT, prior, p,
            rows[0][0] if first is None else first, rows[0][1] if worker is None else worker)

    def test_actual_Endpoint_Y_scope_24_24_first110(self):
        self.scope()
        self.assertEqual((prior['owned_count'], prior['public_count']), (24, 24))
        self.assertEqual(prior['historical_group']['run'], 'runs/attempt-00000')

    def test_both_actual_RESULT_and_reconstructed_WORKER_pins(self):
        for index, (_, _, raw, worker) in enumerate(rows):
            bindings = metadata['runs']['attempt-%05d' % index]
            self.assertEqual(fp(raw), pin(bindings['RESULT.json']))
            self.assertEqual(fp(worker), pin(bindings['WORKER_RESULT.json']))

    def test_new_source_binding_and_own_closure(self):
        s = SimpleNamespace(h=SimpleNamespace(closure=closure))
        y.endpoint_y_prior_source_binding(s, graph, sources, ENDPOINT, prior)
        with self.assertRaises(ValueError):
            y.endpoint_y_prior_source_binding(s, graph, {**sources, ENDPOINT: '0'*64}, ENDPOINT, prior)
        with self.assertRaises(ValueError):
            y.endpoint_y_prior_source_binding(s, {**graph, ENDPOINT: []}, sources, ENDPOINT, prior)
        with self.assertRaises(ValueError):
            y.selection([ENDPOINT])
        self.assertNotIn(ENDPOINT, closure(graph, [MEAN]))

    def test_identity_counts_collection_scope_and_later_status_reject_changes(self):
        mutations = [
            lambda p: p.__setitem__('source_commit', y.SOURCE_ANCHOR),
            lambda p: p.__setitem__('original_run', 'runs/attempt-00001'),
            lambda p: p.__setitem__('current_read_live_source_count', 157),
            lambda p: p.__setitem__('current_read_preserved_dependency_count', 151),
            lambda p: p['owners'][ENDPOINT].__setitem__('owned_count', 15),
            lambda p: p['owners'][ENDPOINT].__setitem__('receipt_rebound_to_current_commit', True),
            lambda p: p['owners'][ENDPOINT]['receipt_bindings'].pop('owned_log'),
            lambda p: p['later_same_source_reuse'].__setitem__('all_selected_owners_accepted', True),
            lambda p: p['later_same_source_reuse'].__setitem__('not_started_modules', []),
        ]
        for index, mutate in enumerate(mutations):
            p = copy.deepcopy(public); mutate(p)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                self.scope(p)

    def test_original_first_final_stock_required(self):
        first = copy.deepcopy(rows[0][0]); first.pop('final_stock_readiness')
        with self.assertRaises((ValueError, KeyError)):
            self.scope(first=first)

    def test_retained_new_adapter_real_scope_with_mocked_runtime_io(self):
        self.retained()

    def test_later_failure_reuse_and_source_artifact_changes_rejected(self):
        for corrupt in ('promoted', 'failure_removed', 'accepted_mean', 'reused_binding',
                        'full21', 'source_plus_five'):
            with self.subTest(corrupt=corrupt), self.assertRaises(ValueError):
                self.retained(corrupt)

    def retained(self, corrupt=None):
        base = Path(prior['historical_group']['evidence_root'])/prior['source_commit']
        catalog, calls = {}, []
        for index, (result0, worker0, raw0, worker_raw0) in enumerate(rows):
            result, worker = copy.deepcopy(result0), copy.deepcopy(worker0)
            if index == 1:
                if corrupt == 'promoted':
                    result['worker_exit_code'] = 0; result['all_selected_owners_accepted'] = True
                if corrupt == 'failure_removed':
                    result['failures'] = {}; worker['failures'] = {}
                if corrupt == 'accepted_mean':
                    result['accepted_owners'].append(MEAN); worker['accepted_owners'].append(MEAN)
                if corrupt == 'reused_binding':
                    result['acceptance_bindings'][ENDPOINT]['source_plus_five_outputs'] = {}
                    worker['acceptance_bindings'][ENDPOINT]['source_plus_five_outputs'] = {}
            run = base/('runs/attempt-%05d' % index)
            bindings = metadata['runs']['attempt-%05d' % index]
            catalog[str(run/'RESULT.json')] = (json.dumps(result).encode(), pin(bindings['RESULT.json']))
            catalog[str(run/'WORKER_RESULT.json')] = (json.dumps(worker).encode(), pin(bindings['WORKER_RESULT.json']))
            for stem in ('CONTEXT', 'GIT'):
                for phase in ('BEFORE', 'AFTER'):
                    name = stem+'_'+phase+'.json'
                    catalog[str(run/name)] = (('opaque fixed '+str(run)+stem).encode(), pin(bindings[name]))
            catalog[str(run/'executed-driver.py')] = (old_driver, pin(prior['historical_group']['driver']))
        stock, public_stock = rows[0][0]['final_stock_readiness'], public['original_final_stock_readiness']
        # Semantic reconstruction for mock IO: original command key order is not
        # available locally. Production retained_read verifies the original byte
        # pin; this fixture checks that exact pin argument and parsed behavior.
        command_raw = (json.dumps(stock, indent=2, sort_keys=True)+'\n').encode()
        catalog[public_stock['command']['path']] = (command_raw, pin(public_stock['command']))
        catalog[public_stock['log']['path']] = (b'opaque fixed original stock log', pin(public_stock['log']))
        binding = rows[0][0]['acceptance_bindings'][ENDPOINT]
        expected = binding['all_observed_target_artifacts']
        self.assertEqual(set(expected), set(y.artifact_paths(ENDPOINT)))
        artifacts = copy.deepcopy(expected)
        snapshot = copy.deepcopy(binding['source_plus_five_outputs'])
        if corrupt == 'full21':
            artifacts[next(iter(artifacts))] = {'bytes': 1, 'sha256': '0'*64}
        if corrupt == 'source_plus_five':
            snapshot = {}
        selected = set(manifest['selection_guidance']['subsequent_6_targets'])
        spec = SimpleNamespace(manifest=copy.deepcopy(manifest), graph=graph, sources=sources,
            active=closure(graph, selected), selected=selected, retained_inputs={}, dependency_pins={},
            supplier_evidence={}, historical_groups={}, historical_owners={})
        s = SimpleNamespace(
            h=SimpleNamespace(closure=closure, guard=lambda lane, argv: stock['argv']
                if lane == 0 and argv == ['lake', '--no-build', 'build', '+'+ENDPOINT+':olean']
                else self.fail('unexpected guarded command')),
            d=SimpleNamespace(snapshot=lambda project, module: snapshot))

        def read(s_, spec_, path, expected_pin=None):
            raw, declared = catalog[str(path)]
            self.assertEqual(expected_pin, declared)
            calls.append(str(path)); spec_.retained_inputs[str(path)] = declared
            return raw

        def published(ref):
            raw = public_raw if ref == prior['historical_group']['public_evidence'] else old_driver
            self.assertEqual(fp(raw), pin(ref))
            return raw

        def audited(s_, shadow, module, validate_live=False):
            self.assertEqual(module, ENDPOINT); self.assertTrue(validate_live)
            self.assertEqual(shadow.manifest['accepted_supplier_groups']['endpoint_y'], prior['historical_group'])
            spec.supplier_evidence[module] = {
                'source_commit': prior['source_commit'], 'selected_supplier_live_closure_count': 110,
                'original_group_worker_exit_code': 0, 'owned_count': 24, 'public_count': 24,
                'audit_plan': {'path': public['owners'][ENDPOINT]['receipt_paths']['audit_plan']}}
            calls.append('audit:'+module)
            return 'original-Endpoint-Y'

        with patch.object(y, 'retained_read', read), patch.object(y, 'published_binding', published), \
             patch.object(y, 'module_artifacts', lambda s_, module: artifacts), \
             patch.object(y, 'retained_owner', audited):
            self.assertEqual(y.retained_endpoint_y_prior_target(s, spec, ENDPOINT), 'original-Endpoint-Y')
        self.assertEqual(spec.dependency_pins[ENDPOINT], expected)
        self.assertEqual(calls.count('audit:'+ENDPOINT), 1)
        for index in (0, 1):
            run = base/('runs/attempt-%05d' % index)
            for name in ('RESULT.json', 'WORKER_RESULT.json', 'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json',
                         'GIT_BEFORE.json', 'GIT_AFTER.json'):
                self.assertIn(str(run/name), calls)
        self.assertIn(str(base/'runs/attempt-00001/executed-driver.py'), calls)
        self.assertIn(public_stock['command']['path'], calls)
        self.assertIn(public_stock['log']['path'], calls)


if __name__ == '__main__':
    unittest.main(verbosity=2)
