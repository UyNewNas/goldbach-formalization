#!/usr/bin/env python3
"""Bounded local checks: actual U JSON scopes plus mocked retained-I/O control flow.

No cloud, Lean, guard, installer or canonical project invocation is performed.
Opaque CONTEXT/GIT/log payloads in the retained-I/O test are synthetic; that test
checks the exact fixed pin arguments. Actual RESULT and reconstructed WORKER
bytes are separately checked against the collector's actual fingerprints.
"""
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch
import ast
import copy
import hashlib
import json
import sys
import unittest

sys.dont_write_bytecode = True
ROOT = Path('/tmp/p15-entrypoint-w')
ACTUAL = Path('/tmp/p15-u-actual')
BASE = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')


def load(path, name):
    module = ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


def fp(raw):
    return {'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}


def funcs(raw):
    return {n.name: ast.get_source_segment(raw, n) for n in ast.parse(raw).body
            if isinstance(n, ast.FunctionDef)}


b = load(ROOT / 'build_candidate.py', 'w_builder_local_tests')
w = load(ROOT / 'run_selected.py', 'w_runner_local_tests')
old_raw = (BASE / 'entrypoint-u/run_selected.py').read_text()
new_raw = (ROOT / 'run_selected.py').read_text()
old_manifest = json.loads(Path('/tmp/p15-entrypoint-u/SOURCE_MANIFEST.json').read_bytes())
manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_bytes())
graph = {name: row['imports'] for name, row in manifest['project_sources'].items()}
sources = {name: row['sha256'] for name, row in manifest['project_sources'].items()}
fixtures = {}
for index, (module, prior) in enumerate(w.U_PREVIOUSLY_ACCEPTED_TARGETS.items()):
    name = 'WORD_U_PUBLIC_ACCEPTANCE.json' if index == 0 else 'ALLGROUP_U_PUBLIC_ACCEPTANCE.json'
    raw = (ACTUAL / ('attempt-%05d-RESULT.json' % index)).read_bytes()
    result = json.loads(raw)
    worker = {key: value for key, value in result.items()
              if key not in ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')}
    worker_raw = (json.dumps(worker, indent=2, sort_keys=True) + '\n').encode()
    fixtures[module] = {'prior': prior, 'public': json.loads((ACTUAL / name).read_bytes()),
                        'result': result, 'worker': worker, 'result_raw': raw, 'worker_raw': worker_raw}


class CandidateTests(unittest.TestCase):
    def scope(self, module, fixture=None):
        f = fixture or fixtures[module]
        w.require_u_prior_scope(module, f['prior'], f['public'], f['result'], f['worker'])

    def test_actual_result_and_reconstructed_worker_raw_pins(self):
        for module, f in fixtures.items():
            with self.subTest(module=module):
                self.assertEqual(fp(f['result_raw']), w.U_PRIOR_RUNS[module]['result'])
                self.assertEqual(fp(f['worker_raw']), w.U_PRIOR_RUNS[module]['worker'])

    def test_actual_public_and_both_original_run_scopes(self):
        for module in fixtures:
            self.scope(module)
        self.assertEqual(fixtures[b.WORD]['result']['acceptance_bindings'][b.WORD],
                         fixtures[b.ALLGROUP]['result']['acceptance_bindings'][b.WORD])

    def test_only_two_dispatches_change_and_47_functions_identical(self):
        before, after = funcs(old_raw), funcs(new_raw)
        self.assertEqual(len(before), 49)
        self.assertEqual({n for n in before if before[n] != after[n]}, {'source_manifest', 'preflight'})
        self.assertEqual(set(after) - set(before),
                         {'u_prior_source_binding', 'require_u_prior_scope', 'retained_u_prior_target'})
        original = after['source_manifest'].replace(
            ' | set(U_PREVIOUSLY_ACCEPTED_TARGETS)', '')
        original = original.replace(
            "        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:\n"
            "            require(module in TARGETS and module not in supplier and prior['group'] not in groups,\n"
            "                    'U prior classification differs: ' + module)\n"
            "            u_prior_source_binding(s, graph, sources, module, prior)\n"
            "            continue\n", '')
        self.assertEqual(original, before['source_manifest'])
        original = after['preflight'].replace(
            "        if module in U_PREVIOUSLY_ACCEPTED_TARGETS:\n"
            "            retained_u_prior_target(s, spec, module)\n"
            "        elif module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:",
            "        if module in FAMILY_S_PREVIOUSLY_ACCEPTED_TARGETS:")
        self.assertEqual(original, before['preflight'])

    def test_exact_v_manifest_smooth_only_and_all_imports(self):
        self.assertEqual(w.SOURCE_ANCHOR, 'f23c4f3308b471350064bf0d6ad1bdb0fce0d6fb')
        self.assertEqual(manifest['source_anchor_commit'], w.SOURCE_ANCHOR)
        self.assertEqual(fp((ROOT / 'SOURCE_MANIFEST.json').read_bytes())['sha256'], w.MANIFEST_SHA)
        self.assertEqual([n for n in sources if manifest['project_sources'][n] != old_manifest['project_sources'][n]],
                         [b.SMOOTH])
        for name, row in manifest['project_sources'].items():
            self.assertEqual((row['imports'], row['all_imports']),
                             (old_manifest['project_sources'][name]['imports'],
                              old_manifest['project_sources'][name]['all_imports']))
        repair = json.loads(Path('/tmp/p15-smooth-repair/REPAIR_CANDIDATE.json').read_bytes())
        self.assertEqual(b.pin(manifest['project_sources'][b.SMOOTH]), repair['after'])
        self.assertEqual(manifest['target_source_origins'][b.SMOOTH]['source_reviews'][-1],
                         {'commit': w.SOURCE_ANCHOR, 'path': b.REPAIR_PATH,
                          **fp(Path('/tmp/p15-smooth-repair/REPAIR_CANDIDATE.json').read_bytes())})

    def test_eight_old_priors_and_303_19_policy_unchanged(self):
        self.assertEqual({n: p for n, p in manifest['previously_accepted_targets'].items()
                          if n not in w.U_PREVIOUSLY_ACCEPTED_TARGETS},
                         old_manifest['previously_accepted_targets'])
        for key in ('fixed_dependencies', 'unaccepted_p3_dependencies', 'unaccepted_p3_policy',
                    'accepted_suppliers', 'accepted_supplier_groups', 'targets', 'scope', 'runtime_review'):
            self.assertEqual(manifest[key], old_manifest[key])
        self.assertEqual(len(manifest['fixed_dependencies']), 303)
        self.assertEqual(len(manifest['unaccepted_p3_dependencies']), 19)
        for module in manifest['previously_accepted_targets']:
            with self.assertRaises(ValueError):
                w.selection([module])

    def test_first130_129_and_later157_149_scopes(self):
        guide = manifest['selection_guidance']
        first, later = guide['minimum_first_targets'], guide['subsequent_8_targets']
        self.assertEqual(first, [b.SMOOTH])
        self.assertEqual(len(b.closure(graph, first)), 130)
        self.assertEqual(len(b.closure(graph, first) - set(first)), 129)
        self.assertEqual(len(later), 8)
        self.assertEqual(later[0], b.SMOOTH)
        self.assertEqual(len(b.closure(graph, later)), 157)
        self.assertEqual(len(b.closure(graph, later) - set(later)), 149)
        self.assertEqual(len(b.closure(graph, later) | set(w.TARGETS)), 160)
        self.assertFalse(set(later) & set(manifest['previously_accepted_targets']))
        self.assertFalse(b.closure(graph, later) & set(manifest['unaccepted_p3_dependencies']))
        for module in (b.WORD, b.ALLGROUP):
            self.assertNotIn(b.SMOOTH, b.closure(graph, [module]))

    def test_u_owner_source_binding_77_139(self):
        s = SimpleNamespace(h=SimpleNamespace(closure=b.closure))
        for module, prior in w.U_PREVIOUSLY_ACCEPTED_TARGETS.items():
            w.u_prior_source_binding(s, graph, sources, module, prior)
            bad = {**sources, module: '0' * 64}
            with self.assertRaises(ValueError):
                w.u_prior_source_binding(s, graph, bad, module, prior)
            with self.assertRaises(ValueError):
                w.u_prior_source_binding(s, {**graph, module: []}, sources, module, prior)

    def test_joint139_137_vs_original77_157_vs_owner77_139_not_confused(self):
        for module in fixtures:
            for key, value in (('current_read_live_source_count', 157),
                               ('current_read_preserved_dependency_count', 149),
                               ('original_group_live_closure_count', 139),
                               ('owner_live_source_closure_count', 157)):
                f = copy.deepcopy(fixtures[module])
                f['public'][key] = value
                with self.subTest(module=module, key=key), self.assertRaises(ValueError):
                    self.scope(module, f)

    def test_original_identity_counts_and_six_receipts_are_fixed(self):
        for module in fixtures:
            mutations = [
                lambda f: f['public'].__setitem__('source_commit', w.SOURCE_ANCHOR),
                lambda f: f['public'].__setitem__('original_run', 'runs/attempt-00002'),
                lambda f: f['public']['owners'][module].__setitem__('owned_count', 16),
                lambda f: f['public']['owners'][module].__setitem__('receipt_rebound_to_current_commit', True),
                lambda f: f['public']['owners'][module]['receipt_bindings'].pop('owned_log'),
                lambda f: f['public']['owners'][module]['receipt_bindings']['normal'].__setitem__('sha256', '0' * 64),
                lambda f: f['public']['owners'][module].__setitem__('source_plus_five_and_all_21_artifacts_bound_to_original_result', False),
                lambda f: f['public']['original_context_pairs']['CONTEXT']['before'].__setitem__('sha256', '0' * 64),
            ]
            for index, mutate in enumerate(mutations):
                f = copy.deepcopy(fixtures[module]); mutate(f)
                with self.subTest(module=module, mutation=index), self.assertRaises(ValueError):
                    self.scope(module, f)

    def test_allgroup_partial_cannot_be_promoted_or_failure_removed(self):
        mutations = [
            lambda f: f['result'].__setitem__('worker_exit_code', 0),
            lambda f: f['result'].__setitem__('all_selected_owners_accepted', True),
            lambda f: f['result'].__setitem__('failures', {}),
            lambda f: f['worker'].__setitem__('failures', {}),
            lambda f: f['public'].__setitem__('original_group_not_started_modules', []),
            lambda f: f['public'].__setitem__('original_group_failed_modules', []),
            lambda f: f['result'].__setitem__('final_stock_readiness', fixtures[b.WORD]['result']['final_stock_readiness']),
            lambda f: f['public'].__setitem__('original_final_stock_readiness', fixtures[b.WORD]['public']['original_final_stock_readiness']),
        ]
        for index, mutate in enumerate(mutations):
            f = copy.deepcopy(fixtures[b.ALLGROUP]); mutate(f)
            with self.subTest(mutation=index), self.assertRaises(ValueError):
                self.scope(b.ALLGROUP, f)

    def test_word_final_stock_and_later_reuse_remain_original(self):
        for field in ('final_stock_readiness',):
            f = copy.deepcopy(fixtures[b.WORD]); f['result'].pop(field)
            with self.assertRaises((ValueError, KeyError)):
                self.scope(b.WORD, f)
        f = copy.deepcopy(fixtures[b.WORD])
        f['public']['later_same_source_reuse']['all_selected_owners_accepted'] = True
        with self.assertRaises(ValueError):
            self.scope(b.WORD, f)

    def test_complete_worker_record_must_match_result(self):
        f = copy.deepcopy(fixtures[b.ALLGROUP])
        f['worker']['acceptance_class'] = 'altered'
        with self.assertRaises(ValueError):
            self.scope(b.ALLGROUP, f)

    def test_retained_adapter_calls_both_fixed_runs_and_only_active_owner_audit(self):
        for module in fixtures:
            self.run_retained_case(module)

    def test_retained_source_plus_five_or_full21_change_is_rejected(self):
        for kind in ('source_plus_five', 'full21', 'word_reuse'):
            with self.subTest(kind=kind), self.assertRaises(ValueError):
                self.run_retained_case(b.ALLGROUP, corrupt=kind)

    def run_retained_case(self, module, corrupt=None):
        reads, audits, catalog, published = [], [], {}, {}
        for owner, f in fixtures.items():
            prior, scope = f['prior'], w.U_PRIOR_RUNS[owner]
            fixed = prior['historical_group']
            base = Path(fixed['evidence_root']) / prior['source_commit']
            run = base / fixed['run']
            published[(fixed['public_evidence']['commit'], fixed['public_evidence']['path'])] = (
                ACTUAL / b.PUBLIC_FILES[owner][0]).read_bytes()
            published[(fixed['driver']['commit'], fixed['driver']['path'])] = old_raw.encode()
            rr = f['result_raw']
            if corrupt == 'word_reuse' and owner == b.ALLGROUP:
                altered = copy.deepcopy(f['result'])
                altered['acceptance_bindings'][b.WORD]['source_plus_five_outputs'] = {}
                rr = json.dumps(altered).encode()
            catalog[str(run / 'RESULT.json')] = (rr, scope['result'])
            catalog[str(run / 'WORKER_RESULT.json')] = (f['worker_raw'], scope['worker'])
            catalog[str(run / 'executed-driver.py')] = (old_raw.encode(), b.U_DRIVER)
            for stem, pair in scope['context_pairs'].items():
                for phase in ('BEFORE', 'AFTER'):
                    catalog[str(run / (stem + '_' + phase + '.json'))] = (
                        ('opaque fixed ' + str(run) + stem).encode(), pair[phase.lower()])
        first = fixtures[b.WORD]
        stock = first['result']['final_stock_readiness']
        public_stock = first['public']['original_final_stock_readiness']
        for name, raw in (('command', (json.dumps(stock, indent=2, sort_keys=True) + '\n').encode()),
                          ('log', b'opaque fixed original Word stock log')):
            catalog[public_stock[name]['path']] = (raw, b.pin(public_stock[name]))
        binding = fixtures[module]['result']['acceptance_bindings'][module]
        expected = binding['all_observed_target_artifacts']
        self.assertEqual(set(expected), set(w.artifact_paths(module)))
        self.assertEqual(len(expected), 21)
        current_artifacts = copy.deepcopy(expected)
        current_snapshot = copy.deepcopy(binding['source_plus_five_outputs'])
        if corrupt == 'full21':
            current_artifacts[next(iter(current_artifacts))] = None
            if current_artifacts == expected:
                current_artifacts[next(iter(current_artifacts))] = {'bytes': 1, 'sha256': '0' * 64}
        if corrupt == 'source_plus_five':
            current_snapshot = {}
        s = SimpleNamespace(
            h=SimpleNamespace(closure=b.closure, guard=lambda lane, argv: stock['argv']
                              if lane == 0 and argv == ['lake', '--no-build', 'build', '+' + b.WORD + ':olean']
                              else self.fail('unexpected guard command')),
            d=SimpleNamespace(snapshot=lambda project, owner: current_snapshot))
        active = b.closure(graph, [module]) | {b.SMOOTH}
        spec = SimpleNamespace(manifest=copy.deepcopy(manifest), graph=graph, sources=sources, active=active,
                               selected={b.SMOOTH}, retained_inputs={}, supplier_evidence={},
                               dependency_pins={}, historical_groups={}, historical_owners={})

        def read(s_, spec_, path, pin_=None):
            path = str(path)
            self.assertIn(path, catalog)
            raw, declared_fp = catalog[path]
            self.assertEqual(pin_, declared_fp)
            reads.append(path)
            spec_.retained_inputs[path] = declared_fp
            return raw

        def published_read(binding_):
            raw = published[(binding_['commit'], binding_['path'])]
            self.assertEqual(fp(raw), b.pin(binding_))
            return raw

        def audit(s_, shadow, owner, validate_live=False):
            self.assertEqual(owner, module)
            self.assertTrue(validate_live)
            prior = w.U_PREVIOUSLY_ACCEPTED_TARGETS[owner]
            self.assertEqual(shadow.manifest['accepted_supplier_groups'][prior['group']], prior['historical_group'])
            self.assertEqual(shadow.manifest['accepted_suppliers'][owner]['source_commit'], b.U)
            spec.supplier_evidence[owner] = {
                'source_commit': b.U, 'selected_supplier_live_closure_count': prior['live_source_closure_count'],
                'original_group_worker_exit_code': w.U_PRIOR_RUNS[owner]['exit_code'],
                'owned_count': 15, 'public_count': 15,
                'audit_plan': {'path': fixtures[owner]['public']['owners'][owner]['receipt_paths']['audit_plan']}}
            audits.append(owner)
            return 'fixed-original-U-owner'

        with patch.object(w, 'retained_read', read), patch.object(w, 'published_binding', published_read), \
             patch.object(w, 'module_artifacts', lambda s_, owner: current_artifacts), \
             patch.object(w, 'retained_owner', audit):
            self.assertEqual(w.retained_u_prior_target(s, spec, module), 'fixed-original-U-owner')
        self.assertEqual(audits, [module])
        self.assertEqual(spec.dependency_pins[module], expected)
        for f in fixtures.values():
            fixed = f['prior']['historical_group']
            run = Path(fixed['evidence_root']) / b.U / fixed['run']
            for name in ('RESULT.json', 'WORKER_RESULT.json', 'executed-driver.py',
                         'CONTEXT_BEFORE.json', 'CONTEXT_AFTER.json', 'GIT_BEFORE.json', 'GIT_AFTER.json'):
                self.assertIn(str(run / name), reads)
        self.assertIn(public_stock['command']['path'], reads)
        self.assertIn(public_stock['log']['path'], reads)


if __name__ == '__main__':
    unittest.main(verbosity=2)
