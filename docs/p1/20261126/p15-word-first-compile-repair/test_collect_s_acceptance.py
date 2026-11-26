#!/usr/bin/env python3
"""Local contract checks only; no cloud environment or historical fixtures executed."""
import ast
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location('collector', HERE / 'collect_s_acceptance.py')
c = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(c)
META = json.loads(Path('/tmp/p15-s-actual/ACTUAL_S_METADATA.json').read_text())
CAPTURES = [json.loads((Path('/tmp/p15-s-actual') / name).read_text()) for name in
    ('FamilyCapturedResult.json', 'Later11CapturedResult.json')]
RESULTS = [{k: v for k, v in r.items() if k not in ('batch6', 'path')} for r in CAPTURES]
WORKERS = [{k: v for k, v in r.items() if k not in
    ('worker_exit_code', 'all_selected_owners_accepted', 'dispatch_error')} for r in RESULTS]


class Contracts(unittest.TestCase):
    def test_actual_raw_result_and_worker_pins(self):
        for index, (result, worker) in enumerate(zip(RESULTS, WORKERS)):
            for stem, value in (('RESULT', result), ('WORKER_RESULT', worker)):
                raw = (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + '\n').encode()
                self.assertEqual(c.raw_fp(raw), c.fp_pair(c.RUN_PINS[index][stem]))
                self.assertEqual(c.raw_fp(raw), c.pin(META['attempt-%05d' % index][stem + '.json']))
            for stem in ('CONTEXT', 'GIT'):
                expected = c.fp_pair(c.GIT_PIN if stem == 'GIT' else c.RUN_PINS[index][stem])
                for side in ('BEFORE', 'AFTER'):
                    self.assertEqual(expected, c.pin(META['attempt-%05d' % index][stem + '_' + side + '.json']))

    def test_real_success_and_partial_scopes(self):
        self.assertEqual(c.validate_scope(RESULTS[0], WORKERS[0], 0), [c.FAMILY])
        self.assertEqual(c.validate_scope(RESULTS[1], WORKERS[1], 1), c.TARGETS)
        self.assertEqual(len(c.TARGETS[2:]), 9)
        self.assertEqual(RESULTS[0]['acceptance_bindings'][c.FAMILY], RESULTS[1]['acceptance_bindings'][c.FAMILY])

    def test_partial_cannot_be_promoted_or_recompiled(self):
        mutations = [('accepted_owners', [c.FAMILY, c.WORD]),
                     ('reused_complete_selected_owners', []),
                     ('targets', c.TARGETS[1:]), ('selected_live_source_count', 75)]
        for key, value in mutations:
            result, worker = copy.deepcopy(RESULTS[1]), copy.deepcopy(WORKERS[1])
            result[key] = worker[key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                c.validate_scope(result, worker, 1)
        result, worker = copy.deepcopy(RESULTS[1]), copy.deepcopy(WORKERS[1])
        result['final_stock_readiness'] = worker['final_stock_readiness'] = RESULTS[0]['final_stock_readiness']
        with self.assertRaises(RuntimeError):
            c.validate_scope(result, worker, 1)

    def test_first_success_requires_final_stock(self):
        result, worker = copy.deepcopy(RESULTS[0]), copy.deepcopy(WORKERS[0])
        del result['final_stock_readiness']
        del worker['final_stock_readiness']
        with self.assertRaises(RuntimeError):
            c.validate_scope(result, worker, 0)

    def test_real_S_manifest_scope_and_source(self):
        raw = Path('/tmp/p15-entrypoint-s/SOURCE_MANIFEST.json').read_bytes()
        self.assertEqual(c.raw_fp(raw), c.MANIFEST_FP)
        graph = json.loads(raw)['project_sources']
        def walk(roots):
            seen, todo = set(), list(roots)
            while todo:
                module = todo.pop()
                if module not in seen:
                    seen.add(module)
                    todo.extend(graph[module]['imports'])
            return seen
        self.assertEqual((len(graph), len(walk([c.FAMILY])), len(walk([c.FAMILY]) - {c.FAMILY})), (360, 75, 74))
        self.assertEqual(len(walk(c.TARGETS)), 157)
        self.assertNotIn(c.WORD, walk([c.FAMILY]))
        self.assertEqual(c.raw_fp((HERE / 'entrypoint-s/run_selected.py').read_bytes()), c.DRIVER_FP)
        self.assertEqual(c.raw_fp((HERE / 'Part3AllKFamilyLambdaCorrectionBound.lean').read_bytes()), c.SOURCE_FP)
        self.assertEqual(c.raw_fp((HERE / 'P5IndependentPrimeSourceWordDictionary.lean').read_bytes()), c.CANDIDATE_FP)

    def test_extra_actual_pins(self):
        wanted = {META[k]['path']: c.pin(META[k]) for k in
                  ('word_source', 'failed_word_setup', 'word_normal', 'family_install')}
        self.assertEqual({p: c.fp_pair(v) for p, v in c.EXTRA_PINS.items()}, wanted)
        self.assertEqual(c.AUDIT_FP, c.pin(META['family_audit']))
        self.assertEqual((META['family_audit']['json']['total_owned_exports'],
                          META['family_audit']['json']['total_public_exports']), (27, 27))

    def test_inventory_detects_mutation_and_symlink_without_writing(self):
        with tempfile.TemporaryDirectory(prefix='p15-s-collector-', dir='/tmp') as directory:
            base = Path(directory)
            evidence = base / 'receipt.json'
            evidence.write_bytes(b'original')
            before = {p.name: p.stat().st_mtime_ns for p in base.iterdir()}
            original = c.tree_inventory(base)
            self.assertEqual(before, {p.name: p.stat().st_mtime_ns for p in base.iterdir()})
            evidence.write_bytes(b'changed')
            self.assertNotEqual(original, c.tree_inventory(base))
            (base / 'alias').symlink_to(evidence)
            with self.assertRaises(RuntimeError):
                c.tree_inventory(base)

    def test_flat_prior_interface_matches_Q_shape(self):
        runs = []
        for index, result in enumerate(RESULTS):
            record = {k: result[k] for k in ('accepted_owners', 'reused_complete_selected_owners',
                'worker_exit_code', 'all_selected_owners_accepted')}
            record.update(evidence_bindings=META['attempt-%05d' % index],
                original_requested_targets=result['targets'], failed_modules=list(result['failures']),
                not_accepted_modules=result['targets'][1:], not_started_modules=result['targets'][2:],
                dispatch_error=result.get('dispatch_error'),
                original_final_stock_readiness={'recorded': index == 0})
            runs.append((result, {}, record))
        owner = {'source_commit': c.S, 'owned_count': 27, 'public_count': 27,
                 'later_same_S_reuse_run': str(c.ROOT / c.S / 'runs/attempt-00001')}
        flat = c.flat_summary(runs, owner)
        old = json.loads(Path('/tmp/p15-r-publication/ALLK_Q_PUBLIC_ACCEPTANCE.json').read_text())
        self.assertEqual(set(old), set(flat) - {'later_same_source_reuse'})
        self.assertEqual(flat['owners'], {c.FAMILY: owner})
        self.assertEqual(flat['status'], 'ORIGINAL_S_ACCEPTED_PREFIX_REVALIDATED_WITHOUT_EXECUTION')
        for key in ('original_result', 'original_worker_result'):
            self.assertEqual(set(flat[key]), {'bytes', 'sha256'})
        self.assertTrue(flat['original_final_stock_readiness']['recorded'])
        self.assertFalse(flat['later_same_source_reuse']['original_final_stock_readiness']['recorded'])

    def test_collector_has_only_read_operations(self):
        tree = ast.parse((HERE / 'collect_s_acceptance.py').read_text())
        calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call)]
        attrs = {n.func.attr for n in calls if isinstance(n.func, ast.Attribute)}
        self.assertFalse(attrs & {'write_bytes', 'write_text', 'mkdir', 'unlink', 'rename', 'replace',
                                  'save', 'write_frozen', 'run', 'Popen', 'check_call', 'system'})
        opens = [n for n in calls if isinstance(n.func, ast.Attribute) and n.func.attr == 'open']
        self.assertEqual([ast.literal_eval(n.args[0]) for n in opens], ['rb'])
        commands = [n for n in calls if isinstance(n.func, ast.Attribute) and n.func.attr == 'check_output']
        self.assertEqual(len(commands), 1)
        self.assertEqual([ast.literal_eval(x) for x in commands[0].args[0].elts[:2]], ['git', 'show'])
        self.assertIn('preflight', attrs)
        self.assertIn('require_completed_existing_owner', attrs)
        self.assertIn('acceptance_binding', attrs)

    def test_changed_published_reader_stops_before_exec(self):
        with patch.object(c.subprocess, 'check_output', return_value=b'changed'):
            with self.assertRaisesRegex(RuntimeError, 'published S reader/manifest differs'):
                c.collect()


if __name__ == '__main__':
    unittest.main(verbosity=2)
