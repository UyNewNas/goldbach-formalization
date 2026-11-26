"""Local wrapper checks only; no Lean, checkout or cloud job is invoked."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
RUNNER = ROOT / 'docs/verification/20261126-p2-5-resumed/run_p2_round4.py'
ROUND2 = ROOT / 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'


class ResumeGuards(unittest.TestCase):
    def setUp(self):
        self.assertTrue(RUNNER.is_file(), 'round-4 wrapper has not been implemented')
        spec = importlib.util.spec_from_file_location('p25_round4', RUNNER)
        self.runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.runner)
        self.graph = json.loads((ROUND2 / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
        self.targets = json.loads((ROUND2 / 'CONTINUATION_AUDIT_TARGETS.json').read_text())
        self.selection = json.loads((Path(__file__).parent / 'SOURCE_SELECTION.json').read_text())

    def test_same_scope_with_only_four_changed_audit_targets_prioritized(self):
        graph, ordered = self.runner.validated_graph(self.graph, self.targets, self.selection)
        self.assertEqual(len(graph['modules']), 377)
        self.assertEqual(graph['roots'], self.graph['roots'])
        self.assertEqual(len(ordered), 69)
        self.assertEqual(set(ordered), set(self.targets['modules']))
        self.assertEqual(ordered[:4], self.selection['changed_audit_targets'])
        changed = {m for m, row in graph['modules'].items()
                   if row['sha256'] != self.graph['modules'][m]['sha256']}
        self.assertEqual(changed, {r['module'] for r in self.selection['sources']})
        self.assertEqual(len(changed), 8)

    def test_rejects_duplicate_audit_target_and_missing_repair(self):
        bad_targets = copy.deepcopy(self.targets)
        bad_targets['modules'][0] = bad_targets['modules'][1]
        with self.assertRaises(RuntimeError):
            self.runner.validated_graph(self.graph, bad_targets, self.selection)
        bad_selection = copy.deepcopy(self.selection)
        bad_selection['sources'].pop()
        with self.assertRaises(RuntimeError):
            self.runner.validated_graph(self.graph, self.targets, bad_selection)

    def test_rejects_wrong_repair_preimage(self):
        bad = copy.deepcopy(self.selection)
        bad['sources'][0]['before_sha256'] = '0' * 64
        with self.assertRaises(RuntimeError):
            self.runner.validated_graph(self.graph, self.targets, bad)

    def test_source_guard_detects_changed_bytes_and_changed_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'ImbalancedChen/Example.lean'
            source.parent.mkdir()
            source.write_text('import ImbalancedChen.Dependency\n')
            graph = {'modules': {'ImbalancedChen.Example': {
                'source': 'ImbalancedChen/Example.lean',
                'sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                'imports': ['ImbalancedChen.Dependency']}}}
            parse = lambda text: [line.split()[1] for line in text.splitlines()
                                  if line.startswith('import ')]
            self.runner.verify_sources(root, graph, parse)
            source.write_text('import ImbalancedChen.Other\n')
            with self.assertRaises(RuntimeError):
                self.runner.verify_sources(root, graph, parse)
            graph['modules']['ImbalancedChen.Example']['sha256'] = hashlib.sha256(source.read_bytes()).hexdigest()
            with self.assertRaises(RuntimeError):
                self.runner.verify_sources(root, graph, parse)

    def test_prior_result_must_keep_round3_counts_and_completed_origin(self):
        rows = json.loads((ROOT / 'docs/verification/20261126-p2-5-resumed/P2_ROUND3_ORIGINAL_FAILURES.json').read_text())
        previous = copy.deepcopy(rows[-1])
        previous['ended_utc'] = '2026-11-26T00:00:00+00:00'
        self.runner.validate_previous_result(previous, self.graph['roots'], self.targets['modules'])
        previous['audit_summary']['accepted'] = 69
        with self.assertRaises(RuntimeError):
            self.runner.validate_previous_result(previous, self.graph['roots'], self.targets['modules'])


if __name__ == '__main__':
    unittest.main()
