"""Offline resume guards against actual receipts and committed source bytes."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import posixpath
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
PACKAGE = Path(__file__).resolve().parent
RESUMED = ROOT / 'docs/verification/20261126-p2-5-resumed'
ROUND2 = ROOT / 'docs/verification/20261126-p2-5-continuation/p2-round2-incremental'


def module(path, name):
    if not path.is_file():
        raise AssertionError('Required wrapper is not implemented: ' + str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


class ResumeGuards(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.runner = module(RESUMED / 'run_p2_round5.py', 'p25_round5_test')
        cls.legacy = module(RESUMED / 'run_p2_round4.py', 'p25_round4_test')
        cls.base = json.loads((ROUND2 / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
        cls.targets = json.loads((ROUND2 / 'CONTINUATION_AUDIT_TARGETS.json').read_text())
        cls.selection = json.loads((PACKAGE / 'SOURCE_SELECTION.json').read_text())
        cls.prior_selection = json.loads((ROOT / cls.runner.ROUND4_SELECTION).read_text())
        cls.previous = json.loads((RESUMED / 'P2_ROUND4_RESULT.json').read_text())
        cls.prior, _ = cls.legacy.validated_graph(cls.base, cls.targets, cls.prior_selection)

    def test_actual_receipt_and_control_pins(self):
        for path, expected in [
            (RESUMED / 'P2_ROUND4_RESULT.json', self.runner.PRIOR_RESULT_SHA),
            (ROOT / self.runner.ROUND4_RUNNER, self.runner.ROUND4_RUNNER_SHA),
            (ROOT / self.runner.ROUND4_SELECTION, self.runner.ROUND4_SELECTION_SHA),
            (ROOT / self.runner.HELPER, self.runner.HELPER_SHA),
            (PACKAGE / 'SOURCE_SELECTION.json', self.runner.SELECTION_SHA),
        ]:
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), expected)
        self.assertEqual(self.runner.PREVIOUS, self.previous['source_commit'])
        self.assertEqual(self.runner.MIN_FREE_BYTES, 1073741824)

    def test_prior_graph_matches_all_resolved_committed_sources(self):
        raw = subprocess.check_output(['git', 'ls-tree', '-r', '-z', self.runner.PREVIOUS], cwd=ROOT)
        tree = {}
        for entry in raw.split(b'\0'):
            if entry:
                metadata, path = entry.split(b'\t', 1)
                mode, _, oid = metadata.decode().split()
                tree[path.decode()] = (mode, oid)
        cache = {}

        def committed(path, visiting=()):
            self.assertNotIn(path, visiting, 'Committed symlink cycle')
            self.assertFalse(path.startswith('../') or posixpath.isabs(path))
            mode, oid = tree[path]
            if oid not in cache:
                cache[oid] = subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=ROOT)
            data = cache[oid]
            if mode == '120000':
                target = posixpath.normpath(posixpath.join(posixpath.dirname(path), data.decode()))
                return committed(target, (*visiting, path))
            return data

        sys.path.insert(0, str(ROOT / 'verification/part2'))
        from inspect_winner9_owner_native import imports
        symlinks = 0
        for name, row in self.prior['modules'].items():
            source = row['source']
            symlinks += tree[source][0] == '120000'
            data = committed(source)
            self.assertEqual(hashlib.sha256(data).hexdigest(), row['sha256'], name)
            self.assertEqual([x for x in imports(data.decode()) if x.startswith('ImbalancedChen.')], row['imports'], name)
        self.assertEqual(len(self.prior['modules']), 377)
        self.assertEqual(symlinks, 15)
        self.assertEqual(sum(self.prior['modules'][m]['sha256'] != r['sha256']
                             for m, r in self.base['modules'].items()), 8)

    def test_only_six_changes_and_original_69_audit_targets(self):
        graph, ordered = self.runner.validated_graph(self.prior, self.targets, self.selection)
        changed = {m for m, row in graph['modules'].items()
                   if row['sha256'] != self.prior['modules'][m]['sha256']}
        self.assertEqual(changed, {r['module'] for r in self.selection['changed_modules']})
        self.assertEqual(len(changed), 6)
        self.assertEqual(len(graph['modules']), 377)
        self.assertEqual(graph['roots'], self.previous['compile_roots'])
        self.assertEqual(len(ordered), 69)
        self.assertEqual(set(ordered), set(self.targets['modules']))
        self.assertEqual(ordered[:2], self.selection['changed_audit_targets'])
        self.assertEqual(len(self.selection['changed_dependency_only_modules']), 4)

    def test_rejects_unadvanced_round2_graph(self):
        with self.assertRaisesRegex(RuntimeError, 'preimage differs'):
            self.runner.validated_graph(self.base, self.targets, self.selection)

    def test_rejects_invalid_repair_identity_or_scope(self):
        for mutation in ['missing', 'duplicate', 'preimage', 'imports', 'options']:
            bad = copy.deepcopy(self.selection)
            rows = bad['changed_modules']
            if mutation == 'missing':
                rows.pop()
            elif mutation == 'duplicate':
                rows[1] = copy.deepcopy(rows[0])
            elif mutation == 'preimage':
                rows[0]['before_sha256'] = '0' * 64
            else:
                rows[0][mutation + '_unchanged'] = False
            with self.subTest(mutation=mutation), self.assertRaises(RuntimeError):
                self.runner.validated_graph(self.prior, self.targets, bad)

    def test_rejects_duplicate_audit_target(self):
        bad = copy.deepcopy(self.targets)
        bad['modules'][0] = bad['modules'][1]
        with self.assertRaises(RuntimeError):
            self.runner.validated_graph(self.prior, bad, self.selection)

    def test_actual_completed_prior_result_and_rejection_guards(self):
        self.runner.validate_previous_result(self.previous, self.prior['roots'], self.targets['modules'], self.prior_selection)
        for change in ['origin', 'normal_count', 'owned_count', 'incomplete', 'postflight', 'prior_repairs']:
            bad = copy.deepcopy(self.previous)
            if change == 'origin':
                bad['source_commit'] = '0' * 40
            elif change == 'normal_count':
                bad['compile_summary']['successful_closure'] = 325
            elif change == 'owned_count':
                bad['audit_summary']['accepted'] = 38
            elif change == 'incomplete':
                bad['ended_utc'] = None
            elif change == 'postflight':
                bad['history_after_matches'] = False
            else:
                bad['changed_sources'][0]['after_sha256'] = '0' * 64
            with self.subTest(change=change), self.assertRaises(RuntimeError):
                self.runner.validate_previous_result(bad, self.prior['roots'], self.targets['modules'], self.prior_selection)

    def test_source_guard_follows_internal_symlink_and_rejects_drift_or_escape(self):
        with tempfile.TemporaryDirectory() as directory, tempfile.TemporaryDirectory() as outside:
            root = Path(directory)
            source = root / 'ImbalancedChen/Example.lean'
            target = root / 'docs/Example.lean'
            source.parent.mkdir()
            target.parent.mkdir()
            target.write_text('import ImbalancedChen.Dependency\n')
            source.symlink_to('../docs/Example.lean')
            row = {'source': 'ImbalancedChen/Example.lean',
                   'sha256': hashlib.sha256(target.read_bytes()).hexdigest(),
                   'imports': ['ImbalancedChen.Dependency']}
            graph = {'modules': {'ImbalancedChen.Example': row}}
            parse = lambda text: [line.split()[1] for line in text.splitlines() if line.startswith('import ')]
            self.runner.verify_sources(root, graph, parse)
            target.write_text('import ImbalancedChen.Other\n')
            with self.assertRaises(RuntimeError):
                self.runner.verify_sources(root, graph, parse)
            row['sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()
            with self.assertRaises(RuntimeError):
                self.runner.verify_sources(root, graph, parse)
            source.unlink()
            external = Path(outside) / 'Example.lean'
            external.write_bytes(target.read_bytes())
            source.symlink_to(external)
            with self.assertRaises(RuntimeError):
                self.runner.verify_sources(root, graph, parse)


if __name__ == '__main__':
    unittest.main()
