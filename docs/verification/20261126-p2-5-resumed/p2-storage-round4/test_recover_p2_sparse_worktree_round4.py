#!/usr/bin/env python3
"""Local structural/provenance checks; never execute recovery main or mutate Git."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import posixpath
import runpy
import subprocess
import unittest

ROOT = Path(__file__).resolve().parents[4]
FOLDER = Path(__file__).resolve().parent
DRIVER = FOLDER / 'recover_p2_sparse_worktree_round4.py'
NS = runpy.run_path(str(DRIVER))
OLD = ROOT / NS['ADAPTED_FROM']
OLD_NS = runpy.run_path(str(OLD))
ROUND4 = runpy.run_path(str(ROOT / NS['ROUND4_RUNNER']))
BASE_GRAPH = json.loads((ROOT / NS['FOLDER'] / 'CONTINUATION_SOURCE_CLOSURE.json').read_text())
TARGETS = json.loads((ROOT / NS['FOLDER'] / 'CONTINUATION_AUDIT_TARGETS.json').read_text())
SELECTION = json.loads((ROOT / NS['ROUND4_SELECTION']).read_text())
GRAPH, _ = ROUND4['validated_graph'](BASE_GRAPH, TARGETS, SELECTION)
RESULT_PATH = ROOT / 'docs/verification/20261126-p2-5-resumed/P2_ROUND4_RESULT.json'
RESULT = json.loads(RESULT_PATH.read_text())
REQUIRED = json.loads((FOLDER / 'REQUIRED_PATHS.json').read_text())


class StorageAdapterChecks(unittest.TestCase):
    def test_actual_completed_result_and_negative_preservation_checks(self):
        self.assertEqual(hashlib.sha256(RESULT_PATH.read_bytes()).hexdigest(), NS['COMPLETED_RESULT_SHA'])
        NS['validate_completed_round4'](RESULT, GRAPH, TARGETS['modules'])
        for key in ['source_after_matches', 'gate_after_matches', 'runner_after_matches',
                    'external_after_matches', 'head_after_matches', 'history_after_matches',
                    'baseline_after_matches']:
            bad = copy.deepcopy(RESULT)
            bad[key] = False
            with self.assertRaises(RuntimeError):
                NS['validate_completed_round4'](bad, GRAPH, TARGETS['modules'])
        bad = copy.deepcopy(RESULT)
        bad['accepted'] = True
        with self.assertRaises(RuntimeError):
            NS['validate_completed_round4'](bad, GRAPH, TARGETS['modules'])

    def test_round4_graph_reconstructs_eight_postimages(self):
        changed = {m for m in GRAPH['modules'] if GRAPH['modules'][m] != BASE_GRAPH['modules'][m]}
        self.assertEqual(changed, {row['module'] for row in SELECTION['sources']})
        self.assertEqual(len(changed), 8)
        self.assertEqual(len(GRAPH['modules']), 377)
        self.assertEqual(len(TARGETS['modules']), 69)
        self.assertEqual(RESULT['changed_sources'], SELECTION['sources'])

    def test_exact_397_required_inputs_against_resolved_publication(self):
        expected = json.loads((OLD.parent / 'STATIC_REQUIRED_PATHS.json').read_text())
        self.assertEqual(len(expected), 394)
        for row in SELECTION['sources']:
            self.assertEqual(expected[row['production_path']], row['before_sha256'])
            expected[row['production_path']] = row['after_sha256']
        expected.update({NS['ADAPTED_FROM']: NS['ADAPTED_FROM_SHA'],
                         NS['ROUND4_RUNNER']: NS['ROUND4_RUNNER_SHA'],
                         NS['ROUND4_SELECTION']: NS['ROUND4_SELECTION_SHA']})
        self.assertEqual(REQUIRED, expected)
        self.assertEqual(len(REQUIRED), NS['REQUIRED_COUNT'])
        self.assertEqual(NS['canonical'](REQUIRED), NS['REQUIRED_SHA'])
        raw = subprocess.check_output(['git', 'ls-tree', '-rz', '--full-tree', NS['PUBLICATION']], cwd=ROOT)
        entries = {}
        for item in raw.split(b'\0'):
            if item:
                meta, path = item.split(b'\t', 1)
                mode, _, oid = meta.decode().split()
                entries[path.decode()] = (mode, oid)
        blobs = {}
        links = 0
        for name, expected_hash in REQUIRED.items():
            path, visited = name, set()
            while True:
                self.assertNotIn(path, visited)
                visited.add(path)
                mode, oid = entries[path]
                if oid not in blobs:
                    blobs[oid] = subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=ROOT)
                data = blobs[oid]
                if mode != '120000':
                    self.assertEqual(hashlib.sha256(data).hexdigest(), expected_hash, name)
                    break
                path = posixpath.normpath(posixpath.join(posixpath.dirname(path), data.decode()))
                self.assertFalse(path.startswith('../'))
            links += len(visited) > 1
        self.assertEqual(links, 15)

    def test_all_original_inventory_and_path_helpers_unchanged(self):
        old = ast.parse(OLD.read_text())
        new = ast.parse(DRIVER.read_text())
        old_top = {n.name: n for n in old.body if isinstance(n, ast.FunctionDef)}
        new_top = {n.name: n for n in new.body if isinstance(n, ast.FunctionDef)}
        helpers = set(old_top) - {'main'}
        self.assertEqual(len(helpers), 17)
        for name in helpers:
            self.assertEqual(ast.dump(old_top[name]), ast.dump(new_top[name]), name)
        nested = lambda node: {n.name: n for n in ast.walk(node)
                               if isinstance(n, ast.FunctionDef) and n is not node}
        old_nested, new_nested = nested(old_top['main']), nested(new_top['main'])
        self.assertEqual(set(old_nested), set(new_nested))
        self.assertEqual(len(old_nested), 4)
        for name in old_nested:
            self.assertEqual(ast.dump(old_nested[name]), ast.dump(new_nested[name]), name)

    def test_original_omission_mutation_and_postflight_body_unchanged(self):
        old, new = OLD.read_text(), DRIVER.read_text()
        for start, end in [
            ('        def is_protected(path):', '        state.update(required_path_count='),
            ('        if not args.apply:', None),
        ]:
            a = old[old.index(start):old.index(end) if end else None]
            b = new[new.index(start):new.index(end) if end else None]
            a = a.replace('# The original 394 files,', '# The 397 pinned files,')
            self.assertEqual(a, b)
        self.assertIn("parser.add_argument('--apply', action='store_true')", new)

    def test_thresholds_prefixes_historical_evidence_and_topology_unchanged(self):
        for key in ['ROOT', 'COMMON', 'PRIVATE', 'MIN_FREE', 'WRITE_BUFFER', 'BASE_CANDIDATE_PREFIXES',
                    'EXTRA_SOURCE_PREFIX', 'FAILED', 'FAILED_PINS', 'PREVIOUS', 'STATIC_KEEP',
                    'ARCHIVE', 'ARCHIVE_SHA', 'RUNNER', 'RUNNER_SHA']:
            self.assertEqual(NS[key], OLD_NS[key], key)
        self.assertEqual(NS['FAILED_PUBLICATION'], OLD_NS['PUBLICATION'])
        self.assertEqual(NS['FAILED_TREE'], OLD_NS['TREE'])
        self.assertEqual(NS['MIN_FREE'], 1073741824)

    def test_current_records_gate_structurally_without_inventing_actual_records(self):
        # This synthetic mapping exercises only the gate. It is never persisted
        # as remote evidence and grants no acceptance or storage-recovery credit.
        successful = set(GRAPH['modules']) - set(RESULT['compile_summary']['failed_or_blocked'])
        fixture = {name: {'exit_code': 0, 'source': GRAPH['modules'][name]['source'],
                          'source_sha256': GRAPH['modules'][name]['sha256']} for name in successful}
        self.assertEqual(NS['validate_current_records'](fixture, GRAPH, RESULT), successful)
        one = next(iter(successful))
        changed = copy.deepcopy(fixture)
        changed[one]['source_sha256'] = '0' * 64
        with self.assertRaises(RuntimeError):
            NS['validate_current_records'](changed, GRAPH, RESULT)
        missing = copy.deepcopy(fixture)
        del missing[one]
        with self.assertRaises(RuntimeError):
            NS['validate_current_records'](missing, GRAPH, RESULT)

    def test_future_round5_paths_are_not_current_exact_omission_candidates(self):
        future = ['docs/verification/20261126-p2-5-resumed/run_p2_round5.py',
                  'docs/source-only/20261126-p2-5-round5-repairs/SOURCE_SELECTION.json']
        for path in future:
            probe = subprocess.run(['git', 'cat-file', '-e', NS['PUBLICATION'] + ':' + path],
                                   cwd=ROOT, capture_output=True)
            self.assertNotEqual(probe.returncode, 0)
        text = DRIVER.read_text()
        self.assertIn("rules = ('/*\\n' + ''.join('!/' + literal_pattern(path)", text)
        self.assertIn('for path in sorted(excluded)', text)
        self.assertIn("if path.startswith(BASE_CANDIDATE_PREFIXES) and not is_protected(path)", text)


if __name__ == '__main__':
    unittest.main()
