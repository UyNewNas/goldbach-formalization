#!/usr/bin/env python3
"""Exercise report encoding and live capacity guards without recovery main."""
import ast
import gzip
import hashlib
import os
from pathlib import Path
import runpy
import tempfile
import unittest

FOLDER = Path(__file__).resolve().parent
DRIVER = Path(os.environ.get(
    'P25_STORAGE_TEST_DRIVER', str(FOLDER / 'recover_p2_sparse_worktree_round4_v2.py')))
NS = runpy.run_path(str(DRIVER))
MAIN = next(node for node in ast.parse(DRIVER.read_text()).body
            if isinstance(node, ast.FunctionDef) and node.name == 'main')
BODY = next(node for node in MAIN.body if isinstance(node, ast.Try)).body
RAW_JSON = (b'{\n  "a": [\n    null,\n    true,\n    17\n  ],\n'
            b'  "z": "\\u0394\\n/x[1]"\n}\n')
VALUE = {'z': '\u0394\n/x[1]', 'a': [None, True, 17]}


def execute_nodes(nodes, values):
    environment = dict(NS)
    environment.update(values)
    code = compile(ast.Module(body=nodes, type_ignores=[]), str(DRIVER), 'exec')
    exec(code, environment)
    return environment


class CompressedDiagnosticChecks(unittest.TestCase):
    def writer(self):
        self.assertTrue('write_compressed_diagnostic' in NS,
                        'Large reports must use the lossless bounded writer')
        return NS['write_compressed_diagnostic']

    def test_each_large_report_preserves_exact_original_json_bytes(self):
        writer = self.writer()
        with tempfile.TemporaryDirectory() as directory:
            for name in ('PROTECTED_PATHS.json', 'PATH_RESOLUTIONS_BEFORE.json'):
                with self.subTest(name=name):
                    path = Path(directory) / name
                    writer(path, VALUE)
                    self.assertFalse(path.exists())
                    stored = path.with_name(name + '.gz').read_bytes()
                    self.assertEqual(gzip.decompress(stored), RAW_JSON)

    def test_metadata_binds_both_stored_and_recovered_bytes(self):
        writer = self.writer()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'PROTECTED_PATHS.json'
            metadata = writer(path, VALUE)
            stored = path.with_name(path.name + '.gz').read_bytes()
            self.assertEqual(metadata, {
                'compression': 'gzip',
                'filename': 'PROTECTED_PATHS.json.gz',
                'bytes': len(stored),
                'sha256': hashlib.sha256(stored).hexdigest(),
                'uncompressed_filename': 'PROTECTED_PATHS.json',
                'uncompressed_bytes': len(RAW_JSON),
                'uncompressed_sha256': hashlib.sha256(RAW_JSON).hexdigest(),
            })

    def test_equal_values_have_equal_compressed_bytes_without_timestamp(self):
        writer = self.writer()
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            a = Path(first) / 'PROTECTED_PATHS.json'
            b = Path(second) / 'PROTECTED_PATHS.json'
            first_metadata = writer(a, VALUE)
            second_metadata = writer(b, VALUE)
            self.assertEqual(first_metadata, second_metadata)
            stored = a.with_name(a.name + '.gz').read_bytes()
            self.assertEqual(stored, b.with_name(b.name + '.gz').read_bytes())
            self.assertEqual(stored[4:8], b'\x00\x00\x00\x00')

    def test_other_reports_are_rejected_before_any_write(self):
        writer = self.writer()
        with tempfile.TemporaryDirectory() as directory:
            for name in ('CURRENT_AUDIT_RECEIPTS.json', 'LAKE_BEFORE.json', 'RESULT.json',
                         'PROTECTED_PATHS.json.gz', 'protected_paths.json'):
                with self.subTest(name=name):
                    with self.assertRaises(RuntimeError):
                        writer(Path(directory) / name, VALUE)
            self.assertEqual(list(Path(directory).iterdir()), [])

    def test_normal_report_writer_still_emits_original_json(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'LAKE_BEFORE.json'
            NS['write_json'](path, VALUE)
            self.assertEqual(path.read_bytes(), RAW_JSON)
            self.assertEqual(sorted(p.name for p in Path(directory).iterdir()), [path.name])


class CapacityGuardChecks(unittest.TestCase):
    def selection(self, free, allocated, extra_size):
        start = next(i for i, node in enumerate(BODY)
                     if isinstance(node, ast.Assign)
                     and any(isinstance(target, ast.Name) and target.id == 'extras'
                             for target in node.targets))
        # Execute the actual initialization, selection loop and following guard.
        return execute_nodes(BODY[start:start + 3], {
            'free_before': free, 'allocated': allocated,
            'extra_candidates': [(extra_size, 'ImbalancedChen/unused.lean')],
            'excluded': set(), 'rows': {'ImbalancedChen/unused.lean': {'oid': 'fixture'}},
        })

    def guard(self, message, values):
        nodes = [node for node in ast.walk(MAIN)
                 if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                 and isinstance(node.value.func, ast.Name) and node.value.func.id == 'require'
                 and len(node.value.args) == 2 and isinstance(node.value.args[1], ast.Constant)
                 and node.value.args[1].value == message]
        self.assertEqual(len(nodes), 1, 'A live capacity guard must enforce this boundary')
        return execute_nodes(nodes, values)

    def test_selection_keeps_next_preparation_reserve_after_write_buffer(self):
        result = self.selection(0, 1090519040, 16777216)
        self.assertEqual(result['allocated'], 1107296256)
        self.assertEqual(result['excluded'], {'ImbalancedChen/unused.lean'})

    def test_selection_rejects_one_byte_short_of_total_budget(self):
        with self.assertRaises(RuntimeError):
            self.selection(0, 1090519040, 16777215)

    def test_fresh_pre_mutation_guard_retains_reserve_or_stops(self):
        message = 'The completed preflight evidence cannot retain the next preparation reserve'
        with self.assertRaises(RuntimeError):
            self.guard(message, {'state': {'disk_free_after_evidence_before_mutation': 1090519039},
                                 'allocated': 0})
        self.guard(message, {'state': {'disk_free_after_evidence_before_mutation': 1090519040},
                             'allocated': 0})

    def test_post_recovery_guard_retains_reserve_or_stops(self):
        message = 'Recovery did not retain the next preparation reserve; no compile is authorized by this result'
        with self.assertRaises(RuntimeError):
            self.guard(message, {'free_after': 1090519039})
        self.guard(message, {'free_after': 1090519040})

    def test_original_one_gib_guards_still_reject_shortfall(self):
        for message, variable in [
            ('The completed preflight evidence consumed the remaining safe recovery margin', 'pre'),
            ('Recovery did not reach the unchanged 1 GiB gate; no compile is authorized by this result', 'post'),
        ]:
            with self.subTest(guard=variable):
                low = ({'state': {'disk_free_after_evidence_before_mutation': 1073741823}, 'allocated': 0}
                       if variable == 'pre' else {'free_after': 1073741823})
                with self.assertRaises(RuntimeError):
                    self.guard(message, low)


if __name__ == '__main__':
    unittest.main()
