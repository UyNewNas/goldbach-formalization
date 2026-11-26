#!/usr/bin/env python3
"""Offline P3 policy and actual-history checks; never execute storage recovery."""
import ast
import copy
import gzip
import hashlib
import json
import os
from pathlib import Path
import runpy
import subprocess
import tempfile
import types
import unittest

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
RESUMED = HERE.parent
DRIVER = Path(os.environ.get('P25_STORAGE_TEST_DRIVER', str(HERE / 'recover_p3_sparse_worktree.py')))
BASE = RESUMED / 'p2-storage-round4-v3/recover_p2_sparse_worktree_round4_v3.py'
NS = runpy.run_path(str(DRIVER))
V6 = types.SimpleNamespace(**runpy.run_path(str(RESUMED / 'run_cell00_four_consumers_v6.py')))
ACTUAL004 = json.loads((RESUMED / 'consumer-attempt004/RESULT.json').read_text())
ACTUAL005 = json.loads((RESUMED / 'consumer-attempt005/RESULT.json').read_text())
EVIDENCE = RESUMED / 'consumer-v6-disk-preflight'
CAPACITY = json.loads((EVIDENCE / 'OWNED_FRONTIERS_CAPACITY.json').read_text())
MAIN = next(n for n in ast.parse(DRIVER.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'main')
BODY = next(n for n in MAIN.body if isinstance(n, ast.Try)).body
PROTECT = next(n for n in BODY if isinstance(n, ast.FunctionDef) and n.name == 'protect')
START = next(i for i, n in enumerate(BODY) if isinstance(n, ast.Assign)
             and any(isinstance(t, ast.Name) and t.id == 'protected_names' for t in n.targets))
END = next(i for i, n in enumerate(BODY) if isinstance(n, ast.FunctionDef) and n.name == 'allocated_bytes')
SELECT = next(n for n in BODY if isinstance(n, ast.Assign)
              and any(isinstance(t, ast.Name) and t.id == 'base_omissions' for t in n.targets))


def execute(nodes, environment):
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(DRIVER), 'exec'), environment)


class P3IdentityAndHistory(unittest.TestCase):
    def test_exact_p3_topology_publication_and_bound_default_arguments(self):
        self.assertEqual(NS['ROOT'], Path('/workspace/p25-q96-20261125'))
        self.assertEqual(NS['COMMON'], Path('/workspace/goldbach-p3/.git'))
        self.assertEqual(NS['PRIVATE'], Path('/workspace/goldbach-p3/.git/worktrees/p25-q96-20261125'))
        self.assertEqual(NS['PUBLICATION'], 'be20f0b050bb787ecb98f9afdd9b6a386706f45a')
        self.assertEqual(NS['TREE'], 'a8ea84a6d46d9567aa3e0e7cbfe3016c6ab18acc')
        self.assertEqual(NS['git'].__defaults__[0], NS['ROOT'])
        self.assertEqual(NS['text'].__defaults__[0], NS['ROOT'])
        self.assertEqual(NS['V6_PUBLICATION'], '4653b261828f127ba0b5082eaf1106a3fea09d46')
        self.assertEqual(NS['EXECUTED_V6'], Path('/workspace/p25-four-consumers-v6-20261126.py'))
        self.assertEqual(NS['ENV']['GIT_NO_LAZY_FETCH'], '1')

    def test_eighteen_general_and_four_nested_helpers_are_exact_copies(self):
        def functions(path):
            return {n.name: ast.dump(n) for n in ast.parse(path.read_text()).body if isinstance(n, ast.FunctionDef)}
        old, new = functions(BASE), functions(DRIVER)
        names = set(old) - {'validate_completed_round4', 'validate_current_records', 'main'}
        self.assertEqual(len(names), 18)
        self.assertTrue(names <= new.keys())
        for name in names:
            self.assertEqual(old[name], new[name], name)
        old_main = next(n for n in ast.parse(BASE.read_text()).body if isinstance(n, ast.FunctionDef) and n.name == 'main')
        old_nested = {n.name: ast.dump(n) for n in ast.walk(old_main) if isinstance(n, ast.FunctionDef) and n.name != 'main'}
        new_nested = {n.name: ast.dump(n) for n in ast.walk(MAIN) if isinstance(n, ast.FunctionDef) and n.name != 'main'}
        self.assertEqual(set(old_nested), {'protect', 'is_protected', 'allocated_bytes', 'literal_pattern'})
        for name in old_nested:
            self.assertEqual(old_nested[name], new_nested[name], name)

    def test_exact_failed_history_is_validated_without_relabeling(self):
        result = NS['validate_consumer_history'](ACTUAL005, ACTUAL004, V6)
        self.assertEqual(result['frozen_input_count'], 16646)
        self.assertEqual(result['source_graph_count'], 45)
        self.assertEqual(result['accepted_dependency_count'], 40)
        self.assertEqual(result['accepted_decoded_owned_count'], 4)
        self.assertFalse(result['aggregate_accepted'])
        self.assertFalse(ACTUAL004['accepted'])
        self.assertFalse(ACTUAL005['accepted'])

    def test_changed_frozen_hash_is_rejected_even_with_same_count(self):
        changed = copy.deepcopy(ACTUAL005)
        key = next(iter(changed['frozen_inputs']))
        changed['frozen_inputs'][key] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'frozen'):
            NS['validate_consumer_history'](changed, ACTUAL004, V6)

    def test_changed_source_graph_is_rejected_even_with_same_count(self):
        changed, old = copy.deepcopy(ACTUAL005), copy.deepcopy(ACTUAL004)
        module = 'ImbalancedChen.P2OriginalSaving16OriginalInput'
        for value in [changed, old]:
            value['source_graph'][module]['source_sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'source graph'):
            NS['validate_consumer_history'](changed, old, V6)

    def test_original_decoded_acceptance_cannot_be_relabelled(self):
        changed = copy.deepcopy(ACTUAL005)
        changed['modules'][V6.DECODED]['object']['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'Decoded'):
            NS['validate_consumer_history'](changed, ACTUAL004, V6)
        changed = copy.deepcopy(ACTUAL005)
        changed['accepted'] = True
        with self.assertRaisesRegex(RuntimeError, 'failed aggregate'):
            NS['validate_consumer_history'](changed, ACTUAL004, V6)

    def test_every_frozen_path_and_the_new_failure_runner_are_bound(self):
        files = NS['history_files'](ACTUAL005, ACTUAL004)
        self.assertEqual(len(files), 16649)
        for path, expected in ACTUAL005['frozen_inputs'].items():
            self.assertEqual(files[path], expected)
        for path, expected in ACTUAL004['frozen_inputs'].items():
            self.assertEqual(files[path], expected)
        self.assertEqual(files[str(NS['FAILED005'])], NS['FAILED005_SHA'])
        self.assertEqual(files[str(NS['EXECUTED_V6'])], NS['V6_RUNNER_SHA'])
        self.assertEqual(files[ACTUAL005['exception_log']['path']], ACTUAL005['exception_log']['sha256'])
        for row in ACTUAL005['source_graph'].values():
            self.assertEqual(files[str(NS['ROOT'] / row['path'])], row['source_sha256'])

    def test_conflicting_historical_artifact_hash_is_rejected(self):
        changed = copy.deepcopy(ACTUAL005)
        changed['runner']['sha256'] = '0' * 64
        with self.assertRaisesRegex(RuntimeError, 'conflicting'):
            NS['history_files'](changed, ACTUAL004)

    def test_actual_receipt_and_inventory_files_are_exact(self):
        pins = {
            RESUMED / 'consumer-attempt004/RESULT.json': '2c8f7b252d2e42f8ac09a6be391401258b0ed8fda1da57dd50cc7269f50b193a',
            RESUMED / 'consumer-attempt005/RESULT.json': 'bc26ddfa2b6a06ce4935430f6bedaf2419c7a1033723c98efe499f24116fdf88',
            EVIDENCE / 'RESOURCE_TOPOLOGY.json': 'd27c6eb710627a30f709b7ecc2d4bc66cd88a96ed227ca27a0b2f9f27572670c',
            EVIDENCE / 'OWNED_FRONTIERS_CAPACITY.json': '9876a9a961d666e27118398195985e773d41e0139df672fcdf8434f773129c3b',
            EVIDENCE / 'TASK_STDOUT.log': 'fd21f0403ea10e143cfa2a0b7ffe0db9d3c3ce982b646026093173c44f35530a',
        }
        for path, expected in pins.items():
            self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), expected, str(path))
        self.assertEqual(NS['canonical'](CAPACITY['eligible']), '2c878b80c078333943049aefffd9bb6ce5374f868bc62bf46fd5a9a52dd578bd')
        self.assertEqual(sum(row['allocated_bytes'] for row in CAPACITY['eligible']), 193220608)
        self.assertEqual(len(CAPACITY['eligible']), 1278)
        self.assertFalse(CAPACITY['mutation_started'])

    def test_all_inventory_git_blobs_and_45_source_rows_match_actual_publication(self):
        raw = subprocess.check_output(['git', 'ls-tree', '-rz', NS['PUBLICATION']], cwd=REPO, env=NS['ENV'])
        rows = {}
        for item in raw.split(b'\0'):
            if item:
                header, path = item.split(b'\t', 1)
                mode, kind, oid = header.decode().split()
                rows[os.fsdecode(path)] = (mode, kind, oid)
        for row in CAPACITY['eligible']:
            self.assertEqual(rows[row['path']], ('100644', 'blob', row['git_blob_sha']))
        blob_lines = subprocess.check_output(
            ['git', 'cat-file', '--batch-check=%(objectname) %(objecttype) %(objectsize)'],
            input=(''.join(row['git_blob_sha'] + '\n' for row in CAPACITY['eligible'])).encode(),
            cwd=REPO, env=NS['ENV']).decode().splitlines()
        self.assertEqual(len(blob_lines), len(CAPACITY['eligible']))
        for row, line in zip(CAPACITY['eligible'], blob_lines):
            self.assertEqual(line, row['git_blob_sha'] + ' blob ' + str(row['bytes']))
        for spec in ACTUAL005['source_graph'].values():
            path = spec['path']
            for _ in range(32):
                mode, kind, oid = rows[path]
                raw = subprocess.check_output(['git', 'cat-file', 'blob', oid], cwd=REPO, env=NS['ENV'])
                if mode != '120000':
                    self.assertEqual(hashlib.sha256(raw).hexdigest(), spec['source_sha256'])
                    break
                path = os.path.normpath(os.path.join(os.path.dirname(path), raw.decode()))
            else:
                self.fail('Unresolved committed source link')


class NarrowCandidatePolicy(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        names = ['docs/evidence/owned-frontiers/free/data.json',
                 'docs/evidence/owned-frontiers/referenced_tree/nested/data.json',
                 'docs/evidence/owned-frontiers/referenced_file.json',
                 'docs/evidence/owned-frontiers/target.txt',
                 'docs/evidence/owned-frontiers/.gitattributes',
                 'docs/evidence/other/evidence.json', 'docs/source-only/unused/source.lean',
                 'ImbalancedChen/unused.lean', 'verification/parts/old.json']
        self.rows = {p: {'mode': '100644', 'oid': 'fixture'} for p in names}
        for name in names:
            p = self.root / name
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(b'fixture')
        alias = self.root / 'docs/source-only/used/link.txt'
        alias.parent.mkdir(parents=True)
        alias.symlink_to('../../evidence/owned-frontiers/target.txt')
        self.rows[str(alias.relative_to(self.root))] = {'mode': '120000', 'oid': 'link'}
        self.env = dict(NS, ROOT=self.root, rows=self.rows, protected={}, resolutions={})
        execute([PROTECT], self.env)
        protect = self.env['protect']
        protect(self.root / 'docs/evidence/owned-frontiers/referenced_tree', 'referenced directory', True)
        protect(self.root / 'docs/evidence/owned-frontiers/referenced_file.json', 'accepted receipt path', True)
        protect(alias, 'every tracked source-only link', True)
        execute(BODY[START:END] + [SELECT], self.env)

    def test_only_one_narrow_prefix_and_no_extra_source_fallback(self):
        self.assertEqual(NS['BASE_CANDIDATE_PREFIXES'], ('docs/evidence/owned-frontiers/',))
        self.assertNotIn('EXTRA_SOURCE_PREFIX', NS)
        self.assertEqual(self.env['base_omissions'], {'docs/evidence/owned-frontiers/free/data.json'})
        self.assertNotIn('extra_candidates', {n.id for n in ast.walk(MAIN) if isinstance(n, ast.Name)})

    def test_referenced_directory_symlink_target_and_metadata_are_protected(self):
        for name in ['docs/evidence/owned-frontiers/referenced_tree/nested/data.json',
                     'docs/evidence/owned-frontiers/referenced_file.json',
                     'docs/evidence/owned-frontiers/target.txt', 'docs/evidence/owned-frontiers/.gitattributes']:
            self.assertTrue(self.env['is_protected'](name), name)
            self.assertNotIn(name, self.env['base_omissions'])

    def test_capacity_snapshot_yields_exact_1278_and_keeps_eight_attributes(self):
        rows = {r['path']: {'mode': '100644', 'oid': r['git_blob_sha']} for r in CAPACITY['eligible']}
        rows.update({r['path']: {'mode': '100644', 'oid': 'metadata'} for r in CAPACITY['blocked']})
        env = dict(NS, ROOT=self.root, rows=rows, protected={})
        execute(BODY[START:END] + [SELECT], env)
        self.assertEqual(env['base_omissions'], {r['path'] for r in CAPACITY['eligible']})
        self.assertEqual(len(env['base_omissions']), 1278)
        self.assertTrue(all(env['is_protected'](r['path']) for r in CAPACITY['blocked']))


class CapacityAndOrdering(unittest.TestCase):
    def test_minimum_report_buffer_and_preparation_reserve_are_unchanged(self):
        self.assertEqual(NS['MIN_FREE'], 1073741824)
        self.assertEqual(NS['WRITE_BUFFER'], 16777216)
        self.assertEqual(NS['NEXT_PREPARATION_RESERVE'], 16777216)
        selection = next(n for n in BODY if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
                         and isinstance(n.value.func, ast.Name) and n.value.func.id == 'require'
                         and 'Safe published working copies' in ast.unparse(n))
        env = dict(NS, allocated=193220608, free_before=1025085440)
        execute([selection], env)
        env['free_before'] = NS['MIN_FREE'] + NS['WRITE_BUFFER'] + NS['NEXT_PREPARATION_RESERVE'] - env['allocated'] - 1
        with self.assertRaises(RuntimeError):
            execute([selection], env)

    def test_fresh_disk_loss_after_report_writes_blocks_mutation(self):
        guard = next(n for n in BODY if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
                     and 'completed preflight evidence cannot retain' in ast.unparse(n))
        env = dict(NS, state={'disk_free_after_evidence_before_mutation': NS['MIN_FREE'] - 193220608}, allocated=193220608)
        with self.assertRaisesRegex(RuntimeError, 'reserve'):
            execute([guard], env)
        env['state']['disk_free_after_evidence_before_mutation'] += NS['NEXT_PREPARATION_RESERVE']
        execute([guard], env)

    def test_only_two_reports_are_losslessly_compressed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            value = {'all_paths': ['first', 'second'], 'accepted': False}
            for name in NS['COMPRESSED_DIAGNOSTIC_REPORTS']:
                row = NS['write_compressed_diagnostic'](root / name, value)
                stored = (root / row['filename']).read_bytes()
                raw = (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()
                self.assertEqual(gzip.decompress(stored), raw)
                self.assertEqual(hashlib.sha256(raw).hexdigest(), row['uncompressed_sha256'])
                self.assertEqual(hashlib.sha256(stored).hexdigest(), row['sha256'])
            with self.assertRaises(RuntimeError):
                NS['write_compressed_diagnostic'](root / 'RESULT.json', value)

    def test_preflight_verifies_all_bound_files_before_sparse_mutation_and_after(self):
        text = ast.unparse(MAIN)
        first = text.index('validate_consumer_history(')
        mutate = text.index('mutation_started=True')
        self.assertLess(first, mutate)
        before, after = text[:mutate], text[mutate:]
        self.assertGreaterEqual(before.count('for p, expected in bound_files.items()'), 1)
        self.assertGreaterEqual(after.count('for p, expected in bound_files.items()'), 1)
        self.assertIn("inventory(ROOT / '.lake') == before_lake", before)
        self.assertIn('after_lake == before_lake and after_untracked == before_untracked', after)
        self.assertIn('after_objects == before_objects', after)
        self.assertIn('not os.path.lexists(V6_OUT)', before)
        self.assertIn('not os.path.lexists(V6_OUT)', after)
        self.assertIn("common-config.before", after)

    def test_executed_adapter_is_bound_and_output_is_external_before_mkdir(self):
        text = ast.unparse(MAIN)
        self.assertLess(text.index('Evidence output must be outside every registered worktree'),
                        text.index('args.output.mkdir()'))
        self.assertLess(text.index('bound_files[str(executed_adapter)] = args.runner_sha256'),
                        text.index('mutation_started=True'))
        self.assertIn('not under(executed_adapter, ROOT)', text)
        self.assertIn('not under(executed_adapter, COMMON)', text)

    def test_missing_or_nonblob_Git_objects_stop_before_omission(self):
        start = next(i for i, n in enumerate(BODY) if isinstance(n, ast.Assign)
                     and any(isinstance(t, ast.Name) and t.id == 'candidate_blob_lines' for t in n.targets))
        end = next(i for i, n in enumerate(BODY) if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Name) and t.id == 'omitted' for t in n.targets))
        nodes = BODY[start:end]
        oid = 'a' * 40
        path = 'docs/evidence/owned-frontiers/candidate.json'
        for line in [oid + ' missing\n', oid + ' tree 7\n', 'b' * 40 + ' blob 7\n']:
            with self.subTest(line=line):
                env = dict(NS, rows={path: {'oid': oid}}, excluded={path}, git=lambda *a, **kw: line.encode())
                with self.assertRaisesRegex(RuntimeError, 'Git blob'):
                    execute(nodes, env)
        env = dict(NS, rows={path: {'oid': oid}}, excluded={path}, git=lambda *a, **kw: (oid + ' blob 7\n').encode())
        execute(nodes, env)
        self.assertEqual(env['candidate_blob_sizes'], {path: 7})

    def test_Git_object_inventory_is_rechecked_before_mutation(self):
        before = ast.unparse(MAIN).split('mutation_started=True')[0]
        self.assertIn("inventory(COMMON / 'objects') == before_objects", before)


if __name__ == '__main__':
    unittest.main()
