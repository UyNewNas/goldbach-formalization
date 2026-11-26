#!/usr/bin/env python3
"""Exercise the narrow candidate policy without running storage recovery."""
import ast
import hashlib
import json
import os
from pathlib import Path
import runpy
import tempfile
import unittest

FOLDER = Path(__file__).resolve().parent
DRIVER = Path(os.environ.get(
    'P25_STORAGE_TEST_DRIVER', str(FOLDER / 'recover_p2_sparse_worktree_round4_v3.py')))
NS = runpy.run_path(str(DRIVER))
MAIN = next(node for node in ast.parse(DRIVER.read_text()).body
            if isinstance(node, ast.FunctionDef) and node.name == 'main')
BODY = next(node for node in MAIN.body if isinstance(node, ast.Try)).body
PROTECT = next(node for node in BODY if isinstance(node, ast.FunctionDef) and node.name == 'protect')
START = next(i for i, node in enumerate(BODY) if isinstance(node, ast.Assign)
             and any(isinstance(target, ast.Name) and target.id == 'protected_names' for target in node.targets))
END = next(i for i, node in enumerate(BODY) if isinstance(node, ast.FunctionDef) and node.name == 'allocated_bytes')
SELECT = next(node for node in BODY if isinstance(node, ast.Assign)
              and any(isinstance(target, ast.Name) and target.id == 'base_omissions' for target in node.targets))
EVIDENCE = FOLDER.parent / 'p2-storage-round4-v2/apply002'
INVENTORY = json.loads((EVIDENCE / 'OWNED_FRONTIERS_CAPACITY.json').read_text())


def execute(nodes, environment):
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(DRIVER), 'exec'), environment)


class OwnedFrontierPolicyChecks(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paths = [
            'docs/evidence/owned-frontiers/unreferenced/item.raw',
            'docs/evidence/owned-frontiers/referenced_tree/nested/item.raw',
            'docs/evidence/owned-frontiers/referenced_file.json',
            'docs/evidence/owned-frontiers/symlink_target.raw',
            'docs/evidence/owned-frontiers/.gitattributes',
            'docs/evidence/external-native-pnt/native-target/component.olean',
            'docs/evidence/other-area/receipt.json',
            'docs/verification/receipt.json',
            'docs/source-only/fixture/unreferenced.lean',
        ]
        self.rows = {path: {'mode': '100644', 'oid': 'fixture'} for path in self.paths}
        for relative in self.paths:
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b'fixture')
        alias = self.root / 'ImbalancedChen/fixture.lean'
        alias.parent.mkdir()
        alias.symlink_to('../docs/evidence/owned-frontiers/symlink_target.raw')
        self.rows['ImbalancedChen/fixture.lean'] = {'mode': '120000', 'oid': 'fixture-link'}
        self.environment = dict(NS, ROOT=self.root, rows=self.rows, protected={}, resolutions={})
        execute([PROTECT], self.environment)
        protect = self.environment['protect']
        protect(self.root / 'docs/evidence/owned-frontiers/referenced_tree', 'referenced directory', True)
        protect(self.root / 'docs/evidence/owned-frontiers/referenced_file.json', 'referenced file', True)
        protect(alias, 'required source symlink', True)
        execute(BODY[START:END] + [SELECT], self.environment)

    def test_only_unreferenced_owned_frontiers_and_existing_base_paths_are_selected(self):
        self.assertEqual(self.environment['base_omissions'], {
            'docs/evidence/owned-frontiers/unreferenced/item.raw',
            'docs/source-only/fixture/unreferenced.lean',
        })

    def test_referenced_directory_inside_new_prefix_protects_its_entire_subtree(self):
        self.assertIn('docs/evidence/owned-frontiers/referenced_tree/',
                      self.environment['protected_subtrees'])
        self.assertTrue(self.environment['is_protected'](
            'docs/evidence/owned-frontiers/referenced_tree/nested/item.raw'))

    def test_resolved_source_symlink_target_and_git_attributes_are_preserved(self):
        for path in ['docs/evidence/owned-frontiers/symlink_target.raw',
                     'docs/evidence/owned-frontiers/.gitattributes', 'ImbalancedChen/fixture.lean']:
            with self.subTest(path=path):
                self.assertTrue(self.environment['is_protected'](path))
                self.assertNotIn(path, self.environment['base_omissions'])

    def test_actual_snapshot_candidates_fit_narrow_policy_and_eight_attributes_stay_out(self):
        rows = {row['path']: {'mode': '100644', 'oid': row['git_blob_sha']}
                for row in INVENTORY['eligible']}
        rows.update({row['path']: {'mode': '100644', 'oid': 'protected-metadata'}
                     for row in INVENTORY['blocked']})
        outside = 'docs/evidence/external-native-pnt/native-target/component.olean'
        rows[outside] = {'mode': '100644', 'oid': 'outside-policy'}
        environment = dict(NS, ROOT=self.root, rows=rows, protected={})
        execute(BODY[START:END] + [SELECT], environment)
        self.assertEqual(len(environment['base_omissions']), 1278)
        self.assertEqual(environment['base_omissions'], {row['path'] for row in INVENTORY['eligible']})
        self.assertNotIn(outside, environment['base_omissions'])
        for row in INVENTORY['blocked']:
            self.assertTrue(environment['is_protected'](row['path']))


class ActualEvidenceChecks(unittest.TestCase):
    def test_failed_v2_receipt_and_readonly_inventory_remain_exact_and_unaccepted(self):
        for name, expected in [
            ('RESULT.json', 'b476b8fc56ae5d1fe5769f31e3792d0a5aeb4608f616267d3e4f100f25d41fb1'),
            ('OWNED_FRONTIERS_CAPACITY.json', '45c66a78741545bb760205aa0d44d0d8a5697f6ce0fec2fa193772a424922ccb'),
        ]:
            raw = (EVIDENCE / name).read_bytes()
            self.assertEqual(hashlib.sha256(raw).hexdigest(), expected)
            value = json.loads(raw)
            self.assertFalse(value['mutation_started'])
            self.assertFalse(value['compiled'])
            self.assertFalse(value['P2_5_proved'])
        result = json.loads((EVIDENCE / 'RESULT.json').read_text())
        self.assertFalse(result['accepted'])
        self.assertFalse(result['storage_recovery_verified'])
        canonical = json.dumps(INVENTORY['eligible'], sort_keys=True, separators=(',', ':')).encode()
        self.assertEqual(hashlib.sha256(canonical).hexdigest(),
                         '2c878b80c078333943049aefffd9bb6ce5374f868bc62bf46fd5a9a52dd578bd')
        self.assertEqual(sum(row['allocated_bytes'] for row in INVENTORY['eligible']), 193220608)
        self.assertEqual(sum(row['bytes'] for row in INVENTORY['eligible']), 190272308)
        self.assertEqual(len(INVENTORY['blocked']), 8)


if __name__ == '__main__':
    unittest.main()
