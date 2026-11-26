#!/usr/bin/env python3
"""Portable historical audit regression; no Lean, cloud, or Git commands."""
from pathlib import Path
import ast
import copy
import importlib.util
import tempfile
import unittest

HERE = Path(__file__).resolve().parent

def load(name, file):
    spec = importlib.util.spec_from_file_location(name, HERE / file)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

v2 = load('portable_selected', 'export_selected_rows_v2.py')
prior = load('prior_selected_tests', 'test_export_selected_rows.py')
prior.selected = v2

class PortableHistoricalAudit(unittest.TestCase):
    def fixture(self, root):
        stage = root / 'current-stage'
        stage.mkdir()
        current = root / 'explicit-audit.lean'
        current.write_bytes(b'-- exact historical source\n')
        historical = {'path': str(root / 'absent-old-host' / 'audit.lean'), **v2.pin(current.read_bytes())}
        return v2.Audit(stage), current, historical

    def test_missing_original_requires_explicit_exact_source(self):
        with tempfile.TemporaryDirectory() as name:
            audit, current, historical = self.fixture(Path(name))
            before = copy.deepcopy(historical)
            with self.assertRaisesRegex(ValueError, 'Missing file'):
                v2.bind_shared_bounded_audit(audit, historical)
            result = v2.bind_shared_bounded_audit(audit, historical, current)
            self.assertEqual(result['historical_identity'], before)
            self.assertEqual(historical, before)
            self.assertNotEqual(result['historical_identity']['path'], result['current_identity']['path'])
            self.assertTrue(v2.same(result['historical_identity'], result['current_identity']))
            self.assertTrue(result['explicit_relocation'])
            self.assertFalse(result['historical_receipt_or_argv_modified'])
            self.assertEqual(list(audit.members), ['prior-evidence/shared-bounded-owned-audit.lean'])
            audit.unchanged()
            current.write_bytes(b'changed audit')
            with self.assertRaises(ValueError):
                audit.unchanged()

    def test_wrong_bytes_symlink_and_noncanonical_original_rejected(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            audit, current, historical = self.fixture(root)
            bad = root / 'bad.lean'
            bad.write_bytes(b'X' * current.stat().st_size)
            with self.assertRaisesRegex(ValueError, 'Changed bytes'):
                v2.bind_shared_bounded_audit(audit, historical, bad)
            link = root / 'link.lean'
            link.symlink_to(current)
            with self.assertRaisesRegex(ValueError, 'Noncanonical'):
                v2.bind_shared_bounded_audit(audit, historical, link)
            for value in ('relative.lean', str(root / '..' / 'old.lean')):
                with self.assertRaisesRegex(ValueError, 'Noncanonical historical'):
                    v2.bind_shared_bounded_audit(audit, {**historical, 'path': value}, current)

    def test_existing_original_cannot_be_overridden(self):
        with tempfile.TemporaryDirectory() as name:
            audit, current, historical = self.fixture(Path(name))
            original = Path(historical['path'])
            original.parent.mkdir()
            original.write_bytes(current.read_bytes())
            with self.assertRaisesRegex(ValueError, 'only when'):
                v2.bind_shared_bounded_audit(audit, historical, current)
            result = v2.bind_shared_bounded_audit(audit, historical)
            self.assertFalse(result['explicit_relocation'])
            original.unlink()
            original.symlink_to(original.parent / 'absent-target')
            with self.assertRaisesRegex(ValueError, 'only when'):
                v2.bind_shared_bounded_audit(audit, historical, current)

    def test_only_expected_functions_changed(self):
        def nodes(path):
            return {node.name: ast.dump(node) for node in ast.parse(path.read_text()).body
                    if isinstance(node, (ast.FunctionDef, ast.ClassDef))}
        old = nodes(HERE / 'export_selected_rows.py')
        new = nodes(HERE / 'export_selected_rows_v2.py')
        self.assertEqual(set(new) - set(old), {'bind_shared_bounded_audit'})
        self.assertEqual(set(old) - set(new), set())
        changed = {key for key in old if old[key] != new[key]}
        self.assertEqual(changed, {'historical_boundary', 'review', 'main'})
        old_text = (HERE / 'export_selected_rows.py').read_text()
        new_text = (HERE / 'export_selected_rows_v2.py').read_text()
        start = '    selected_objects, rows, steps, union = {}, [], [], set()\n'
        stop = '    exact_attempt_inventory(root, audit)'
        self.assertEqual(old_text[old_text.index(start):old_text.index(stop)],
                         new_text[new_text.index(start):new_text.index(stop)])

if __name__ == '__main__':
    suite = unittest.TestSuite()
    for name in unittest.defaultTestLoader.getTestCaseNames(prior.SelectionBoundaries):
        if name != 'test_reviewed_v1_core_is_unchanged':
            suite.addTest(prior.SelectionBoundaries(name))
    suite.addTests(unittest.defaultTestLoader.loadTestsFromTestCase(PortableHistoricalAudit))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    raise SystemExit(0 if result.wasSuccessful() else 1)
