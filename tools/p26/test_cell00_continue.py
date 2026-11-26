"""Host-only integrity checks; these tests never invoke Lean or leanchecker."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


class Cell00DriverChecks(unittest.TestCase):
    def setUp(self):
        path = Path(__file__).with_name('Cell00OriginalFloor_continue.py')
        self.assertTrue(path.exists(), 'Cell00 continuation driver is not implemented')
        spec = importlib.util.spec_from_file_location('cell00_driver', path)
        self.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.driver)

    def test_hash_change_and_external_symlink_are_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'source.lean'
            source.write_text('pinned source\n')
            pin = self.driver.fp(source)
            self.driver.require_pin(source, pin, root)
            source.write_text('changed source\n')
            with self.assertRaises(self.driver.VerificationError):
                self.driver.require_pin(source, pin, root)
            link = root / 'link.lean'
            link.symlink_to(source)
            with self.assertRaises(self.driver.VerificationError):
                self.driver.require_pin(link, self.driver.fp(source), root)

    def test_seven_sibling_packages_work_without_cli(self):
        with tempfile.TemporaryDirectory() as directory:
            packages = Path(directory)
            mathlib = packages / 'mathlib'
            (mathlib / '.lake/build/lib/lean').mkdir(parents=True)
            for package in self.driver.REQUIRED_PACKAGES:
                (packages / package / '.lake/build/lib/lean').mkdir(parents=True)
            roots = self.driver.package_roots(mathlib)
            self.assertEqual(len(roots), 8)  # mathlib plus its seven built suppliers
            (packages / 'aesop/.lake/build/lib/lean').rmdir()
            with self.assertRaises(self.driver.VerificationError):
                self.driver.package_roots(mathlib)

    def test_external_suppliers_bind_source_and_record_object_bytes(self):
        self.assertTrue(hasattr(self.driver, 'external_inputs'), 'External package binding is missing')
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            packages = {name: base / name for name in ('goldbach', 'LeanArchitect')}
            rows = []
            for package, module in [('goldbach', 'MathlibNt.Example'),
                                    ('LeanArchitect', 'Architect.Example')]:
                source = packages[package] / (module.replace('.', '/') + '.lean')
                obj = packages[package] / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
                source.parent.mkdir(parents=True)
                obj.parent.mkdir(parents=True)
                source.write_text('pinned external source\n')
                obj.write_bytes(b'existing external object')
                rows.append({'module': module, 'package': package,
                    'source_sha256': self.driver.fp(source)['sha256'], 'bytes': source.stat().st_size})
            manifest = {'module_count': 2, 'package_pins': self.driver.EXTERNAL_COMMITS, 'rows': rows}
            bound = self.driver.external_inputs(manifest, packages)
            self.assertEqual(len(bound['modules']), 2)
            self.assertEqual(len(bound['files']), 4)
            source.write_text('changed external source\n')
            with self.assertRaises(self.driver.VerificationError):
                self.driver.external_inputs(manifest, packages)

    def test_single_object_root_contains_both_supplier_namespaces(self):
        self.assertTrue(hasattr(self.driver, 'copy_project_union'), 'Single namespace union is missing')
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            suppliers = {}
            for folder, module in [('base', 'ImbalancedChen.Base'), ('analytic', 'ImbalancedChen.Analytic')]:
                path = root / folder / (module.replace('.', '/') + '.olean')
                path.parent.mkdir(parents=True)
                path.write_bytes(module.encode())
                suppliers[module] = self.driver.fp(path)
            union = root / 'single-root'
            union.mkdir()
            copied = self.driver.copy_project_union(union, suppliers)
            self.assertEqual(len(copied), 2)
            for module, original in suppliers.items():
                target = union / (module.replace('.', '/') + '.olean')
                self.assertTrue(target.is_file())
                self.assertFalse(target.is_symlink())
                self.assertEqual(self.driver.fp(target)['sha256'], original['sha256'])

    def test_failed_command_has_hashed_log_and_fails_closed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            argv = [sys.executable, '-c', 'print("deliberate failure"); raise SystemExit(7)']
            with self.assertRaises(self.driver.VerificationError):
                self.driver.run_command(argv, root, {}, root / 'step', 10)
            result = json.loads((root / 'step/result.json').read_text())
            self.assertEqual(result['status'], 'failed')
            self.assertEqual(result['exit_code'], 7)
            self.assertEqual(result['log']['sha256'], self.driver.fp(root / 'step/output.log')['sha256'])

    def test_owned_audit_requires_every_name_and_only_standard_axioms(self):
        module = 'ImbalancedChen.Example'
        def output(axioms, include_decl=True):
            rows = [('INVENTORY', {'module': module, 'names': [module + '.proof']})]
            if include_decl:
                rows.append(('DECL', {'module': module, 'name': module + '.proof',
                    'type': 'True', 'unsafe': False, 'partial': False, 'axiom': False,
                    'axioms': axioms}))
            rows.append(('COMPLETE', {'module': module, 'count': 1}))
            return '\n'.join('P26_CELL00_AUDIT_' + kind + ' ' + json.dumps(data)
                             for kind, data in rows)
        self.assertEqual(self.driver.parse_owned(output(['propext']), module)['count'], 1)
        for text in [output(['sorryAx']), output([], include_decl=False)]:
            with self.assertRaises(self.driver.VerificationError):
                self.driver.parse_owned(text, module)


if __name__ == '__main__':
    unittest.main()
