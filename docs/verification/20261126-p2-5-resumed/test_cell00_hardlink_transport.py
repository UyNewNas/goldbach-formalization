#!/usr/bin/env python3
"""Real filesystem regressions for bounded-space accepted-object reuse."""
import importlib.util
from pathlib import Path
import tempfile
import unittest

DRIVER = Path(__file__).with_name('run_cell00_four_consumers_v7.py')


class HardlinkTransport(unittest.TestCase):
    def setUp(self):
        self.assertTrue(DRIVER.is_file(), 'bounded-space consumer driver is missing')
        spec = importlib.util.spec_from_file_location('p25_consumer_v7_test', DRIVER)
        self.module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.module)

    def test_reuses_identical_bytes_without_second_data_allocation(self):
        with tempfile.TemporaryDirectory(prefix='p25-link-test-') as folder:
            source, target = Path(folder) / 'accepted.olean', Path(folder) / 'isolated.olean'
            source.write_bytes(bytes(range(256)) * 16)
            self.module.link_dependency_bytes(source, target)
            self.assertEqual(source.read_bytes(), target.read_bytes())
            self.assertEqual(source.stat().st_ino, target.stat().st_ino)
            self.assertEqual(source.stat().st_dev, target.stat().st_dev)
            target.unlink()
            self.assertEqual(source.read_bytes(), bytes(range(256)) * 16)

    def test_existing_target_is_preserved(self):
        with tempfile.TemporaryDirectory(prefix='p25-link-test-') as folder:
            source, target = Path(folder) / 'accepted.olean', Path(folder) / 'target.olean'
            source.write_bytes(b'accepted')
            target.write_bytes(b'previous evidence')
            with self.assertRaises(RuntimeError):
                self.module.link_dependency_bytes(source, target)
            self.assertEqual(target.read_bytes(), b'previous evidence')

    def test_symbolic_source_is_rejected(self):
        with tempfile.TemporaryDirectory(prefix='p25-link-test-') as folder:
            source, alias, target = (Path(folder) / name for name in ('source', 'alias', 'target'))
            source.write_bytes(b'accepted')
            alias.symlink_to(source)
            with self.assertRaises(RuntimeError):
                self.module.link_dependency_bytes(alias, target)
            self.assertFalse(target.exists())


if __name__ == '__main__':
    unittest.main()
