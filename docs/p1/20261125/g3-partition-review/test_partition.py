#!/usr/bin/env python3
"""Read-only source reconstruction checks; no Lean, fixture I/O or compilation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
BASE = '220c14630ffd266f824bdbf0977147ecb740c0dd'
DATA = 'ImbalancedChen/P4AOriginalNewFifthArchiveData.lean'
NAMESPACE = 'ImbalancedChen.P4AOriginalNewFifthArchiveData'
INCLUDE = re.compile(rb'^def ([CF]\d{4}) : Block := include_new_fifth_pair% "([^"]+)" "([^"]+)"\n', re.M)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


class PartitionSourceChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = subprocess.check_output(['git', 'show', BASE + ':' + DATA], cwd=ROOT)
        cls.plan = json.loads((HERE / 'PARTITION_PLAN.json').read_text())
        cls.original_defs = {m[1].decode(): m[0] for m in INCLUDE.finditer(cls.original)}
        assert len(cls.original_defs) == 94

    def test_every_original_literal_is_moved_once_with_same_namespace_and_paths(self):
        """Catches omission, duplication, namespace drift and changed fixture arguments."""
        found = {}
        for group in self.plan['groups']:
            path = ROOT / group['path']
            self.assertTrue(path.is_file(), 'partition provider is absent: ' + str(path))
            raw = path.read_bytes()
            self.assertEqual(path.parent, ROOT / 'ImbalancedChen')
            self.assertEqual(re.findall(rb'^import (\S+)$', raw, re.M),
                             [b'ImbalancedChen.P4AOriginalNewFifthArchiveReader'])
            self.assertEqual(re.findall(rb'^namespace (\S+)$', raw, re.M), [NAMESPACE.encode()])
            definitions = list(INCLUDE.finditer(raw))
            self.assertEqual([m[1].decode() for m in definitions], group['blocks'])
            self.assertEqual(len(re.findall(rb'^(?:def|theorem|abbrev|opaque|axiom|instance|structure|inductive) ', raw, re.M)),
                             len(definitions))
            for match in definitions:
                name = match[1].decode()
                self.assertNotIn(name, found)
                self.assertEqual(match[0], self.original_defs[name])
                found[name] = match[0]
        self.assertEqual(found, self.original_defs)

    def test_facade_preserves_every_nonliteral_original_byte(self):
        """Catches changed banks, counts, floors, index types, row APIs or extra definitions."""
        facade = (ROOT / DATA).read_bytes()
        self.assertFalse(INCLUDE.search(facade), 'old monolithic literals remain in facade')
        expected_imports = [a['module'].encode() for a in self.plan['groups']]
        imports = re.findall(rb'^import (\S+)$', facade, re.M)
        self.assertEqual(imports, [b'ImbalancedChen.P4AOriginalNewFifthArchiveReader'] + expected_imports)
        stripped = facade
        for module in expected_imports:
            line = b'import ' + module + b'\n'
            self.assertEqual(stripped.count(line), 1)
            stripped = stripped.replace(line, b'', 1)
        self.assertEqual(stripped, INCLUDE.sub(b'', self.original))

    def test_manifest_binds_all_actual_sources_and_original188_fixture_records(self):
        """Catches missing owners, wrong postimages or altered external-data provenance."""
        path = HERE / 'SOURCE_PARTITION.json'
        self.assertTrue(path.is_file(), 'partition source manifest is absent')
        manifest = json.loads(path.read_text())
        self.assertEqual(manifest['schema'], 'p1_g3_literal_data_partition_v1')
        self.assertEqual(manifest['status'], 'SOURCE_ONLY_UNCOMPILED_UNAUDITED_CANDIDATE')
        self.assertEqual(manifest['base_source_commit'], BASE)
        expected = {a['module']: a['path'] for a in self.plan['groups']}
        expected['ImbalancedChen.P4AOriginalNewFifthArchiveData'] = DATA
        self.assertEqual({a['module']: a['path'] for a in manifest['modules']}, expected)
        self.assertEqual(len(manifest['modules']), 25)
        for item in manifest['modules']:
            self.assertEqual(digest((ROOT / item['path']).read_bytes()), item['source_sha256'])
            self.assertEqual(item['expected_before_sha256'], digest(self.original) if item['path'] == DATA else None)
        inv = json.loads((ROOT / 'docs/p1/20261125/g3-reuse/G3_REUSE_INVENTORY.json').read_text())
        expected_inputs = {a['install_path']: (a['bytes'], a['sha256']) for a in inv['g3_files']}
        actual_inputs = {a['path']: (a['bytes'], a['sha256']) for a in manifest['data_inputs']}
        self.assertEqual(len(manifest['data_inputs']), 188)
        self.assertEqual(actual_inputs, expected_inputs)
        self.assertFalse(manifest['normal_accepted'])
        self.assertFalse(manifest['kernel_accepted'])
        self.assertFalse(manifest['full_owned_accepted'])

    def test_reader_archive_and_integral_source_remain_original_bytes(self):
        """Catches accidental changes outside the authorized Data partition."""
        for name in ['P4AOriginalNewFifthArchiveReader', 'P4AOriginalNewFifthArchive',
                     'P4AOriginalNewFifthBoxIntegral']:
            path = 'ImbalancedChen/' + name + '.lean'
            original = subprocess.check_output(['git', 'show', BASE + ':' + path], cwd=ROOT)
            self.assertEqual((ROOT / path).read_bytes(), original)


if __name__ == '__main__':
    unittest.main(verbosity=2)
