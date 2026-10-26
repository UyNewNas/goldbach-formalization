"""Fast stdlib-only tests; no compiler or network dependencies."""
import unittest
import hashlib
import json
from full_source_inventory import CENSUS_ARCHIVE, MANIFEST, closure, disposition, inventory, parse_imports


class InventoryTests(unittest.TestCase):
    def test_nested_comments_and_strings(self):
        text = '''/- import Fake.A /- import Fake.B -/ -/
import ImbalancedChen.Real -- import Fake.C
/- multiline
import Fake.D
-/
def message := "import Fake.E\\\" -- text"
import /- inline -/ Mathlib.Data.Nat.Basic
public import ImbalancedChen.Other
'''
        self.assertEqual(parse_imports(text), ['ImbalancedChen.Real', 'Mathlib.Data.Nat.Basic', 'ImbalancedChen.Other'])

    def test_multiple_imports(self):
        self.assertEqual(parse_imports('import A B\n-- import C'), ['A', 'B'])

    def test_closure_includes_dependencies_not_unrelated(self):
        graph = {'Root': ['A'], 'A': ['B', 'External'], 'B': ['A'], 'C': []}
        self.assertEqual(closure({'Root'}, graph), {'Root', 'A', 'B'})

    def test_inventory_membership_changed_hash_and_full_disposition(self):
        census = json.dumps({'modules': {'ImbalancedChen.Owned': {}}}).encode()
        census_sha = hashlib.sha256(census).hexdigest()
        archive = {'roles': {'current_census': {'sha256': census_sha}},
                   'payloads': [{'sha256': census_sha, 'stored_path': 'census.raw'}]}
        source = b'import ImbalancedChen.Owned\n'
        data = {
            MANIFEST: json.dumps({'records': [{'path': 'ImbalancedChen/New.lean', 'sha256': 'original'}]}).encode(),
            CENSUS_ARCHIVE: json.dumps(archive).encode(),
            CENSUS_ARCHIVE.rsplit('/', 1)[0] + '/census.raw': census,
            'ImbalancedChen.lean': b'import ImbalancedChen.Owned\n',
            'ImbalancedChen/Owned.lean': b'',
            'ImbalancedChen/New.lean': source,
            'ImbalancedChen/UncompiledContinuation.lean': b'import ImbalancedChen.New\n',
            'README.md': b'documentation',
        }
        class FakeRepo:
            revision = None
            def paths(self): return sorted(data)
            def read(self, path): return data[path]
            def git(self, *args): return b'fake-sha\n'
        report = inventory(FakeRepo())
        self.assertEqual(report['counts']['tracked_files'], len(data))
        self.assertEqual(report['counts']['library_modules'], 4)
        self.assertEqual(report['missing_local_imports'], [])
        self.assertEqual(report['changed_batch_hashes'][0]['original_sha256'], 'original')
        new = next(row for row in report['files'] if row['path'] == 'ImbalancedChen/New.lean')
        self.assertTrue(new['batch711_member'])
        self.assertTrue(new['continuation_reachable'])
        self.assertFalse(new['root_reachable'])
        self.assertTrue(all(row['disposition'] and row['sha256'] for row in report['files']))

    def test_archive_never_production(self):
        self.assertIn('independent_target', disposition('ImbalancedChen/A.lean'))
        self.assertIn('historical', disposition('verification/parts/p0/round3/ledger/snapshot-sources/ImbalancedChen/A.lean'))
        self.assertIn('historical', disposition('docs/evidence/external/A.lean'))
        self.assertIn('documented_runner', disposition('verification/ActualSelectorAudit.lean'))


if __name__ == '__main__':
    unittest.main()
