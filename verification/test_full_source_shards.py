"""Stdlib-only deterministic shard coverage tests; never invoke Lean."""
import copy
import json
import unittest

from full_source_shards import PRODUCTION, make_manifest, select_targets


def fixture():
    graph = {'ImbalancedChen': ['ImbalancedChen.Z'],
             'ImbalancedChen.A': [], 'ImbalancedChen.B': ['ImbalancedChen.A'],
             'ImbalancedChen.C': [], 'ImbalancedChen.D': ['ImbalancedChen.C'],
             'ImbalancedChen.Z': ['ImbalancedChen.B', 'ImbalancedChen.D']}
    return {'head': 'a' * 40, 'read_mode': 'git_revision', 'targets': list(graph),
            'counts': {'library_modules': len(graph)}, 'missing_local_imports': [],
            'missing_batch_paths': [], 'missing_tracked_paths': [],
            'files': [{'path': m.replace('.', '/') + '.lean', 'module': m, 'imports': deps,
                       'exists': True, 'sha256': 'b' * 64, 'bytes': 10, 'disposition': PRODUCTION}
                      for m, deps in graph.items()]}


class ShardTests(unittest.TestCase):
    def test_balanced_disjoint_exhaustive_contiguous_order(self):
        result = make_manifest(fixture())
        self.assertEqual([s['target_count'] for s in result['shards']], [2, 2, 1, 1])
        flat = [m for s in result['shards'] for m in s['targets']]
        self.assertEqual(flat, result['topological_order'])
        self.assertEqual(set(flat), set(fixture()['targets']))
        self.assertEqual(len(flat), len(set(flat)))
        self.assertEqual(flat[-1], 'ImbalancedChen')
        for edge in result['dependency_order_evidence']['edges']:
            self.assertLess(edge['dependency_position'], edge['importer_position'])
            self.assertLessEqual(edge['dependency_shard'], edge['importer_shard'])
        self.assertEqual(select_targets(result, 4), ['ImbalancedChen'])

    def test_deterministic_under_input_permutation(self):
        first = fixture()
        second = copy.deepcopy(first)
        second['targets'].reverse()
        second['files'].reverse()
        for row in second['files']:
            row['imports'].reverse()
        self.assertEqual(json.dumps(make_manifest(first), sort_keys=True),
                         json.dumps(make_manifest(second), sort_keys=True))

    def test_count_and_index_bounds(self):
        for count in (0, -1, 7, True, 1.5):
            with self.subTest(count=count), self.assertRaises(ValueError):
                make_manifest(fixture(), count)
        result = make_manifest(fixture(), 1)
        for index in (0, -1, 2, True, 1.5):
            with self.subTest(index=index), self.assertRaises(ValueError):
                select_targets(result, index)

    def test_missing_dependency_and_cycle(self):
        bad = fixture()
        bad['files'][1]['imports'] = ['ImbalancedChen.Absent']
        with self.assertRaisesRegex(ValueError, 'missing project dependency'):
            make_manifest(bad)
        bad = fixture()
        bad['files'][1]['imports'] = ['ImbalancedChen']
        with self.assertRaisesRegex(ValueError, 'cycle'):
            make_manifest(bad)

    def test_malformed_inventory(self):
        mutations = [lambda x: x['targets'].append(x['targets'][0]),
                     lambda x: x['targets'].pop(),
                     lambda x: x['files'].append(copy.deepcopy(x['files'][0])),
                     lambda x: x['files'][0].update(sha256='bad'),
                     lambda x: x['files'][0].update(exists=False),
                     lambda x: x['files'][0].update(imports=None),
                     lambda x: x['files'][0].update(module='ImbalancedChen.Wrong'),
                     lambda x: x['counts'].update(library_modules=99),
                     lambda x: x.update(head='short'),
                     lambda x: x.update(missing_local_imports=[{'import': 'Absent'}]),
                     lambda x: x.pop('missing_tracked_paths')]
        for mutate in mutations:
            bad = fixture()
            mutate(bad)
            with self.subTest(inventory=bad), self.assertRaises(ValueError):
                make_manifest(bad)

    def test_heavy_families_spread_across_dependency_safe_waves(self):
        source = fixture()
        rows = ['ImbalancedChen.Part5SavedParent394700BuchstabRow%02d' % i for i in range(32)]
        blocks = ['ImbalancedChen.Certificates.OriginalNodeArraysV1.Block%02dFullCheck' % i for i in range(40)]
        for module in rows + blocks:
            source['targets'].append(module)
            source['files'].append({'path': module.replace('.', '/') + '.lean', 'module': module,
                                    'imports': ['ImbalancedChen.A'], 'exists': True,
                                    'sha256': 'b' * 64, 'bytes': 10, 'disposition': PRODUCTION})
        source['files'][0]['imports'] += rows + blocks
        source['counts']['library_modules'] = len(source['targets'])
        result = make_manifest(source)
        self.assertEqual([s['heavy_family_counts']['saved_parent_original_rows'] for s in result['shards']], [8] * 4)
        self.assertEqual([s['heavy_family_counts']['original_node_full_checks'] for s in result['shards']], [10] * 4)
        self.assertEqual(result['topological_order'][-1], 'ImbalancedChen')
        for edge in result['dependency_order_evidence']['edges']:
            self.assertLess(edge['dependency_position'], edge['importer_position'])
            self.assertLessEqual(edge['dependency_shard'], edge['importer_shard'])
        reverse = copy.deepcopy(source)
        reverse['files'].reverse()
        reverse['targets'].reverse()
        self.assertEqual(result, make_manifest(reverse))
        # Membership and assignments are derived even when family members change.
        modified = copy.deepcopy(source)
        removed = rows[0]
        modified['files'] = [r for r in modified['files'] if r['module'] != removed]
        modified['targets'].remove(removed)
        modified['files'][0]['imports'].remove(removed)
        added = 'ImbalancedChen.Part5SavedParent394700BuchstabRow32'
        new_row = copy.deepcopy(next(r for r in modified['files'] if r['module'] == rows[1]))
        new_row.update(module=added, path=added.replace('.', '/') + '.lean')
        modified['files'].append(new_row)
        modified['targets'].append(added)
        changed = make_manifest(modified)
        family = changed['scheduling_policy']['families']['saved_parent_original_rows']
        self.assertIn(added, family)
        self.assertNotIn(removed, family)
        self.assertIn(added, changed['all_targets'])
        self.assertEqual(sum(s['heavy_family_counts']['saved_parent_original_rows'] for s in changed['shards']), len(family))
        # An earlier reserved row cannot depend on a later reserved row.
        next(r for r in source['files'] if r['module'] == rows[0])['imports'].append(rows[-1])
        with self.assertRaisesRegex(ValueError, 'later reserved wave'):
            make_manifest(source)

    def test_uneven_dynamic_families_three_waves_and_single_wave(self):
        source = fixture()
        members = ['ImbalancedChen.Part5SavedParent394700BuchstabRow%02d' % i for i in range(5)]
        members += ['ImbalancedChen.Certificates.OriginalNodeArraysV1.Block%02dFullCheck' % i for i in range(7)]
        for module in members:
            source['targets'].append(module)
            source['files'].append({'path': module.replace('.', '/') + '.lean', 'module': module,
                                    'imports': ['ImbalancedChen.A'], 'exists': True,
                                    'sha256': 'b' * 64, 'bytes': 10, 'disposition': PRODUCTION})
        source['files'][0]['imports'] += members
        source['counts']['library_modules'] = len(source['targets'])
        three = make_manifest(source, 3)
        self.assertEqual([s['heavy_family_counts']['saved_parent_original_rows'] for s in three['shards']], [2, 2, 1])
        self.assertEqual([s['heavy_family_counts']['original_node_full_checks'] for s in three['shards']], [3, 2, 2])
        single = make_manifest(source, 1)
        self.assertEqual(single['shards'][0]['heavy_family_counts'],
                         {'saved_parent_original_rows': 5, 'original_node_full_checks': 7})
        self.assertEqual(single['target_count'], len(source['targets']))
        with self.assertRaisesRegex(ValueError, 'exceed target count'):
            make_manifest(source, len(source['targets']) + 1)

    def test_oversized_reserved_closure_fails_instead_of_empty_shard(self):
        source = fixture()
        module = 'ImbalancedChen.Part5SavedParent394700BuchstabRow00'
        source['targets'].append(module)
        source['files'].append({'path': module.replace('.', '/') + '.lean', 'module': module,
                                'imports': ['ImbalancedChen'], 'exists': True,
                                'sha256': 'b' * 64, 'bytes': 10, 'disposition': PRODUCTION})
        source['counts']['library_modules'] = len(source['targets'])
        with self.assertRaisesRegex(ValueError, 'empty warm-build shard'):
            make_manifest(source, 4)

    def test_source_hash_identity_changes_with_bytes(self):
        source = fixture()
        before = make_manifest(source)
        source['files'][0]['sha256'] = 'c' * 64
        after = make_manifest(source)
        self.assertNotEqual(before['source_identity_sha256'], after['source_identity_sha256'])
        self.assertEqual(before['topological_order'], after['topological_order'])


if __name__ == '__main__':
    unittest.main()
