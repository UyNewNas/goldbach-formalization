import unittest
from full_source_build_report import classify, make_report, validate_selected_targets


class ReportTests(unittest.TestCase):
    def test_complete_build(self):
        self.assertEqual(classify(['A', 'B'], '', 0), {'A': 'build_passed_or_validated_cache', 'B': 'build_passed_or_validated_cache'})

    def test_partial_is_not_success(self):
        log = 'ℹ [1/8] Built A (1s)\n⚠ [2/8] Built B (2s)\n✖ [3/8] Building C (4s)\n'
        states = classify(['A', 'B', 'C', 'D', 'E'], log, 1, ['C', 'D'])
        self.assertEqual(states, {'A': 'compiled_or_replayed_successfully', 'B': 'compiled_or_replayed_successfully', 'C': 'compile_failed', 'D': 'unconfirmed_existing_object', 'E': 'not_completed_or_dependency_blocked'})

    def test_partial_scope_exit_zero_never_claims_all_production(self):
        inventory = {'head': 'a' * 40, 'targets': ['A', 'B'],
                     'files': [{'path': 'A.lean', 'module': 'A'}, {'path': 'B.lean', 'module': 'B'},
                               {'path': 'README.md', 'module': None}]}
        report = make_report(inventory, b'', 0, selected=['A'])
        self.assertTrue(report['all_requested_targets_passed'])
        self.assertFalse(report['all_production_targets_passed'])
        self.assertFalse(report['full_production_scope_requested'])
        self.assertEqual(report['targets']['B'], 'outside_this_build_shard')
        self.assertEqual(report['files'][1]['build_status'], 'outside_this_build_shard')
        self.assertEqual(report['files'][2]['build_status'], 'not_a_production_build_target')
        full = make_report(inventory, b'', 0)
        self.assertTrue(full['all_production_targets_passed'])
        self.assertTrue(full['all_requested_targets_passed'])
        failed = make_report(inventory, b'', 1, selected=['A'])
        self.assertFalse(failed['all_requested_targets_passed'])
        self.assertFalse(failed['all_production_targets_passed'])

    def test_malformed_unknown_duplicate_and_empty_selection(self):
        for selected in ([], ['A', 'A'], ['Unknown'], [' A'], ['A B'], [''], ['A', ''], [None], 'A'):
            with self.subTest(selected=selected), self.assertRaises(ValueError):
                validate_selected_targets(['A', 'B'], selected)

    def test_nonselected_logged_dependency_is_not_selected_acceptance(self):
        result = classify(['A', 'B'], '✔ [1/2] Built B (1s)\n', 0, selected=['A'])
        self.assertEqual(result['B'], 'outside_this_build_shard')

    def test_selected_full_scope_preserves_success(self):
        self.assertEqual(classify(['A', 'B'], '', 0, selected=['B', 'A']),
                         classify(['A', 'B'], '', 0))


if __name__ == '__main__':
    unittest.main()
