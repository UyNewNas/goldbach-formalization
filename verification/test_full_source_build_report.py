import unittest
from full_source_build_report import classify


class ReportTests(unittest.TestCase):
    def test_complete_build(self):
        self.assertEqual(classify(['A', 'B'], '', 0), {'A': 'build_passed_or_validated_cache', 'B': 'build_passed_or_validated_cache'})

    def test_partial_is_not_success(self):
        log = '✔ [1/8] Built A (1s)\n⚠ [2/8] Built B (2s)\n✖ [3/8] Building C (4s)\n'
        states = classify(['A', 'B', 'C', 'D', 'E'], log, 1, ['C', 'D'])
        self.assertEqual(states, {'A': 'compiled_successfully', 'B': 'compiled_successfully', 'C': 'compile_failed', 'D': 'unconfirmed_existing_object', 'E': 'not_completed_or_dependency_blocked'})


if __name__ == '__main__':
    unittest.main()
