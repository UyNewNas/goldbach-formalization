"""Only the new round-8 admission boundary; no Lean or settled test reruns."""
from pathlib import Path
import copy
import sys
import types
import unittest

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[3]
RUNNER = ROOT / 'docs/verification/20261126-p2-5-resumed/run_p2_round8.py'


def load_runner():
    module = types.ModuleType('p25_round8_delta_test')
    module.__file__ = str(RUNNER)
    exec(compile(RUNNER.read_bytes(), str(RUNNER), 'exec'), module.__dict__)
    return module


class Round8Delta(unittest.TestCase):
    def test_unpinned_prior_receipt_stops_before_cloud_access(self):
        runner = load_runner()
        runner.PRIOR_RESULT_SHA = None
        with self.assertRaisesRegex(RuntimeError, 'final receipt has not been pinned'):
            runner.require_prior_pins()
        runner.PRIOR_RESULT_SHA = '1' * 64
        runner.PRIOR_NORMAL_SUCCESSFUL = None
        with self.assertRaisesRegex(RuntimeError, 'final counts have not been pinned'):
            runner.require_prior_pins()

    def test_blocked_module_is_not_a_direct_failure(self):
        runner = load_runner()
        a, b, c = ('ImbalancedChen.A', 'ImbalancedChen.B', 'ImbalancedChen.C')
        compiled = {'failed_or_blocked': [a, b, c]}
        selection = {'changed_modules': [{'module': a}, {'module': b}]}
        text = 'PASS ImbalancedChen.Prior 1.25\nFAIL ' + a + ' 1\nFAIL ' + b + ' 124\n'
        self.assertEqual(runner.validate_repair_failures(selection, compiled, text), [a, b])
        bad = copy.deepcopy(selection)
        bad['changed_modules'].append({'module': c})
        with self.assertRaisesRegex(RuntimeError, 'actually executed failure'):
            runner.validate_repair_failures(bad, compiled, text)
        with self.assertRaisesRegex(RuntimeError, 'outside the terminal failed scope'):
            runner.validate_repair_failures(selection, {'failed_or_blocked': [a]}, text)

    def test_round7_controls_are_added_without_replacing_earlier_controls(self):
        runner = load_runner()
        self.assertEqual(runner.ROUND7_RUNNER_SHA,
                         '7599eb65dd43cf83d9664a719216f546be3b0c7c91100a42ae30de3c7174b8a0')
        self.assertEqual(runner.ROUND7_SELECTION_SHA,
                         'a50d75f57d17a781b4330d41249c168e1fabfbca1af979ec2a451ec791fd7269')
        self.assertEqual(runner.ROUND6_RUNNER_SHA,
                         '11c62f535a94f53ed4b22b7f08e55c8476529c49ec4b5d3cd6e219d3f04292f3')
        self.assertEqual(runner.PREVIOUS, '1e80a5fa2fa2dbb346dbdef5760a7361a8001a46')
        self.assertEqual(runner.PRIOR_OUT, '.lake/p25-followup-repairs-attempt007')
        self.assertEqual(runner.NEW_OUT, '.lake/p25-followup-repairs-attempt008')
        self.assertEqual(runner.MIN_FREE_BYTES, 1073741824)


if __name__ == '__main__':
    unittest.main()
