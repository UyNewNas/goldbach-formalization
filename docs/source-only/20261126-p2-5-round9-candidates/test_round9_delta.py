"""Round9-only checks: two dependency repairs and actual terminal provenance."""
from pathlib import Path
import copy
import json
import sys
import types
import unittest

sys.dont_write_bytecode = True
PACKAGE = Path(__file__).resolve().parent
ROOT = PACKAGE.parents[2]


def load(path, name):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(path.read_bytes(), str(path), 'exec'), module.__dict__)
    return module


class Round9Delta(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.prepare = load(PACKAGE / 'prepare_p2_round9.py', 'p25_round9_delta_prepare')
        cls.runner, cls.graph, cls.targets, cls.previous = cls.prepare.context()
        cls.selection = json.loads((PACKAGE / 'SOURCE_SELECTION.json').read_bytes())

    def test_two_dependency_repairs_keep_all_owned_targets_and_prior_successes(self):
        updated, ordered = self.runner.validated_graph(self.graph, self.targets, self.selection)
        self.assertEqual(ordered, self.targets['modules'])
        self.assertEqual(len(ordered), 69)
        self.assertEqual(len(updated['modules']), 377)
        self.assertEqual(updated['roots'], self.graph['roots'])
        self.assertEqual(self.selection['changed_audit_targets'], [])
        self.assertEqual(self.selection['changed_dependency_only_modules'], list(self.runner.EXPECTED_REPAIRS))
        affected = set(self.prepare.affected_modules(self.graph, self.runner.EXPECTED_REPAIRS))
        self.assertEqual(affected, set(self.previous['compile_summary']['failed_or_blocked']))
        self.assertEqual(len(affected), 28)
        accepted = {name for name, row in self.previous['audit_summary']['modules'].items() if row['accepted']}
        self.assertEqual(len(accepted), 46)
        self.assertFalse(accepted & affected)
        self.assertEqual(377 - len(affected), 349)

    def test_complete_terminal_stdout_reconstructs_the_exact_selected_bytes(self):
        text = (self.prepare.RECEIPT.parent / 'TASK_STDOUT.log').read_text()
        prefix = 'P25_ROUND8_RESULT '
        lines = [line[len(prefix):] for line in text.splitlines() if line.startswith(prefix)]
        self.assertEqual(len(lines), 1)
        terminal = json.loads(lines[0])
        expected = (json.dumps(terminal, indent=2, sort_keys=True) + '\n').encode()
        self.assertEqual(expected, self.prepare.RECEIPT.read_bytes())
        self.assertEqual(self.prepare.digest(expected), self.runner.PRIOR_RESULT_SHA)
        provenance = json.loads((self.prepare.RECEIPT.parent / 'RESULT_PROVENANCE.json').read_bytes())
        self.assertIs(provenance['independent_remote_file_digest_received'], False)
        self.assertIs(self.selection['round8_terminal_result']['derived_from_complete_task_stdout'], True)
        self.assertIs(self.selection['round8_terminal_result']['independent_remote_file_digest_received'], False)

    def test_original_remote_hash_gate_precedes_all_mutation_and_stale_rounds_are_rejected(self):
        code = (ROOT / self.runner.RUNNER).read_text()
        gate = code.index('require(sha(prior_result_path) == PRIOR_RESULT_SHA')
        for marker in ['out.mkdir(parents=True, exist_ok=False)',
                       "subprocess.check_call(['git', 'checkout', '--detach'",
                       "state['compile_exit'] = original.logged_call"]:
            self.assertLess(gate, code.index(marker))
        prior_selection = json.loads((ROOT / self.runner.ROUND8_SELECTION).read_bytes())
        bad = copy.deepcopy(self.previous)
        bad['runner_sha256'] = self.runner.ROUND7_RUNNER_SHA
        with self.assertRaisesRegex(RuntimeError, 'source/control'):
            self.runner.validate_previous_result(bad, self.graph['roots'], self.targets['modules'], prior_selection)
        bad = copy.deepcopy(self.previous)
        bad['audit_summary']['accepted'] = 45
        with self.assertRaisesRegex(RuntimeError, 'owned result'):
            self.runner.validate_previous_result(bad, self.graph['roots'], self.targets['modules'], prior_selection)


if __name__ == '__main__':
    unittest.main()
