"""Test the single-source round-11 continuation without starting Lean."""
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
VERIFY = ROOT / 'docs/verification/20261127-p2-5-resumed'
TEN = ROOT / 'docs/source-only/20261127-p2-5-round10-candidate'
sys.path.insert(0, str(ROOT / 'verification/part2'))
from inspect_winner9_owner_native import imports, source_tokens
from run_winner9_private_audit import project_nodes


def module(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def get(path):
    return json.loads(path.read_bytes())


def commit_file(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + str(path)], cwd=ROOT)


r11 = module(VERIFY / 'run_p2_round11.py')
r10 = module(VERIFY / 'run_p2_round10.py')
prep = module(ROOT / 'docs/source-only/20261126-p2-5-round9-candidates/prepare_p2_round9.py')
result_dir = VERIFY / 'p2-round10'
prior = get(result_dir / 'RUN_RESULT.json')
sel = get(PACK / 'SOURCE_SELECTION.json')


class Round11Delta(unittest.TestCase):
    def test_original_target_uses_exact_previous_donor_body(self):
        row, = sel['changed_modules']
        before = (PACK / 'before' / row['source']).read_bytes()
        after = (PACK / 'after' / row['source']).read_bytes()
        self.assertEqual(before, commit_file(r11.PREVIOUS, row['source']))
        self.assertEqual(hashlib.sha256(after).hexdigest(), row['after_sha256'])
        donor = commit_file(r11.PREVIOUS, 'ImbalancedChen/P4AOriginalVariableFifthPhysicalLedger.lean')
        start = donor.index(b'theorem fifth_even (')
        donor_body = donor[start:donor.index(b'\n\n', start)].split(b' := by\n', 1)[1]
        self.assertEqual(hashlib.sha256(donor_body).hexdigest(),
                         'ba64c488a4dbefded4d9ade39bc8bda43c059d464c25b661fbd200436b2880f5')
        faulty = (b'  apply fifthCappedUpperPolicy_even_retained\n  intro history\n'
                  b'  simp [HistoricalThirdCoarse.initialPolicy, oddFirstExitPolicy]')
        self.assertEqual(before.count(faulty), 1)
        self.assertEqual(before.replace(faulty, donor_body), after)
        self.assertEqual(imports(before.decode()), imports(after.decode()))
        self.assertEqual(len(imports(after.decode())), 3)
        self.assertEqual(prep.option_commands(source_tokens(before.decode())),
                         prep.option_commands(source_tokens(after.decode())))
        self.assertIsNone(re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', source_tokens(after.decode())))
        nodes = project_nodes(ROOT, row['module'])
        self.assertEqual(len(nodes), 220)
        self.assertNotIn('ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger', nodes)
        self.assertNotIn('ImbalancedChen.ActualUpperPolicyDensity', nodes)
        self.assertIn('ImbalancedChen.P1OriginalFifthAttainedRowBinding', nodes)
        self.assertIn('ImbalancedChen.ActualUpperPolicyFiniteBridge', nodes)

    def test_terminal_digests_scope_and_all_nine_prior_postflights(self):
        r9, g8, targets, _ = prep.context()
        g9, _ = r9.validated_graph(g8, targets, get(ROOT / r10.ROUND9_SELECTION))
        g10, _ = r10.validated_graph(g9, targets, get(TEN / 'SOURCE_SELECTION.json'))
        g11, ordered = r11.validated_graph(g10, targets, sel)
        changed = [name for name in g10['modules'] if g10['modules'][name] != g11['modules'][name]]
        self.assertEqual(changed, list(r11.EXPECTED_REPAIRS))
        self.assertEqual(ordered, targets['modules'])
        self.assertEqual(prep.affected_modules(g10, changed), sel['affected_closure'])
        self.assertEqual(set(sel['affected_closure']), set(prior['compile_summary']['failed_or_blocked']))
        self.assertEqual(set(ordered) & set(sel['affected_closure']), set(sel['affected_owned_targets']))
        self.assertEqual((len(g11['modules']), len(ordered), len(sel['affected_closure']),
                          sel['qualified_normal_reuse_candidates']), (377, 69, 22, 355))
        self.assertEqual(sel['qualified_owned_reuse_candidates'], prior['audit_summary']['accepted'])
        self.assertEqual(r11.sha(result_dir / 'RUN_RESULT.json'), r11.PRIOR_RESULT_SHA)
        self.assertEqual(r11.sha(result_dir / 'COMPILE.log'), prior['compile_log_sha256'])
        self.assertEqual(r11.sha(result_dir / 'AUDIT.log'), prior['audit_log_sha256'])
        self.assertEqual(r11.validate_repair_failures(sel, prior['compile_summary'],
                         (result_dir / 'COMPILE.log').read_text()), changed)
        args = (g10['roots'], ordered, get(TEN / 'SOURCE_SELECTION.json'))
        r11.validate_previous_result(prior, *args)
        self.assertEqual(len(sel['prior_postflight_checks']), 9)
        for key in sel['prior_postflight_checks']:
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                r11.validate_previous_result(dict(prior, **{key: False}), *args)
        for section, key in [('compile_summary', 'reused'), ('compile_summary', 'successful_closure'),
                             ('audit_summary', 'accepted')]:
            corrupted = copy.deepcopy(prior)
            corrupted[section][key] -= 1
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                r11.validate_previous_result(corrupted, *args)

    def test_reuse_qualification_and_actual_execution_gates_unchanged(self):
        def functions(path):
            return {n.name: ast.dump(n) for n in ast.parse(path.read_bytes()).body if isinstance(n, ast.FunctionDef)}
        current = functions(VERIFY / 'run_p2_round11.py')
        previous = functions(VERIFY / 'run_p2_round10.py')
        for guard in ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight',
                      'verify_sources', 'validate_repair_failures'):
            self.assertEqual(current[guard], previous[guard])
        actual = r11.normal_reuse_postflight(['ImbalancedChen.Old', 'ImbalancedChen.Fresh'],
                         ['ImbalancedChen.Fresh'], {}, {}, dict(failed_or_blocked=[], pending=[], reused=2,
                         successful_closure=2), 'START ImbalancedChen.Old\n')
        self.assertFalse(actual[0])
        self.assertFalse(r11.owned_reuse_postflight({'ImbalancedChen.Old': dict(accepted=True, declarations=2)},
                         {'modules': {'ImbalancedChen.Old': dict(accepted=True, reused=False, declarations=2)}},
                         'AUDIT ImbalancedChen.Old\n')[0])


if __name__ == '__main__':
    unittest.main()
