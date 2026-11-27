"""Offline checks on the two real round-12 failures and the one added graph edge."""
import ast
import copy
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import re
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
VER = ROOT / 'docs/verification/20261127-p2-5-resumed'
THEN = PACK.with_name('20261127-p2-5-round12-candidate')


def module(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def read(path):
    return json.loads(path.read_bytes())


old = module(THEN / 'test_round12_delta.py')
r12 = old.r12
r13 = module(VER / 'run_p2_round13.py')
sel = read(PACK / 'SOURCE_SELECTION.json')
actual = read(VER / 'p2-round12/RUN_RESULT.json')


def table(name):
    source = (ROOT / 'ImbalancedChen' / (name + '.lean')).read_text()
    return [(label, tuple(Fraction(v.strip()) for v in vector.split(','))) for label, vector in
            re.findall(r'\("([^"]+)", !\[([^\]]+)\]\)', source)]


def graph():
    r9, view, targets, _ = old.helpers.prep.context()
    for n in range(9, 13):
        driver = r12 if n == 12 else module(ROOT / getattr(r12, f'ROUND{n}_RUNNER'))
        selection = read(THEN / 'SOURCE_SELECTION.json') if n == 12 else read(ROOT / getattr(r12, f'ROUND{n}_SELECTION'))
        view, _ = driver.validated_graph(view, targets, selection)
    return view, targets


class Round13Delta(unittest.TestCase):
    def test_exact_source_rows_and_public_headers(self):
        h3 = table('P4AOriginalH3SourceDefinitions')
        self.assertEqual(len(h3), 12 * 99)
        keys = {18: 'new region H3 above D23', 19: 'new cap improvement', 36: 'previous H1 strictly below D23'}
        for idx, name in keys.items():
            common = {h3[99 * cell + idx] for cell in range(12)}
            self.assertEqual(common, {(name, h3[idx][1])})
        self.assertEqual((h3[19][1][4], h3[20][1][4]), (0, -2))
        seed = table('P4AOriginalSeed7Unequal15SourceDefinitions')[:96]
        self.assertEqual(seed[13][0], 'old H7 below L3')
        self.assertEqual(seed[16][0], 'new cap improvement')
        for row in sel['changed_modules']:
            before = (PACK / 'before' / row['source']).read_text()
            after = (PACK / 'after' / row['source']).read_text()
            self.assertEqual(r13.sha(PACK / 'before' / row['source']), row['before_sha256'])
            self.assertEqual(r13.sha(PACK / 'after' / row['source']), row['after_sha256'])
            decl = r'^(?:theorem|def)\s+\w+.*?:='
            self.assertEqual(re.findall(decl, before, re.M | re.S), re.findall(decl, after, re.M | re.S))
            self.assertEqual(old.helpers.imports(before), row['imports_before'])
            self.assertEqual(old.helpers.imports(after), row['imports_after'])
            self.assertEqual(old.helpers.prep.option_commands(old.helpers.source_tokens(before)),
                             old.helpers.prep.option_commands(old.helpers.source_tokens(after)))
            self.assertIsNone(re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', old.helpers.source_tokens(after)))
            if row['module'] == r13.H3_OWNER:
                self.assertIn('P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3', after)
                self.assertNotIn('private theorem', after)
            else:
                vectors = re.findall(r'^private theorem seed_(?:history|improvement)_row.*?!\[([^\]]+)\] := by\n  rfl',
                                     after, re.M | re.S)
                self.assertEqual([tuple(Fraction(v.strip()) for v in vec.split(',')) for vec in vectors],
                                 [seed[13][1], seed[16][1]])
                self.assertIn('firstExitDepthSplicePolicy_absorb]', after)

    def test_only_previously_accepted_semantics_edge_is_admitted(self):
        before, targets = graph()
        updated, ordered = r13.validated_graph(before, targets, sel)
        self.assertEqual(set(ordered), set(targets['modules']))
        self.assertEqual(ordered[:2], list(r13.EXPECTED_REPAIRS))
        self.assertEqual(set(updated['modules']), set(before['modules']))
        self.assertEqual(len(updated['modules']), 377)
        self.assertEqual(len(ordered), 69)
        changed_edges = [n for n in before['modules'] if updated['modules'][n]['imports'] != before['modules'][n]['imports']]
        self.assertEqual(changed_edges, [r13.H3_OWNER])
        self.assertEqual(len(r13.project_reach(before, [r13.H3_OWNER])), 228)
        self.assertEqual(len(r13.project_reach(updated, [r13.H3_OWNER])), 260)
        self.assertEqual(r13.project_reach(updated, updated['roots']), set(before['modules']))
        failed = set(actual['compile_summary']['failed_or_blocked'])
        self.assertEqual(len(failed), 20)
        self.assertEqual(set(old.helpers.prep.affected_modules(updated, r13.EXPECTED_REPAIRS)), failed)
        self.assertEqual(actual['audit_summary']['modules'][r13.H3_PROVIDER],
                         {'accepted': True, 'reused': True, 'declarations': 174})
        self.assertEqual(failed & set(ordered), set(sel['affected_owned_targets']))
        for unwanted in ('ImbalancedChen.Unlisted', r13.H3_OWNER, r13.H3_LITERAL):
            broken = copy.deepcopy(sel)
            broken['changed_modules'][1]['imports_after'][1] = unwanted
            with self.subTest(unwanted=unwanted), self.assertRaises(RuntimeError):
                r13.validated_graph(before, targets, broken)
        cycle = copy.deepcopy(before)
        cycle['modules'][r13.H3_PROVIDER]['imports'].append(r13.H3_OWNER)
        with self.assertRaisesRegex(RuntimeError, 'cyclic'):
            r13.validated_graph(cycle, targets, sel)

    def test_real_previous_result_and_unchanged_no_rerun_checks(self):
        g, targets = graph()
        prior = read(THEN / 'SOURCE_SELECTION.json')
        args = (g['roots'], targets['modules'], prior)
        r13.validate_previous_result(actual, *args)
        self.assertEqual(r13.sha(VER / 'p2-round12/RUN_RESULT.json'), r13.PRIOR_RESULT_SHA)
        for key in sel['prior_postflight_checks']:
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                r13.validate_previous_result(dict(actual, **{key: False}), *args)
        self.assertEqual(len(sel['prior_postflight_checks']), 9)
        self.assertEqual((sel['qualified_normal_reuse_candidates'], sel['qualified_owned_reuse_candidates']),
                         (actual['compile_summary']['successful_closure'], actual['audit_summary']['accepted']))
        current = [ast.parse((VER / f'run_p2_round{n}.py').read_bytes()) for n in (12, 13)]
        for name in ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight',
                     'verify_sources', 'validate_repair_failures'):
            bodies = [next(ast.dump(v) for v in tree.body if getattr(v, 'name', None) == name) for tree in current]
            self.assertEqual(*bodies)


if __name__ == '__main__':
    unittest.main()
