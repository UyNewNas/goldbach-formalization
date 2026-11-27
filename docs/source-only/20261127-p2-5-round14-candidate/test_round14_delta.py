"""Validate two terminal-error changes without repeating any Lean gate."""
import ast
import copy
import importlib.util
import json
from pathlib import Path
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
VER = ROOT / 'docs/verification/20261127-p2-5-resumed'
PRIOR = PACK.with_name('20261127-p2-5-round13-candidate')


def module(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    obj = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj


def read(p):
    return json.loads(p.read_bytes())


old = module(PRIOR / 'test_round13_delta.py')
r13 = old.r13
r14 = module(VER / 'run_p2_round14.py')
sel = read(PACK / 'SOURCE_SELECTION.json')
origin = VER / 'p2-round13'
actual = read(origin / 'RUN_RESULT.json')


class Round14Delta(unittest.TestCase):
    def test_source_changes_are_the_two_reported_goals(self):
        for row in sel['changed_modules']:
            pre = (PACK / 'before' / row['source']).read_text()
            post = (PACK / 'after' / row['source']).read_text()
            if row['module'] == r14.H3_OWNER:
                earlier = '  · obtain ⟨_, i, hrows, _, hparent⟩ := h\n    simp only [selectedCap, if_pos h]'
                later = '  · simp only [selectedCap, if_pos h]\n    obtain ⟨_, i, hrows, _, hparent⟩ := h'
                self.assertIn('P4AOriginalFirstFailureH3SourceSemantics.sourceAffineGuard_iff_StrictH3', post)
            else:
                earlier = ('    P4AOriginalActualElevenSixthCandidate.sixthSourceLevel, actualSixth,\n'
                           '    firstExitDepthSplicePolicy_absorb]')
                later = '    actualSixth, firstExitDepthSplicePolicy_absorb]\n  rfl'
                provider = (ROOT / 'ImbalancedChen/P4AOriginalActualElevenSixthCandidate.lean').read_text()
                self.assertIn('def sixthSourceLevel (pre : List ℕ) : ℝ :=\n  N ^ sixthSourceCap ', provider)
            self.assertEqual(pre.count(earlier), 1)
            self.assertEqual(pre.replace(earlier, later), post)
            self.assertEqual(r14.sha(PACK / 'before' / row['source']), row['before_sha256'])
            self.assertEqual(r14.sha(PACK / 'after' / row['source']), row['after_sha256'])
            self.assertEqual(row['imports_before'], row['imports_after'])

    def test_no_new_edges_and_previously_accepted_provider_remains_frozen(self):
        g12, targets = old.graph()
        g13, _ = r13.validated_graph(g12, targets, read(PRIOR / 'SOURCE_SELECTION.json'))
        g14, order = r14.validated_graph(g13, targets, sel)
        self.assertEqual(order, list(r14.EXPECTED_REPAIRS) +
                         [name for name in targets['modules'] if name not in r14.EXPECTED_REPAIRS])
        self.assertEqual((len(order), len(g14['modules'])), (69, 377))
        for name, row in g13['modules'].items():
            self.assertEqual(row['imports'], g14['modules'][name]['imports'])
        self.assertEqual(r14.project_reach(g13, [r14.H3_OWNER]), r14.project_reach(g14, [r14.H3_OWNER]))
        self.assertEqual(len(r14.project_reach(g14, [r14.H3_OWNER])), 260)
        self.assertEqual(actual['audit_summary']['modules'][r14.H3_PROVIDER],
                         dict(accepted=True, reused=True, declarations=174))
        for i in (0, 1):
            bad = copy.deepcopy(sel)
            bad['changed_modules'][i]['imports_after'].append('ImbalancedChen.Other')
            with self.assertRaises(RuntimeError):
                r14.validated_graph(g13, targets, bad)
        self.assertEqual(set(old.old.helpers.prep.affected_modules(g14, r14.EXPECTED_REPAIRS)),
                         set(actual['compile_summary']['failed_or_blocked']))
        prior_sel = read(PRIOR / 'SOURCE_SELECTION.json')
        args = (g13['roots'], targets['modules'], prior_sel)
        r14.validate_previous_result(actual, *args)
        for key in sel['prior_postflight_checks']:
            with self.assertRaises(RuntimeError):
                r14.validate_previous_result(dict(actual, **{key: False}), *args)

    def test_actual_runtime_evidence_and_reuse_guards(self):
        self.assertEqual(r14.sha(origin / 'RUN_RESULT.json'), r14.PRIOR_RESULT_SHA)
        for f, key in [('COMPILE.log', 'compile_log_sha256'), ('AUDIT.log', 'audit_log_sha256')]:
            self.assertEqual(r14.sha(origin / f), actual[key])
        self.assertEqual(r14.validate_repair_failures(sel, actual['compile_summary'], (origin / 'COMPILE.log').read_text()),
                         list(r14.EXPECTED_REPAIRS))
        self.assertEqual((sel['qualified_normal_reuse_candidates'], sel['qualified_owned_reuse_candidates']),
                         (357, 49))
        self.assertEqual(len(sel['prior_postflight_checks']), 9)
        for name in ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight',
                     'verify_sources', 'validate_repair_failures'):
            bodies = []
            for n in (13, 14):
                tree = ast.parse((VER / f'run_p2_round{n}.py').read_bytes())
                bodies.append(next(ast.dump(f) for f in tree.body if getattr(f, 'name', None) == name))
            self.assertEqual(*bodies)


if __name__ == '__main__':
    unittest.main()
