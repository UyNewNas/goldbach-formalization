"""Check the physical source identities, single-owner repair and no-rerun gates without running Lean."""
import ast
import copy
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path
import re
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
VER = ROOT / 'docs/verification/20261127-p2-5-resumed'
PRIOR = PACK.with_name('20261127-p2-5-round14-candidate')
ORIGIN = VER / 'p2-round14'
OWNER = 'ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7'


def read(path):
    return json.loads(path.read_bytes())


def module(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


old = module(PRIOR / 'test_round14_delta.py')
r14 = old.r14
r15 = module(VER / 'run_p2_round15.py')
selection = read(PACK / 'SOURCE_SELECTION.json')
terminal = read(ORIGIN / 'RUN_RESULT.json')


def g14():
    g12, targets = old.old.graph()
    g13, _ = old.r13.validated_graph(g12, targets, read(old.PRIOR / 'SOURCE_SELECTION.json'))
    return r14.validated_graph(g13, targets, read(PRIOR / 'SOURCE_SELECTION.json'))[0], targets


class Round15Delta(unittest.TestCase):
    def test_physical_rows_and_selected_branches(self):
        row, = selection['changed_modules']
        files = {side: PACK / side / row['source'] for side in ('before', 'after')}
        for side, file in files.items():
            self.assertEqual(r15.sha(file), row[f'{side}_sha256'])
        pre, post = files['before'].read_text(), files['after'].read_text()
        # Declaration headers and every data definition are unaltered. The unresolved
        # preimage auto-implicit C is deliberately bound to the real descending plane.
        before_headers = re.findall(r'^(?:private )?theorem [\s\S]+? := by', pre, re.M)
        after_headers = re.findall(r'^(?:private )?theorem [\s\S]+? := by', post, re.M)
        self.assertEqual(before_headers, after_headers)
        self.assertEqual(post.count('open VariableEnvelope (C)'), 1)
        self.assertNotIn('open VariableEnvelope (C)', pre)
        values = {}
        for tag in [14, 16, 17, 58]:
            pattern = rf'def cell0Row{tag} : Fin 9 → ℚ :=\s*!\[([^\]]+)\]'
            original = re.search(pattern, pre).group(1)
            self.assertEqual(re.search(pattern, post).group(1), original)
            values[tag] = tuple(Q(v.strip()) for v in original.split(','))
        # The origin and eight basis vectors distinguish all affine functions on Q^8.
        for axis in range(-1, 8):
            t = [Q(int(i == axis)) for i in range(8)]
            d, s = t[1] + t[2], t[0] + t[7]
            expr = {14: 2*(d-Q(25,128)), 17: 2*(Q(25,128)-s),
                    16: (1+s)/2-Q(1,1000000)-(Q(57,64)-Q(3,2)*d)}
            for tag in expr:
                c = values[tag]
                self.assertEqual(c[0] + sum(a*b for a,b in zip(c[1:], t)), expr[tag])
        source = (ROOT / 'ImbalancedChen/P4AOriginalSeed7Unequal15SourceDefinitions.lean').read_text()
        seedrows = source.split('def seed7Rows : Fin 96', 1)[1].split('\n  ]', 1)[0]
        name, data = re.findall(r'\("([^"]+)", !\[([^\]]+)\]\)', seedrows)[58]
        self.assertEqual(name, 'old subset 26 chosen plane 1 below R6')
        self.assertIn('![' + data + '] := by\n  rfl', post)
        dictionary = (ROOT / 'ImbalancedChen/P2OriginalAscendingEighthCapDictionary.lean').read_text()
        for lemma in ['old_descending_iff','ascending_half_iff','new_cap_ascending']:
            self.assertIn('theorem '+lemma+' ', dictionary)
            self.assertIn(lemma+' t', post)
        self.assertIn('if SelectedFamilyGuard patterns t ∧ CurrentParentGuard t (inheritedExponent lambda6 history)', dictionary)
        self.assertIn('  lambda6 (rosserAncestor 6 history)', dictionary)
        self.assertIn('exact if_pos ⟨ha, hparent⟩', post)
        self.assertIn('rw [slot15_source_identity, if_neg hnot]', post)

    def test_scope_and_source_failures(self):
        graph, targets = g14()
        after, order = r15.validated_graph(graph, targets, selection)
        self.assertEqual((order[0], len(order), len(after['modules'])), (OWNER, 69, 377))
        for name in graph['modules']:
            self.assertEqual(graph['modules'][name]['imports'], after['modules'][name]['imports'])
        altered = [m for m in graph['modules'] if graph['modules'][m] != after['modules'][m]]
        self.assertEqual(altered, [OWNER])
        affected = set(old.old.old.helpers.prep.affected_modules(after, [OWNER]))
        self.assertEqual(affected, set(terminal['compile_summary']['failed_or_blocked']))
        self.assertEqual((len(affected), len(affected.intersection(order))), (18, 18))
        self.assertEqual(r15.validate_repair_failures(selection, terminal['compile_summary'],
            (ORIGIN/'COMPILE.log').read_text()), [OWNER])
        bad = copy.deepcopy(selection)
        bad['changed_modules'][0]['imports_after'].append('ImbalancedChen.New')
        with self.assertRaises(RuntimeError):
            r15.validated_graph(graph, targets, bad)
        bad = copy.deepcopy(selection)
        bad['changed_modules'][0]['module'] = 'ImbalancedChen.P4AOriginalAscendingCell0Literal96'
        with self.assertRaises(RuntimeError):
            r15.validate_repair_failures(bad, terminal['compile_summary'], (ORIGIN/'COMPILE.log').read_text())

    def test_terminal_receipt_and_no_reruns(self):
        self.assertEqual(r15.sha(ORIGIN/'RUN_RESULT.json'), r15.PRIOR_RESULT_SHA)
        for f, key in [('COMPILE.log','compile_log_sha256'), ('AUDIT.log','audit_log_sha256')]:
            self.assertEqual(r15.sha(ORIGIN/f), terminal[key])
        graph, targets = g14()
        args = (graph['roots'], targets['modules'], read(PRIOR/'SOURCE_SELECTION.json'))
        r15.validate_previous_result(terminal, *args)
        self.assertEqual((selection['qualified_normal_reuse_candidates'],
                          selection['qualified_owned_reuse_candidates']), (359,51))
        self.assertEqual(len(selection['prior_postflight_checks']),9)
        for field in selection['prior_postflight_checks']:
            with self.assertRaises(RuntimeError):
                r15.validate_previous_result(dict(terminal, **{field: False}), *args)
        for name in ['validate_reuse','normal_reuse_postflight','owned_reuse_postflight',
                     'verify_sources','validate_repair_failures']:
            bodies = []
            for n in (14,15):
                tree = ast.parse((VER / f'run_p2_round{n}.py').read_bytes())
                bodies.append(next(ast.dump(f) for f in tree.body if getattr(f,'name',None)==name))
            self.assertEqual(*bodies)


if __name__ == '__main__':
    unittest.main()
