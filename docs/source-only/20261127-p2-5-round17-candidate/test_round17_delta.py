"""Bind four literal row projections to the real failed goals and the unchanged normal/owned reuse gates."""
import ast
import copy
import importlib.util
import json
import re
from pathlib import Path
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
PRIOR = PACK.with_name('20261127-p2-5-round16-candidate')
VER = ROOT / 'docs/verification/20261127-p2-5-resumed'
ORIGIN = VER / 'p2-round16'


def load(p):
    spec = importlib.util.spec_from_file_location(p.stem, p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def read(p):
    return json.loads(p.read_bytes())


old = load(PRIOR / 'test_round16_delta.py')
r17 = load(VER / 'run_p2_round17.py')
selection = read(PACK / 'SOURCE_SELECTION.json')
prior_selection = read(PRIOR / 'SOURCE_SELECTION.json')
terminal = read(ORIGIN / 'RUN_RESULT.json')
owner = 'ImbalancedChen.P4AOriginalAscendingCell0Literal96'
donor = 'ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7'


def g16():
    g15, targets = old.g15()
    return old.r16.validated_graph(g15, targets, prior_selection)[0], targets


class Round17Delta(unittest.TestCase):
    def test_four_source_vectors_and_exact_errors(self):
        row, = selection['changed_modules']
        self.assertEqual(row['module'], owner)
        before = PACK / 'before' / row['source']
        after = PACK / 'after' / row['source']
        self.assertEqual(r17.sha(before), row['before_sha256'])
        self.assertEqual(r17.sha(after), row['after_sha256'])
        original, repaired = before.read_text(), after.read_text()
        code = '  funext j\n  fin_cases j <;> decide'
        self.assertEqual(original.count(code), 4)
        self.assertEqual(original.replace(code, '  rfl'), repaired)
        rows = re.findall(r'\("([^"]+)", !\[([^\]]+)\]\)', original.split('def rows : Fin 96',1)[1].split('\n  ]',1)[0])
        self.assertEqual(len(rows), 96)
        source = (ROOT/(donor.replace('.','/')+'.lean')).read_text()
        for k, label in [(14,'old winner6 descending below ascending'),(16,'new cap improvement'),
                         (17,'new descending license buffered'),(58,'old subset 26 chosen plane 0 below R6')]:
            self.assertEqual(rows[k][0], label)
            vector = re.search(r'def cell0Row'+str(k)+r' : Fin 9 → ℚ :=\s*!\[([^\]]+)\]', source).group(1)
            self.assertEqual(rows[k][1], vector)
            self.assertEqual(len(vector.split(',')), 9)
            self.assertIn(f'private theorem row{k} : (rows {k}).2 = cell0Row{k} := by\n  rfl', repaired)
        failures = list((ORIGIN/'failures').glob('*.log'))
        self.assertEqual(len(failures), 1)
        messages = [line for line in failures[0].read_text().splitlines() if ': error:' in line]
        self.assertEqual({int(line.split(':')[1]) for line in messages}, {127,131,135,139})
        self.assertTrue(all(': error: Tactic `decide` failed for proposition' in line for line in messages))

    def test_protected_scope(self):
        before, targets = g16()
        after, order = r17.validated_graph(before, targets, selection)
        self.assertEqual((len(order), len(after['modules']), order[0]), (69,377,owner))
        self.assertEqual([m for m in before['modules'] if before['modules'][m] != after['modules'][m]], [owner])
        self.assertEqual(before['modules'][owner]['imports'], after['modules'][owner]['imports'])
        self.assertEqual(set(old.old.old.old.old.helpers.prep.affected_modules(after,[owner])),
                         set(terminal['compile_summary']['failed_or_blocked']))
        self.assertEqual((len(selection['affected_closure']),len(selection['affected_owned_targets'])), (17,17))
        self.assertEqual((selection['qualified_normal_reuse_candidates'],selection['qualified_owned_reuse_candidates']), (360,52))
        self.assertEqual(r17.validate_repair_failures(selection, terminal['compile_summary'], (ORIGIN/'COMPILE.log').read_text()), [owner])
        candidate = copy.deepcopy(selection)
        candidate['changed_modules'][0]['module'] = 'ImbalancedChen.P4AOriginalAscendingCell1Affine'
        with self.assertRaises(RuntimeError):
            r17.validate_repair_failures(candidate, terminal['compile_summary'], (ORIGIN/'COMPILE.log').read_text())

    def test_stock_guards_and_exact_terminal_receipt(self):
        self.assertEqual(r17.sha(ORIGIN/'RUN_RESULT.json'), r17.PRIOR_RESULT_SHA)
        for path, key in [('COMPILE.log','compile_log_sha256'),('AUDIT.log','audit_log_sha256')]:
            self.assertEqual(r17.sha(ORIGIN/path), terminal[key])
        graph, targets = g16()
        args = (graph['roots'], targets['modules'], prior_selection)
        r17.validate_previous_result(terminal,*args)
        self.assertEqual(len(selection['prior_postflight_checks']),9)
        for field in selection['prior_postflight_checks']:
            with self.assertRaises(RuntimeError):
                r17.validate_previous_result(dict(terminal, **{field:False}),*args)
        for name in ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight', 'verify_sources', 'validate_repair_failures'):
            versions = []
            for n in (16,17):
                tree = ast.parse((VER/f'run_p2_round{n}.py').read_bytes())
                versions.append(next(ast.dump(f) for f in tree.body if getattr(f, 'name', None)==name))
            self.assertEqual(*versions)


if __name__ == '__main__':
    unittest.main()
