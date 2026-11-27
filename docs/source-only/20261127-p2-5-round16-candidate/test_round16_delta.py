"""Bind the reduction to the real final goal and the unchanged normal/owned reuse gates."""
import ast
import copy
import importlib.util
import json
from pathlib import Path
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
PRIOR = PACK.with_name('20261127-p2-5-round15-candidate')
VER = ROOT / 'docs/verification/20261127-p2-5-resumed'
ORIGIN = VER / 'p2-round15'


def load(p):
    spec = importlib.util.spec_from_file_location(p.stem, p)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def read(p):
    return json.loads(p.read_bytes())


old = load(PRIOR / 'test_round15_delta.py')
r16 = load(VER / 'run_p2_round16.py')
selection = read(PACK / 'SOURCE_SELECTION.json')
prior_selection = read(PRIOR / 'SOURCE_SELECTION.json')
terminal = read(ORIGIN / 'RUN_RESULT.json')
owner = 'ImbalancedChen.P4AOriginalAscendingCell0AfterSeed7'


def g15():
    g14, targets = old.g14()
    return old.r15.validated_graph(g14, targets, prior_selection)[0], targets


class Round16Delta(unittest.TestCase):
    def test_only_the_actual_let_reduction_is_changed(self):
        row, = selection['changed_modules']
        self.assertEqual(row['module'], owner)
        before = PACK / 'before' / row['source']
        after = PACK / 'after' / row['source']
        self.assertEqual(r16.sha(before), row['before_sha256'])
        self.assertEqual(r16.sha(after), row['after_sha256'])
        self.assertEqual(before.read_bytes(), (PRIOR/'after'/row['source']).read_bytes())
        line = '  simp only [slot16, h15, h16, max_eq_right hle]\n'
        self.assertEqual(before.read_text().count(line), 1)
        self.assertEqual(before.read_text().replace(line, line+'  rfl\n'), after.read_text())
        self.assertIn('  let t := primeHistoryLogCoordinates N 8 pre', after.read_text())
        failure_logs = list((ORIGIN/'failures').glob('*.log'))
        self.assertEqual(len(failure_logs), 1)
        log = failure_logs[0].read_text()
        self.assertEqual(log.count(': error:'), 1)
        self.assertIn('⊢ P2OriginalAscendingEighthCapDictionary.M t =\n'
                      '    P2OriginalAscendingEighthCapDictionary.M (primeHistoryLogCoordinates N 8 pre)', log)

    def test_protected_scope(self):
        before, targets = g15()
        after, order = r16.validated_graph(before, targets, selection)
        self.assertEqual((len(order), len(after['modules']), order[0]), (69,377,owner))
        self.assertEqual([m for m in before['modules'] if before['modules'][m] != after['modules'][m]], [owner])
        self.assertEqual(before['modules'][owner]['imports'], after['modules'][owner]['imports'])
        self.assertEqual(set(old.old.old.old.helpers.prep.affected_modules(after,[owner])),
                         set(terminal['compile_summary']['failed_or_blocked']))
        self.assertEqual((len(selection['affected_closure']),len(selection['affected_owned_targets'])), (18,18))
        self.assertEqual((selection['qualified_normal_reuse_candidates'],selection['qualified_owned_reuse_candidates']), (359,51))
        self.assertEqual(r16.validate_repair_failures(selection, terminal['compile_summary'], (ORIGIN/'COMPILE.log').read_text()), [owner])
        candidate = copy.deepcopy(selection)
        candidate['changed_modules'][0]['module'] = 'ImbalancedChen.P4AOriginalAscendingCell0Literal96'
        with self.assertRaises(RuntimeError):
            r16.validate_repair_failures(candidate, terminal['compile_summary'], (ORIGIN/'COMPILE.log').read_text())

    def test_stock_guards_and_exact_terminal_receipt(self):
        self.assertEqual(r16.sha(ORIGIN/'RUN_RESULT.json'), r16.PRIOR_RESULT_SHA)
        for path, key in [('COMPILE.log','compile_log_sha256'),('AUDIT.log','audit_log_sha256')]:
            self.assertEqual(r16.sha(ORIGIN/path), terminal[key])
        graph, targets = g15()
        args = (graph['roots'], targets['modules'], prior_selection)
        r16.validate_previous_result(terminal,*args)
        self.assertEqual(len(selection['prior_postflight_checks']),9)
        for field in selection['prior_postflight_checks']:
            with self.assertRaises(RuntimeError):
                r16.validate_previous_result(dict(terminal, **{field:False}),*args)
        for name in ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight', 'verify_sources', 'validate_repair_failures'):
            versions = []
            for n in (15,16):
                tree = ast.parse((VER/f'run_p2_round{n}.py').read_bytes())
                versions.append(next(ast.dump(f) for f in tree.body if getattr(f, 'name', None)==name))
            self.assertEqual(*versions)


if __name__ == '__main__':
    unittest.main()
