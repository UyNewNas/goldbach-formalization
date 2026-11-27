"""Round-12 source, historical and changed-owned-target checks. Does not run Lean."""
import ast
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import unittest

PACK = Path(__file__).resolve().parent
ROOT = PACK.parents[2]
VERIFY = ROOT / 'docs/verification/20261127-p2-5-resumed'
PREVIOUS = ROOT / 'docs/source-only/20261127-p2-5-round11-candidate'


def module(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


def read(path):
    return json.loads(path.read_bytes())


helpers = module(PREVIOUS / 'test_round11_delta.py')
r11 = helpers.r11
r12 = module(VERIFY / 'run_p2_round12.py')
selection = read(PACK / 'SOURCE_SELECTION.json')
result_dir = VERIFY / 'p2-round11'
actual = read(result_dir / 'RUN_RESULT.json')


class Round12Delta(unittest.TestCase):
    def test_four_arguments_are_the_exact_sixth_cap_inputs(self):
        row, = selection['changed_modules']
        before = (PACK / 'before' / row['source']).read_text()
        after = (PACK / 'after' / row['source']).read_text()
        published = subprocess.check_output(['git', 'show', r12.PREVIOUS + ':' + row['source']], cwd=ROOT)
        self.assertEqual(before.encode(), published)
        self.assertEqual(hashlib.sha256(after.encode()).hexdigest(), row['after_sha256'])
        start = before.index('  finiteMax allCells.toFinset\n', before.index('def sixthSourceCap'))
        args = before[start:before.index('\n\n', start)].removeprefix('  finiteMax ')
        old = '  exact finiteMax_row_le _ _ _ _ c'
        self.assertEqual(before.count(old), 1)
        self.assertEqual(before.replace(old, '  exact finiteMax_row_le ' + args + ' c'), after)
        self.assertEqual(helpers.imports(before), helpers.imports(after))
        self.assertEqual(len(helpers.imports(after)), 3)
        self.assertEqual(len(re.findall(r'^def ', after, re.M)), 7)
        self.assertEqual(len(re.findall(r'^theorem ', after, re.M)), 6)
        self.assertEqual(helpers.prep.option_commands(helpers.source_tokens(before)),
                         helpers.prep.option_commands(helpers.source_tokens(after)))
        self.assertIsNone(re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', helpers.source_tokens(after)))

    def test_owner_is_prioritized_without_changing_69_target_set(self):
        r9, g8, targets, _ = helpers.prep.context()
        g9, _ = r9.validated_graph(g8, targets, read(ROOT / r11.ROUND9_SELECTION))
        g10, _ = helpers.r10.validated_graph(g9, targets, read(ROOT / r11.ROUND10_SELECTION))
        g11, _ = r11.validated_graph(g10, targets, read(PREVIOUS / 'SOURCE_SELECTION.json'))
        g12, ordered = r12.validated_graph(g11, targets, selection)
        owner, = r12.EXPECTED_REPAIRS
        self.assertEqual([n for n in g11['modules'] if g11['modules'][n] != g12['modules'][n]], [owner])
        self.assertEqual(ordered, [owner] + [n for n in targets['modules'] if n != owner])
        self.assertEqual((len(g12['modules']), len(ordered)), (377, 69))
        affected = helpers.prep.affected_modules(g11, [owner])
        self.assertEqual(affected, selection['affected_closure'])
        self.assertEqual(affected, sorted(actual['compile_summary']['failed_or_blocked']))
        self.assertEqual(len(affected), 21)
        self.assertEqual(set(affected) & set(ordered), set(selection['affected_owned_targets']))
        self.assertEqual(selection['qualified_normal_reuse_candidates'], 356)
        self.assertEqual(selection['qualified_owned_reuse_candidates'], actual['audit_summary']['accepted'])
        broken = dict(selection, changed_audit_targets=[], changed_dependency_only_modules=[owner])
        with self.assertRaises(RuntimeError):
            r12.validated_graph(g11, targets, broken)
        args = (g11['roots'], targets['modules'], read(PREVIOUS / 'SOURCE_SELECTION.json'))
        r12.validate_previous_result(actual, *args)
        self.assertEqual(r12.PRIOR_RESULT_SHA, r12.sha(result_dir / 'RUN_RESULT.json'))
        self.assertEqual(r12.sha(result_dir / 'COMPILE.log'), actual['compile_log_sha256'])
        self.assertEqual(r12.sha(result_dir / 'AUDIT.log'), actual['audit_log_sha256'])
        self.assertEqual(len(selection['prior_postflight_checks']), 9)
        for key in selection['prior_postflight_checks']:
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                r12.validate_previous_result(dict(actual, **{key: False}), *args)
        for section, key in [('compile_summary', 'reused'), ('compile_summary', 'successful_closure'),
                             ('audit_summary', 'accepted')]:
            bad = copy.deepcopy(actual)
            bad[section][key] -= 1
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                r12.validate_previous_result(bad, *args)

    def test_existing_reuse_preflight_and_postflights_are_identical(self):
        def bodies(path):
            return {n.name: ast.dump(n) for n in ast.parse(path.read_bytes()).body if isinstance(n, ast.FunctionDef)}
        previous = bodies(VERIFY / 'run_p2_round11.py')
        current = bodies(VERIFY / 'run_p2_round12.py')
        for name in ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight',
                     'verify_sources', 'validate_repair_failures'):
            self.assertEqual(previous[name], current[name])


if __name__ == '__main__':
    unittest.main()
