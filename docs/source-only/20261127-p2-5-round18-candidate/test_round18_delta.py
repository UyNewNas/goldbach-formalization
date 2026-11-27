"""Check proof/spec preservation, actual-failure scope, and inherited reuse gates."""
import ast
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest

sys.dont_write_bytecode = True
PACK = Path(__file__).resolve().parent
STAGED_ROOT = PACK.parents[2]
ROOT = Path(os.environ.get('P25_REPO_ROOT', str(STAGED_ROOT))).resolve()
RELVER = Path('docs/verification/20261127-p2-5-resumed')
VER = ROOT / RELVER
PRIOR = ROOT / 'docs/source-only/20261127-p2-5-round17-candidate'
ORIGIN = VER / 'p2-round17'
OWNER = 'ImbalancedChen.P4AOriginalCell0AffineChronology'
SOURCE = OWNER.replace('.', '/') + '.lean'
COMMIT = 'f0c80794844b7a1318eb386ce454988af1c678a3'
RESULT_SHA = '120597fd258b3add1f86174bec0149bfead4e1b17db3e096aec02ec2a5afbacb'
PROTECTED = ('validate_reuse', 'normal_reuse_postflight', 'owned_reuse_postflight',
             'verify_sources', 'validate_repair_failures')
POSTFLIGHTS = {'source_after_matches', 'gate_after_matches', 'runner_after_matches',
              'external_after_matches', 'head_after_matches', 'history_after_matches',
              'baseline_after_matches', 'prior_normal_reuse_after_matches',
              'prior_owned_reuse_after_matches'}


def load(path):
    name = 'round18_review_' + path.stem
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def read(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def affected_modules(graph, owners):
    affected = set(owners)
    while True:
        expanded = affected | {name for name, row in graph['modules'].items()
                               if affected.intersection(row['imports'])}
        if expanded == affected:
            return sorted(affected)
        affected = expanded


def function_ast(source, name):
    return next(ast.dump(node) for node in ast.parse(source).body
                if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and node.name == name)


def postflight_lists(source):
    result = []
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.List) and all(isinstance(x, ast.Constant) and isinstance(x.value, str)
                                              for x in node.elts):
            values = [x.value for x in node.elts]
            if values and all(value.endswith('_after_matches') for value in values):
                result.append(values)
    return result


old = load(PRIOR / 'test_round17_delta.py')
r17 = load(VER / 'run_p2_round17.py')
r18 = load(STAGED_ROOT / RELVER / 'run_p2_round18.py')
invariants = load(PACK / 'source_invariants.py')
selection = read(PACK / 'SOURCE_SELECTION.json')
prior_selection = read(PRIOR / 'SOURCE_SELECTION.json')
terminal = read(ORIGIN / 'RUN_RESULT.json')


def g17():
    graph16, targets = old.g16()
    return r17.validated_graph(graph16, targets, prior_selection)[0], targets


class Round18Delta(unittest.TestCase):
    def test_proof_only_guard_rejects_specification_changes(self):
        row, = selection['changed_modules']
        self.assertEqual((row['module'], row['source']), (OWNER, SOURCE))
        before_path, after_path = (PACK / stage / SOURCE for stage in ('before', 'after'))
        self.assertEqual(digest(before_path), row['before_sha256'])
        self.assertEqual(digest(after_path), row['after_sha256'])
        before, after = before_path.read_bytes(), after_path.read_bytes()
        self.assertEqual(before, subprocess.check_output(['git', 'show', COMMIT + ':' + SOURCE], cwd=ROOT))
        review = invariants.validate_proof_only(before, after)
        self.assertEqual(review, selection['proof_only_review'])
        self.assertEqual(review, read(PACK / 'PROOF_ONLY_REVIEW.json'))
        self.assertEqual(review['declaration_count'], 20)
        self.assertEqual(review['new_public_hypotheses'], 0)
        text = after.decode('utf-8')
        # These mutations must be rejected even though they are Lean-shaped and
        # can be placed next to the legitimately changed theorem proof bodies.
        header = 'OldPlaneRows (literalPattern 0) t := by'
        definition = 'if literalPattern 0 I then 0 else 25 / 64'
        self.assertEqual(text.count(header), 1)
        self.assertEqual(text.count(definition), 1)
        mutants = {
            'theorem result': text.replace(header, 'True := by'),
            'rational definition': text.replace(definition, 'if literalPattern 0 I then 0 else 26 / 64'),
            'extra import': 'import Mathlib.Data.Nat.Basic\n' + text,
            'option': text + '\nset_option maxHeartbeats 0\n',
        }
        for label, mutant in mutants.items():
            with self.subTest(mutation=label), self.assertRaises(RuntimeError):
                invariants.validate_proof_only(before, mutant.encode())

    def test_scope_guard_rejects_unexecuted_or_import_changes(self):
        before, targets = g17()
        after, order = r18.validated_graph(before, targets, selection)
        self.assertEqual((len(order), len(after['modules']), order[0]), (69, 377, OWNER))
        self.assertEqual([name for name in before['modules']
                          if before['modules'][name] != after['modules'][name]], [OWNER])
        self.assertEqual(before['modules'][OWNER]['imports'], after['modules'][OWNER]['imports'])
        affected = affected_modules(after, [OWNER])
        self.assertEqual(len(affected), 16)
        self.assertEqual(affected, selection['affected_closure'])
        self.assertEqual(affected, selection['affected_owned_targets'])
        self.assertEqual(affected, sorted(terminal['compile_summary']['failed_or_blocked']))
        self.assertEqual((selection['qualified_normal_reuse_candidates'],
                          selection['qualified_owned_reuse_candidates']), (361, 53))
        compile_log = (ORIGIN / 'COMPILE.log').read_text()
        self.assertEqual(r18.validate_repair_failures(selection, terminal['compile_summary'], compile_log), [OWNER])
        candidate = copy.deepcopy(selection)
        candidate['changed_modules'][0]['module'] = 'ImbalancedChen.P4AOriginalAscendingCell1Affine'
        with self.assertRaises(RuntimeError):
            r18.validate_repair_failures(candidate, terminal['compile_summary'], compile_log)
        candidate = copy.deepcopy(selection)
        candidate['changed_modules'][0]['imports_after'].append('ImbalancedChen.VariableEnvelope')
        with self.assertRaises(RuntimeError):
            r18.validated_graph(before, targets, candidate)

    def test_exact_terminal_and_protected_controller_guards(self):
        self.assertEqual(digest(ORIGIN / 'RUN_RESULT.json'), RESULT_SHA)
        self.assertEqual(r18.PRIOR_RESULT_SHA, RESULT_SHA)
        self.assertEqual(r18.PREVIOUS, COMMIT)
        self.assertEqual(r18.ROUND17_RUNNER_SHA, digest(VER / 'run_p2_round17.py'))
        self.assertEqual(r18.ROUND17_SELECTION_SHA, digest(PRIOR / 'SOURCE_SELECTION.json'))
        for path, key in [('COMPILE.log', 'compile_log_sha256'), ('AUDIT.log', 'audit_log_sha256')]:
            self.assertEqual(digest(ORIGIN / path), terminal[key])
        graph, targets = g17()
        args = (graph['roots'], targets['modules'], prior_selection)
        r18.validate_previous_result(terminal, *args)
        self.assertEqual(set(selection['prior_postflight_checks']), POSTFLIGHTS)
        self.assertTrue(all(value is True for value in selection['prior_postflight_checks'].values()))
        for field in POSTFLIGHTS:
            with self.subTest(guard=field), self.assertRaises(RuntimeError):
                r18.validate_previous_result(dict(terminal, **{field: False}), *args)
        with self.assertRaises(RuntimeError):
            r18.validate_previous_result(dict(terminal, ended_utc=None), *args)
        bad = copy.deepcopy(terminal)
        bad['compile_summary']['successful_closure'] -= 1
        with self.assertRaises(RuntimeError):
            r18.validate_previous_result(bad, *args)
        previous_source = (VER / 'run_p2_round17.py').read_text()
        next_source = (STAGED_ROOT / RELVER / 'run_p2_round18.py').read_text()
        for name in PROTECTED:
            self.assertEqual(function_ast(previous_source, name), function_ast(next_source, name), name)
        previous_gates, next_gates = postflight_lists(previous_source), postflight_lists(next_source)
        self.assertEqual(previous_gates, next_gates)
        self.assertEqual(len(next_gates), 2)
        self.assertTrue(all(len(gates) == 9 and set(gates) == POSTFLIGHTS for gates in next_gates))


if __name__ == '__main__':
    unittest.main()
