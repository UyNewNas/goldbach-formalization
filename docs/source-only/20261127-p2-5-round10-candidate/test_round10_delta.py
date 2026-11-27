"""Targeted offline checks for the round-9 -> round-10 delta. No Lean invocation."""
from contextlib import ExitStack
import copy
from pathlib import Path
import json
import re
import shutil
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import importlib.util

ROOT = Path(__file__).resolve().parents[3]
PACK = Path(__file__).resolve().parent
RESULT = ROOT / 'docs/verification/20261127-p2-5-cell01-decoder/p2-round9'
sys.path.insert(0, str(ROOT / 'verification/part2'))
from inspect_winner9_owner_native import imports, source_tokens
import run_winner9_private_audit as audit
import run_winner9_private_checks as normal


def read_module(path):
    spec = importlib.util.spec_from_file_location(path.stem, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def read_json(path):
    return json.loads(path.read_bytes())


old = read_module(ROOT / 'docs/source-only/20261126-p2-5-round9-candidates/prepare_p2_round9.py')
runner = read_module(ROOT / 'docs/verification/20261127-p2-5-resumed/run_p2_round10.py')


class Round10Delta(unittest.TestCase):
    def test_real_history_graph_and_terminal_rejections(self):
        r9, graph8, targets, _ = old.context()
        prior_selection = read_json(ROOT / runner.ROUND9_SELECTION)
        graph9, _ = r9.validated_graph(graph8, targets, prior_selection)
        selection = read_json(PACK / 'SOURCE_SELECTION.json')
        graph10, ordered = runner.validated_graph(graph9, targets, selection)
        actual = read_json(RESULT / 'RUN_RESULT.json')
        self.assertEqual(runner.sha(RESULT / 'RUN_RESULT.json'), runner.PRIOR_RESULT_SHA)
        self.assertEqual(ordered, targets['modules'])
        changed = [n for n in graph9['modules'] if graph9['modules'][n] != graph10['modules'][n]]
        self.assertEqual(changed, list(runner.EXPECTED_REPAIRS))
        self.assertEqual(old.affected_modules(graph9, changed), selection['affected_closure'])
        self.assertEqual(set(selection['affected_closure']), set(actual['compile_summary']['failed_or_blocked']))
        self.assertEqual(set(ordered) & set(selection['affected_closure']), set(selection['affected_owned_targets']))
        self.assertEqual((len(graph10['modules']), len(ordered), len(selection['affected_closure']),
                          len(selection['affected_owned_targets'])), (377, 69, 23, 21))
        for filename, key in [('COMPILE.log', 'compile_log_sha256'), ('AUDIT.log', 'audit_log_sha256')]:
            self.assertEqual(runner.sha(RESULT / filename), actual[key])
        args = (graph9['roots'], ordered, prior_selection)
        runner.validate_previous_result(actual, *args)
        self.assertEqual(runner.validate_repair_failures(selection, actual['compile_summary'],
                         (RESULT / 'COMPILE.log').read_text()), changed)
        for key in selection['prior_postflight_checks']:
            self.assertIs(selection['prior_postflight_checks'][key], True)
            with self.subTest(postflight=key), self.assertRaises(RuntimeError):
                runner.validate_previous_result(dict(actual, **{key: False}), *args)
        for summary, key in [('compile_summary', 'successful_closure'), ('compile_summary', 'reused'),
                             ('audit_summary', 'accepted')]:
            bad = copy.deepcopy(actual)
            bad[summary][key] -= 1
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                runner.validate_previous_result(bad, *args)
        with self.assertRaises(RuntimeError):
            runner.validate_repair_failures(selection, actual['compile_summary'], '')

    def test_two_proof_bodies_and_identical_headers(self):
        selection = read_json(PACK / 'SOURCE_SELECTION.json')
        row, = selection['changed_modules']
        # This archived preimage is also pinned by the reconstructed round-9 source graph.
        before = (ROOT / 'docs/source-only/20261126-p2-5-round8-existing-reuse/before' / row['source']).read_text()
        after = (PACK / 'after' / row['source']).read_text()
        self.assertEqual(old.digest(before.encode()), row['before_sha256'])
        self.assertEqual(old.digest(after.encode()), row['after_sha256'])
        self.assertEqual(imports(before), imports(after))
        self.assertEqual(old.option_commands(source_tokens(before)), old.option_commands(source_tokens(after)))
        self.assertFalse(re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b', source_tokens(after)))
        # Tokens through the first := of every declaration in this particular owner.
        names = r'^(?:theorem|def)\s+\w+.*?:='
        self.assertEqual(re.findall(names, before, re.M | re.S), re.findall(names, after, re.M | re.S))
        self.assertEqual(len(re.findall(names, before, re.M | re.S)), 9)
        patch_text = (PACK / 'SOURCE_DELTA.patch').read_bytes()
        self.assertEqual(len(re.findall(rb'^@@ ', patch_text, re.M)), 2)
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / row['source']
            path.parent.mkdir()
            path.write_text(before)
            subprocess.run(['git', 'apply', '--whitespace=error', '-'], cwd=temp, input=patch_text, check=True)
            self.assertEqual(path.read_text(), after)

    def test_reuse_guard_rejects_tampered_object_artifact_and_old_success(self):
        with tempfile.TemporaryDirectory() as temp, ExitStack() as stack:
            root = Path(temp)
            # Use core-only fixture bytes and a version-printing binary, without running Lean.
            program = Path(shutil.which('true')).resolve()
            self.assertTrue(program.is_file())
            original = SimpleNamespace(LEAN=program, MATHLIB_COMMIT='fixture-pin')
            external = SimpleNamespace(modules={})
            good, repair, dependent = ['ImbalancedChen.' + s for s in ('Good', 'Repair', 'Dependent')]
            stack.enter_context(patch.multiple(runner, ROOT=root, EXPECTED_REPAIRS=(repair,),
                                              PRIOR_NORMAL_SUCCESSFUL=1, PRIOR_OWNED_ACCEPTED=1))
            stack.enter_context(patch.multiple(audit, LEAN=program, LEANCHECKER=program))
            source = 'ImbalancedChen/Good.lean'
            project = root / source
            project.parent.mkdir()
            project.write_text('-- offline source fixture\n')
            record_root = root / '.lake/p2-private'
            lib = record_root / 'lib'
            obj = lib / 'ImbalancedChen/Good.olean'
            obj.parent.mkdir(parents=True)
            obj.write_bytes(b'object fixture')
            nodes = {good: {'source': project, 'deps': []}}
            toolchain = {'lean_version': subprocess.check_output([program, '--version'], text=True).strip(),
                         'lean_binary_sha256': runner.sha(program), 'mathlib_commit': original.MATHLIB_COMMIT}
            snapshot = audit.snapshot(root, lib, nodes, toolchain, external)
            record = dict(module=good, source_sha256=runner.sha(project), object_sha256=runner.sha(obj),
                          toolchain=toolchain, deps={}, dependency_signatures={}, cache_schema=normal.CACHE_SCHEMA,
                          exit_code=0)
            record['closure_signature'] = normal.closure_signature(record)
            (record_root / 'records.json').write_text(json.dumps({good: record}))
            directory = record_root / 'audit' / good
            directory.mkdir(parents=True)
            artifact = directory / 'evidence.txt'
            artifact.write_bytes(b'audited bytes')
            receipt = {'accepted': True, 'input_snapshot': snapshot,
                       'artifacts': {str(artifact.relative_to(root)): runner.sha(artifact)}}
            (directory / 'latest.json').write_text(json.dumps(receipt))
            graph = {'modules': {good: {'source': source, 'imports': []},
                                 repair: {'imports': []}, dependent: {'imports': [repair]}}}
            previous = {'compile_summary': {'failed_or_blocked': [repair, dependent]},
                        'audit_summary': {'modules': {good: {'accepted': True}, dependent: {'accepted': False}}}}
            selection = {'affected_closure': [repair, dependent], 'affected_owned_targets': [dependent],
                         'qualified_normal_reuse_candidates': 1, 'qualified_owned_reuse_candidates': 1}
            args = (graph, previous, selection, external, original)
            runner.validate_reuse(*args)
            obj.write_bytes(b'changed object')
            with self.assertRaisesRegex(ValueError, 'Source/object differs'):
                runner.validate_reuse(*args)
            obj.write_bytes(b'object fixture')
            artifact.write_bytes(b'changed evidence')
            with self.assertRaisesRegex(RuntimeError, 'cannot be reused'):
                runner.validate_reuse(*args)
            previous['audit_summary']['modules'][dependent]['accepted'] = True
            with self.assertRaisesRegex(RuntimeError, 'previously qualified'):
                runner.validate_reuse(*args)

    def test_normal_postflight_uses_attempt_deltas_and_allows_blocked_nodes(self):
        good, repair, blocked = ('ImbalancedChen.' + n for n in ('Good', 'Repair', 'Dependent'))
        modules, affected = [good, repair, blocked], [repair, blocked]
        prior = {good: {'attempts': [{'log': 'previous.log'}]}}
        current = {**prior, repair: {'attempts': [{'log': 'fresh.log'}]}}
        summary = dict(failed_or_blocked=[repair, blocked], pending=[], reused=1, successful_closure=1)
        log = f'START {repair}\nFAIL {repair} 1\n'
        args = (modules, affected, prior, current, summary)
        ok, evidence = runner.normal_reuse_postflight(*args, log)
        self.assertTrue(ok)
        self.assertEqual(evidence['fresh_attempt_modules'], [repair])
        for broken in (log.replace('START', 'MISSING'), log.replace('FAIL', 'MISSING'),
                       log + f'START {good}\n', log + f'START {repair}\n'):
            with self.subTest(log=broken):
                self.assertFalse(runner.normal_reuse_postflight(*args, broken)[0])
        self.assertFalse(runner.normal_reuse_postflight(modules, affected, prior, prior, summary, log)[0])
        rerun = copy.deepcopy(current)
        rerun[good]['attempts'].append({'log': 'unwanted.log'})
        self.assertFalse(runner.normal_reuse_postflight(modules, affected, prior, rerun, summary,
                         log + f'START {good}\nPASS {good} 0.8\n')[0])

    def test_owned_postflight_binds_reuse_flags_logs_counts_and_actual_stages(self):
        good, repair = 'ImbalancedChen.Good', 'ImbalancedChen.Repair'
        prior = {good: {'accepted': True, 'declarations': 9}, repair: {'accepted': False}}
        rows = {good: {'accepted': True, 'reused': True, 'declarations': 9},
                repair: {'accepted': True, 'reused': False, 'declarations': 3}}
        log = f'REUSE_AUDIT {good} 9\nREPLAY {repair}\nAUDIT {repair}\nPASS_AUDIT {repair} 3\n'
        self.assertTrue(runner.owned_reuse_postflight(prior, {'modules': rows}, log)[0])
        for broken in (log.replace('REUSE_AUDIT', 'MISSING'), log.replace(' 9', ' 8'),
                       log + f'REPLAY {good}\n', log + f'AUDIT {good}\n', log + f'REUSE_AUDIT {good} 9\n'):
            with self.subTest(log=broken):
                self.assertFalse(runner.owned_reuse_postflight(prior, {'modules': rows}, broken)[0])
        rows[good]['reused'] = False
        self.assertFalse(runner.owned_reuse_postflight(prior, {'modules': rows}, log)[0])
        _, _, _, real8 = old.context()
        real9 = read_json(RESULT / 'RUN_RESULT.json')
        self.assertTrue(runner.owned_reuse_postflight(real8['audit_summary']['modules'],
                        real9['audit_summary'], (RESULT / 'AUDIT.log').read_text())[0])


if __name__ == '__main__':
    unittest.main()
