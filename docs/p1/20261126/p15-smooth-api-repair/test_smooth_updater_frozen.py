#!/usr/bin/env python3
"""Narrow independent tests of the actual V-bound Smooth updater; no cloud IO."""
from pathlib import Path
from types import ModuleType, SimpleNamespace
from unittest.mock import patch
import ast, copy, hashlib, importlib.util, json, re, sys, unittest

sys.dont_write_bytecode = True
DIR = Path('/tmp/p15-smooth-repair')
BASE = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
script = DIR / 'apply_smooth_repair.py'
raw = script.read_bytes()
assert len(raw) == 30616
assert hashlib.sha256(raw).hexdigest() == '7ae5a21517dcbf4350a94e21cb06894a210a908723843c287aaf5663d04a5309'
m = ModuleType('actual_frozen_smooth_updater')
m.__file__ = str(script)
exec(compile(raw, str(script), 'exec'), m.__dict__)

# Reuse only this updater's eleven focused fixtures, pointed at actual code.
spec = importlib.util.spec_from_file_location('smooth_local_fixtures', DIR / 'test_smooth_updater_delta.py')
fixture = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fixture)
fixture.m, fixture.body = m, raw.decode()
tree = ast.parse(raw)
repair = json.loads((DIR / 'REPAIR_CANDIDATE.json').read_bytes())
probe = json.loads((DIR / 'ACTUAL_SMOOTH_PROBE_RESULT.json').read_bytes())
docs = {m.REPAIR: repair, m.PROBE: probe, m.READ: fixture.read}


def gate(message, **context):
    nodes = [node for node in ast.walk(tree)
             if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
             and isinstance(node.value.func, ast.Name) and node.value.func.id == 'need'
             and len(node.value.args) == 2
             and isinstance(node.value.args[1], ast.Constant)
             and node.value.args[1].value == message]
    assert len(nodes) == 1, (message, len(nodes))
    scope = {**m.__dict__, **context}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(script), 'exec'), scope)


class Frozen(fixture.Delta):
    def test_unbound_publication_holds_without_subprocess(self):
        with patch.object(m, 'V', 'UNBOUND_TEST_ONLY'), \
             patch.object(m.subprocess, 'check_output', side_effect=AssertionError('unexpected command')) as proc:
            with self.assertRaises(RuntimeError):
                m.load('0' * 40)
            proc.assert_not_called()

    def test_actual_seven_publication_pins_and_frozen_code(self):
        config = json.loads((DIR / 'UPDATER_CONFIG.json').read_bytes())
        self.assertEqual(m.FROZEN, config)
        self.assertEqual(m.V, 'f23c4f3308b471350064bf0d6ad1bdb0fce0d6fb')
        local = {
            m.REPAIR: DIR / 'REPAIR_CANDIDATE.json',
            m.PROBE: DIR / 'ACTUAL_SMOOTH_PROBE_RESULT.json',
            m.DIAGNOSTICS: Path('/tmp/p15-u-actual/ACTUAL_U_METADATA.json'),
            m.READ: Path('/tmp/p15-u-actual/ACTUAL_U_ACCEPTANCE_READ.json'),
            m.COLLECTOR: BASE / 'collect_u_acceptance.py',
            m.PUBLIC_WORD: Path('/tmp/p15-u-actual/WORD_U_PUBLIC_ACCEPTANCE.json'),
            m.PUBLIC_ALLGROUP: Path('/tmp/p15-u-actual/ALLGROUP_U_PUBLIC_ACCEPTANCE.json'),
        }
        self.assertEqual(set(m.PINS), set(local))
        for path, file in local.items():
            self.assertEqual(m.raw_fp(file.read_bytes()), m.PINS[path], path)
        self.assertEqual(m.value_fp(fixture.reader.PINNED), fixture.read['frozen_actual_input_binding'])
        actual = {n.name: ast.get_source_segment(raw.decode(), n)
                  for n in tree.body if isinstance(n, ast.FunctionDef)}
        for name in fixture.names:
            expected = fixture.fns[name].replace('S/T/U/script-bound', 'U/V/W/script-bound')
            expected = re.sub(r'\bS\b', 'U', expected).replace('WordDictionary', 'SmoothLicence')
            self.assertEqual(actual[name], expected, name)

    def test_repair_probe_identity_gate_real_positive_and_rejections(self):
        message = 'published proof-only repair differs'
        gate(message, repair=repair, docs=docs)
        mutations = [
            lambda x: x.update(schema='p15_smooth_licence_four_proof_splices_candidate_v1'),
            lambda x: x.update(declaration_count=10),
            lambda x: x.update(compiler_probe_performed=False),
            lambda x: x['actual_whole_module_probe'].update(compiler_job='wrong-job'),
            lambda x: x['actual_whole_module_probe'].update(path='/wrong/ACTUAL_SMOOTH_PROBE_RESULT.json'),
            lambda x: x['actual_whole_module_probe'].update(sha256='0' * 64),
            lambda x: x['actual_whole_module_probe'].update(exit_code=1),
        ]
        for change in mutations:
            bad = copy.deepcopy(repair)
            change(bad)
            with self.assertRaises(RuntimeError):
                gate(message, repair=bad, docs={**docs, m.REPAIR: bad})

    def test_actual_probe_guard_scope_and_preservation_gate(self):
        message = 'whole-module no-output probe differs'
        gate(message, probe=probe)
        changes = {
            'exit_code': 1,
            'output_object_requested': True,
            'original_serializer_and_guard_used': False,
            'lake_no_build_env_lean': False,
            'accepted_prefix_live_source_count': 157,
            'accepted_prefix_dependency_count': 149,
            'watched_source_slots': 359,
            'watched_modules': 159,
            'watched_artifact_slots': 3359,
            'U_original_Word_AllGroup_acceptances_preserved': [m.WORD],
            'original_source_and_failed_setup_preserved': False,
            'all_original_U_S_Q_evidence_runtime_and_Git_preserved': False,
            'existing_project_modules_rebuilt': [m.TARGET],
            'normal_or_kernel_acceptance_claimed': True,
        }
        for key, value in changes.items():
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                gate(message, probe={**probe, key: value})

    def test_git_guard_binds_initial_read_not_only_final_state(self):
        # Original raw Git state is remote. Exercise actual comparison with a
        # synthetic value; actual public fingerprint bytes are checked above.
        git = {'isolated_git_fixture': 'unchanged'}
        c = SimpleNamespace(docs={m.READ: {'current_dirty_Git_state': m.value_fp(git)}})
        message = 'original U dirty Git identity differs'
        gate(message, git=git, c=c)
        with self.assertRaises(RuntimeError):
            gate(message, git={**git, 'unrelated': 'changed'}, c=c)


if __name__ == '__main__':
    unittest.main(verbosity=2)
