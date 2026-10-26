#!/usr/bin/env python3
"""Deterministic guard tests with fake toolchain executables, never proof evidence."""
import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import ci_runtime_guard as guard


class MemoryBudgetTests(unittest.TestCase):
    def test_default_and_explicit_normalization(self):
        args = ['-qj8', '-M', '9999', '--trust=9', '--threads', '12',
                '--memory=10', '-T100', 'Example.lean']
        expected = ['-t0', '-j2', '-M4096', '-DElab.async=false', '-q', '-T', '100', 'Example.lean']
        self.assertEqual(guard.normalize_lean_args(args), expected)
        for budget in (1, 4096, 6144, 8192, 16384):
            with self.subTest(budget=budget):
                self.assertEqual(guard.parse_memory_budget(str(budget)), budget)
                self.assertEqual(guard.normalize_lean_args(args, budget),
                                 [*expected[:2], '-M' + str(budget), *expected[3:]])

    def test_invalid_budgets_fail_closed(self):
        for value in ('', '0', '-1', '+6144', '06144', '6144 ', ' 6144',
                      '6144\n', '6.5', '16385', '999999999999999999', None):
            with self.subTest(value=value), self.assertRaises(RuntimeError):
                guard.parse_memory_budget(value)
        for value in (0, -1, 16385, True, '6144', 6144.0):
            with self.subTest(value=value), self.assertRaises(RuntimeError):
                guard.normalize_lean_args([], value)

    def test_fixed_scheduling_option_normalization(self):
        for args in (['-DElab.async=false'], ['-D', 'Elab.async=false'],
                     ['-qDElab.async=false'], ['-DElab.async=false', '-DElab.async=false']):
            with self.subTest(args=args):
                actual = guard.normalize_lean_args([*args, 'Example.lean'], 6144)
                self.assertEqual(actual.count('-DElab.async=false'), 1)
                self.assertNotIn('Elab.async=false', actual)
                self.assertEqual(actual[:4], ['-t0', '-j2', '-M6144', '-DElab.async=false'])
        self.assertEqual(guard.normalize_lean_args(['-DmaxRecDepth=2048', 'Example.lean'])[-3:],
                         ['-D', 'maxRecDepth=2048', 'Example.lean'])

    def test_conflicting_or_invalid_scheduling_options_rejected(self):
        for value in ('Elab.async=true', 'Elab.async=0', 'Elab.async=',
                      'Elab.async=False', 'Elab.async=false ', 'Elab.async',
                      '.Elab.async=false', 'Elab..async=false', ' Elab.async=false'):
            for prefix in (['-D', value], ['-D' + value], ['-qD' + value]):
                with self.subTest(args=prefix), self.assertRaises(RuntimeError):
                    guard.normalize_lean_args(prefix, 6144)

    def test_execution_and_abbreviation_still_rejected(self):
        for args in (['--run', 'x.lean'], ['-r', 'x.lean'], ['-qr', 'x.lean'],
                     ['--mem=1'], ['--thr=8'], ['--tru=9']):
            with self.subTest(args=args), self.assertRaises(RuntimeError):
                guard.normalize_lean_args(args, 6144)


class FakeRuntimeTests(unittest.TestCase):
    @contextlib.contextmanager
    def runtime(self, budget=None):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            root, tmp, real = base / 'project', base / 'temp', base / 'pin'
            for path in (root, tmp, real / 'bin', real / 'lib' / 'lean'):
                path.mkdir(parents=True)
            (root / 'lean-toolchain').write_text(guard.PIN)
            for name in ('lakefile.toml', 'lake-manifest.json'):
                (root / name).write_text('{"packages": []}' if name == 'lake-manifest.json' else 'name = "test"\nleanOptions = {Elab.async = false}')
            (root / 'Example.lean').write_text('theorem test : True := True.intro')
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            subprocess.run(['git', '-C', str(root), 'add', '.'], check=True)
            lean = ('#!/usr/bin/env python3\nimport pathlib, sys\n'
                    'if "--print-prefix" in sys.argv:\n'
                    '    print(pathlib.Path(sys.argv[0]).parent.parent)\n')
            lake = ('#!/usr/bin/env python3\nimport os, sys\n'
                    'assert sys.argv[1] == "env"\n'
                    'os.execvp(sys.argv[2], sys.argv[2:])\n')
            for name in (*guard.TOOLS, 'lake', 'leanchecker', 'leantar'):
                path = real / 'bin' / name
                path.write_text(lake if name == 'lake' else lean)
                path.chmod(0o755)
            env = {'PATH': os.environ['PATH'], 'LEAN_NUM_THREADS': '2'}
            if budget is not None:
                env['CI_LEAN_MEMORY_MIB'] = budget
            with patch.dict(os.environ, env, clear=True), contextlib.redirect_stdout(io.StringIO()):
                state = guard.prepare(root, tmp, tmp / 'evidence', real / 'bin',
                                      base / 'unused-action', verify_action=False)
                os.environ.update(state['environment'])
                os.environ['PATH'] = state['shadow'] + '/bin:' + env['PATH']
                previous = Path.cwd()
                os.chdir(root)
                try:
                    yield state
                finally:
                    os.chdir(previous)

    def test_setup_wrapper_probe_and_audit(self):
        for selected in (None, '6144', '8192'):
            with self.subTest(budget=selected), self.runtime(selected) as state:
                expected = int(selected or '4096')
                self.assertEqual(state['lean_memory_mib'], expected)
                self.assertEqual(state['environment']['CI_LEAN_MEMORY_MIB'], str(expected))
                self.assertIn('-M' + str(expected), state['policy'])
                subprocess.run(['lean', '-M1', '-t9', '-j99', 'Example.lean'], check=True)
                report = guard.audit(Path(state['environment']['P0_CI_GUARD_STATE']),
                                     probe=True, require_source=True)
                self.assertEqual(report['lean_memory_mib'], expected)
                self.assertEqual(report['source_commands'], 1)
                self.assertIs(state['lean_elab_async'], False)
                self.assertIs(report['lean_elab_async'], False)
                self.assertEqual(state['environment']['P0_LEAN_ELAB_ASYNC'], 'scoped-v1')
                record = json.loads(Path(state['log']).read_text().splitlines()[0])
                self.assertEqual(record['command'][1:5], ['-t0', '-j2', '-M' + str(expected), '-DElab.async=false'])

    def test_environment_and_state_cannot_change_budget(self):
        with self.runtime('6144') as state:
            os.environ['CI_LEAN_MEMORY_MIB'] = '8192'
            with self.assertRaises(RuntimeError):
                guard.check_environment(state)
            result = subprocess.run(['lean', 'Example.lean'], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'changed environment: CI_LEAN_MEMORY_MIB', result.stderr)
            os.environ['CI_LEAN_MEMORY_MIB'] = '6144'
            state['lean_memory_mib'] = 8192
            with self.assertRaises(RuntimeError):
                guard.check_environment(state)

    def test_fixed_scheduling_wrapper_and_tampering(self):
        with self.runtime('6144') as state:
            state_path = Path(state['environment']['P0_CI_GUARD_STATE'])
            for args in (['-DElab.async=true'], ['-D', 'Elab.async=true'], ['-qDElab.async=true']):
                result = subprocess.run(['lean', *args, 'Example.lean'], capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(b'CLI conflicts with source-scoped scheduling', result.stderr)
            self.assertEqual(Path(state['log']).read_text(), '')
            subprocess.run(['lean', '-DElab.async=false', 'Example.lean'], check=True)
            log = Path(state['log'])
            record = json.loads(log.read_text())
            record['command'][4] = '-DElab.async=true'
            log.write_text(json.dumps(record) + '\n')
            with self.assertRaisesRegex(RuntimeError, 'normalized input'):
                guard.audit(state_path)
            os.environ['P0_LEAN_ELAB_ASYNC'] = 'true'
            with self.assertRaisesRegex(RuntimeError, 'Changed guard environment'):
                guard.check_environment(state)
            result = subprocess.run(['lean', 'Example.lean'], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b'changed environment: P0_LEAN_ELAB_ASYNC', result.stderr)
            os.environ['P0_LEAN_ELAB_ASYNC'] = 'scoped-v1'
            state['lean_elab_async'] = True
            with self.assertRaisesRegex(RuntimeError, 'scheduling'):
                guard.check_environment(state)

    def test_audit_rejects_modified_command_budget(self):
        with self.runtime('6144') as state:
            subprocess.run(['lean', 'Example.lean'], check=True)
            log = Path(state['log'])
            record = json.loads(log.read_text())
            record['command'][3] = '-M8192'
            log.write_text(json.dumps(record) + '\n')
            with self.assertRaisesRegex(RuntimeError, 'normalized input'):
                guard.audit(Path(state['environment']['P0_CI_GUARD_STATE']))


    def test_project_setup_record_and_audit_mutation(self):
        with self.runtime('6144') as state:
            build = Path.cwd() / '.lake'; build.mkdir()
            setup = build / 'Example.setup.json'
            setup.write_text(json.dumps({'options': {'Elab.async': False}}))
            subprocess.run(['lean', 'Example.lean', '--setup', str(setup)], check=True)
            guard.audit(Path(state['environment']['P0_CI_GUARD_STATE']), require_source=True)
            setup.write_text(json.dumps({'options': {'Elab.async': True}}))
            with self.assertRaisesRegex(RuntimeError, 'setup'):
                guard.audit(Path(state['environment']['P0_CI_GUARD_STATE']))
            result = subprocess.run(['lean', 'Example.lean', '--setup', str(setup)], capture_output=True)
            self.assertNotEqual(result.returncode, 0)

    def test_setup_abbreviations_fail_in_wrapper(self):
        with self.runtime('6144') as state:
            build = Path.cwd() / '.lake'; build.mkdir()
            setup = build / 'evil.json'
            setup.write_text(json.dumps({'options': {'Elab.async': True}}))
            for key in ('--s', '--se', '--set', '--setu'):
                for args in ([key, str(setup)], [key + '=' + str(setup)],
                             ['--setup', str(setup), key + '=' + str(setup)]):
                    result = subprocess.run(['lean', 'Example.lean', *args], capture_output=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertTrue(b'abbreviated setup option' in result.stderr or b'non-file/non-build' in result.stderr)
            self.assertEqual(Path(state['log']).read_text(), '')

    def test_alternate_input_modes_fail_in_wrapper(self):
        with self.runtime('6144') as state:
            for mode in ('--stdin', '--std', '--server', '--serv', '--worker', '--wor'):
                result = subprocess.run(['lean', mode, 'Example.lean'], input=b'-- unbound source', capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(b'non-file/non-build', result.stderr)
            self.assertEqual(Path(state['log']).read_text(), '')

    def test_unknown_source_and_scope_state_tampering(self):
        with self.runtime('6144') as state:
            Path('Unknown.lean').write_text('-- no')
            result = subprocess.run(['lean', 'Unknown.lean'], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertEqual(Path(state['log']).read_text(), '')
            state['source_scope']['source_scopes'][str(Path.cwd() / 'Unknown.lean')] = 'project'
            state_path = Path(state['environment']['P0_CI_GUARD_STATE'])
            state_path.write_text(json.dumps(state))
            with self.assertRaisesRegex(RuntimeError, 'source scope'):
                guard.audit(state_path)


class SourcePolicyTests(unittest.TestCase):
    @contextlib.contextmanager
    def scope(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            src, dep, probe = root / 'Main.lean', root / 'dep/Dep.lean', root / 'Probe.lean'
            dep.parent.mkdir()
            for p in (src, dep, probe): p.write_text('-- source')
            cfg = root / 'lakefile.toml'; cfg.write_text('leanOptions = {Elab.async = false}')
            build = root / '.lake'; build.mkdir()
            scope = {'source_scopes': {str(src): 'project', str(dep): 'dependency', str(probe): 'probe'},
                     'dependency_source_sha256': {str(dep): guard.sha(dep)},
                     'scope_config_sha256': {str(cfg): guard.sha(cfg)}, 'setup_roots': [str(build)]}
            yield root, scope

    def policy(self, root, scope, args):
        return guard.source_policy(guard.normalize_lean_args(args, 6144, None), scope, str(root))

    def test_quoted_dot_is_not_a_traced_lean_option(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for config in ('leanOptions = {"Elab.async" = false}',
                           'leanOptions = {Elab.async = true}'):
                (root / 'lakefile.toml').write_text(config)
                with self.assertRaisesRegex(RuntimeError, 'must trace'):
                    guard.build_source_scope(root, [])

    def test_scopes_and_native_dependency_options(self):
        with self.scope() as (root, scope):
            for path, kind, expected in [('Main.lean', 'project', False), ('dep/Dep.lean', 'dependency', True), ('Probe.lean', 'probe', False)]:
                result = self.policy(root, scope, [path])
                self.assertEqual((result['scope'], result['effective_async']), (kind, expected))
            self.assertNotIn('-DElab.async=false', guard.normalize_lean_args(['dep/Dep.lean'], 6144, None))
            self.policy(root, scope, ['-DElab.async=true', 'dep/Dep.lean'])
            for args in (['-DElab.async=false', 'dep/Dep.lean'], ['-DElab.async=true', 'Main.lean']):
                with self.assertRaises(RuntimeError): self.policy(root, scope, args)

    def test_setup_overrides_and_integrity(self):
        with self.scope() as (root, scope):
            setup = root / '.lake/Main.setup.json'
            for value in (True, 'false', 0):
                setup.write_text(json.dumps({'options': {'Elab.async': value}}))
                with self.assertRaises(RuntimeError): self.policy(root, scope, ['Main.lean', '--setup', str(setup)])
            setup.write_text(json.dumps({'options': {'Elab.async': False}}))
            result = self.policy(root, scope, ['Main.lean', '--setup=' + str(setup)])
            self.assertEqual(result['setup']['sha256'], guard.sha(setup))
            with self.assertRaises(RuntimeError): self.policy(root, scope, ['dep/Dep.lean', '--setup', str(setup)])
            setup.write_text('{"options":{"Elab.async":false,"Elab.async":true}}')
            with self.assertRaises(RuntimeError): self.policy(root, scope, ['Main.lean', '--setup', str(setup)])
            setup.write_text('{"options":{}}')
            with self.assertRaises(RuntimeError): self.policy(root, scope, ['Main.lean', '--setup', str(setup), '--setup', str(setup)])
            outside = root / 'outside.json'; outside.write_text('{}')
            with self.assertRaises(RuntimeError): self.policy(root, scope, ['Main.lean', '--setup', str(outside)])

    def test_unknown_sources_and_option_values(self):
        with self.scope() as (root, scope):
            unknown = root / 'Unknown.lean'; unknown.write_text('-- no')
            alias = root / 'Alias.lean'; alias.symlink_to(root / 'Main.lean')
            for args in (['Unknown.lean'], ['Alias.lean'], ['Main.lean', 'Probe.lean'], ['Main.lean', '--version'], ['Main.lean', '--vers'], ['Main.lean', '-g'], ['Main.lean', '--features'], [], ['--server']):
                with self.assertRaises(RuntimeError): self.policy(root, scope, args)
            self.policy(root, scope, ['Main.lean', '-o', 'output.lean'])
            self.assertEqual(self.policy(root, scope, ['--print-prefix'])['scope'], 'metadata')

    def test_changed_dependency_and_config_rejected(self):
        with self.scope() as (root, scope):
            (root / 'dep/Dep.lean').write_text('-- modified')
            with self.assertRaises(RuntimeError): self.policy(root, scope, ['dep/Dep.lean'])
            (root / 'lakefile.toml').write_text('leanOptions = {Elab.async = true}')
            with self.assertRaises(RuntimeError): self.policy(root, scope, ['Main.lean'])


if __name__ == '__main__':
    unittest.main()
