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
        expected = ['-t0', '-j2', '-M4096', '-q', '-T', '100', 'Example.lean']
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
                (root / name).write_text('{}')
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
                yield state

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
                record = json.loads(Path(state['log']).read_text().splitlines()[0])
                self.assertEqual(record['command'][1:4], ['-t0', '-j2', '-M' + str(expected)])

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

    def test_audit_rejects_modified_command_budget(self):
        with self.runtime('6144') as state:
            subprocess.run(['lean', 'Example.lean'], check=True)
            log = Path(state['log'])
            record = json.loads(log.read_text())
            record['command'][3] = '-M8192'
            log.write_text(json.dumps(record) + '\n')
            with self.assertRaisesRegex(RuntimeError, 'normalized input'):
                guard.audit(Path(state['environment']['P0_CI_GUARD_STATE']))


if __name__ == '__main__':
    unittest.main()
