"""Local orchestration fixtures only: no cloud, Lean, or kernel evidence."""
from pathlib import Path
import contextlib
import hashlib
import importlib.util
import io
import json
import subprocess
import sys
import tempfile
import types
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
DRIVER = HERE / 'resume_batch10.py'


def digest(data):
    return hashlib.sha256(data).hexdigest()


class ContinuationTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue(DRIVER.is_file(), 'Batch10 continuation driver is not implemented')
        spec = importlib.util.spec_from_file_location('batch10_fixture_driver', DRIVER)
        self.driver = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.driver)
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.project = Path(self.tmp.name) / 'project'
        self.project.mkdir()
        self.receipts = Path(self.tmp.name) / 'receipts'
        helper_bytes = (REPO / 'docs/p1/20261124/batch5-parallel/run_batch5_parallel.py').read_bytes()
        self.helper = self.driver.load_helper(helper_bytes)

    def source(self, module, data):
        path = self.project / (module.replace('.', '/') + '.lean')
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def rows(self):
        old, after, core = b'-- old ordinary\n', b'-- repaired ordinary\n', b'-- new provider\n'
        self.source('ImbalancedChen.Ordinary', old)
        rows = [
            {'module': 'ImbalancedChen.Ordinary', 'path': 'ImbalancedChen/Ordinary.lean',
             'before_sha256': digest(old), 'after_sha256': digest(after)},
            {'module': 'ImbalancedChen.Core', 'path': 'ImbalancedChen/Core.lean',
             'before_sha256': None, 'after_sha256': digest(core)},
        ]
        return rows, {rows[0]['path']: after, rows[1]['path']: core}

    def project_bytes(self):
        return {str(p.relative_to(self.project)): p.read_bytes()
                for p in self.project.rglob('*') if p.is_file()}

    def test_unknown_new_provider_prevents_every_source_write(self):
        rows, payloads = self.rows()
        self.source('ImbalancedChen.Core', b'-- somebody else\n')
        before = self.project_bytes()
        with self.assertRaisesRegex(RuntimeError, 'preimage'):
            self.driver.install_sources(self.project, rows, payloads, self.receipts, self.helper)
        self.assertEqual(before, self.project_bytes())
        self.assertFalse(self.receipts.exists())

    def test_dangling_new_provider_symlink_prevents_ordinary_write_and_backup(self):
        rows, payloads = self.rows()
        (self.project / rows[1]['path']).symlink_to(self.project / 'does-not-exist.lean')
        ordinary = self.project / rows[0]['path']
        before = ordinary.read_bytes()
        try:
            self.driver.install_sources(self.project, rows, payloads, self.receipts, self.helper)
        except (RuntimeError, FileExistsError):
            pass
        else:
            self.fail('occupied provider symlink was accepted')
        self.assertEqual(ordinary.read_bytes(), before)
        self.assertFalse(self.receipts.exists())
        self.assertTrue((self.project / rows[1]['path']).is_symlink())

    def test_corrupt_payload_prevents_every_source_write(self):
        rows, payloads = self.rows()
        payloads[rows[1]['path']] = b'-- corrupt payload\n'
        before = self.project_bytes()
        with self.assertRaisesRegex(RuntimeError, 'payload'):
            self.driver.install_sources(self.project, rows, payloads, self.receipts, self.helper)
        self.assertEqual(before, self.project_bytes())
        self.assertFalse(self.receipts.exists())

    def test_install_creates_absent_provider_and_backs_up_existing_source(self):
        rows, payloads = self.rows()
        self.driver.install_sources(self.project, rows, payloads, self.receipts, self.helper)
        self.assertEqual((self.project / rows[0]['path']).read_bytes(), b'-- repaired ordinary\n')
        self.assertEqual((self.project / rows[1]['path']).read_bytes(), b'-- new provider\n')
        self.assertEqual((self.receipts / rows[0]['path']).read_bytes(), b'-- old ordinary\n')

    def test_already_after_install_is_exact_noop(self):
        rows, payloads = self.rows()
        for row in rows:
            self.source(row['module'], payloads[row['path']])
        before = {r['path']: (self.project / r['path']).stat() for r in rows}
        self.driver.install_sources(self.project, rows, payloads, self.receipts, self.helper)
        for row in rows:
            stat = (self.project / row['path']).stat()
            self.assertEqual((stat.st_ino, stat.st_mtime_ns),
                             (before[row['path']].st_ino, before[row['path']].st_mtime_ns))
        self.assertFalse(self.receipts.exists())

    def test_check_preflight_does_not_create_provider_or_receipt(self):
        rows, payloads = self.rows()
        before = self.project_bytes()
        result = self.driver.preflight_sources(self.project, rows, payloads)
        self.assertEqual([r['action'] for r in result], ['REPLACE_PREIMAGE', 'CREATE_ABSENT'])
        self.assertEqual(before, self.project_bytes())
        self.assertFalse(self.receipts.exists())

    def test_compile_order_keeps_higher_units_separate_and_sorts_ordinary_ancestors(self):
        graph = {'H.Core': [], 'H.GuardA': ['H.Core'], 'H.GuardB': ['H.Core'],
                 'H.Facade': ['H.GuardA', 'H.GuardB'], 'O.Parent': ['O.Leaf'], 'O.Leaf': []}
        order = self.driver.compile_order(['H.Core', 'H.GuardA', 'H.GuardB', 'H.Facade'],
                                          ['O.Parent', 'O.Leaf'], graph)
        self.assertEqual(order, ['H.Core', 'H.GuardA', 'H.GuardB', 'H.Facade', 'O.Leaf', 'O.Parent'])

    def fake_compiler(self, *, fail_module=None, unready=()):
        """Subprocess boundary double; all outputs are explicitly local fixtures."""
        builds = []

        def run(argv, cwd, stdout, stderr, **kwargs):
            self.assertEqual(Path(cwd), self.project)
            lake = argv[argv.index('lake'):]
            targets = [a[1:-6] for a in lake if a.startswith('+') and a.endswith(':olean')]
            self.assertTrue(targets)
            if '--no-build' in lake:
                ready = all(m not in unready and
                            (self.project / ('.lake/build/lib/lean/' + m.replace('.', '/') + '.olean')).exists()
                            for m in targets)
                return types.SimpleNamespace(returncode=0 if ready else 3)
            self.assertEqual(lake[0:2], ['lake', 'build'])
            self.assertEqual(len(targets), 1, 'A normal command must never cold-build multiple Higher owners')
            module = targets[0]
            builds.append(module)
            if module == fail_module:
                stdout.write(b'error: fixture-only simulated interruption\n')
                return types.SimpleNamespace(returncode=1)
            self.outputs(module)
            stdout.write(('\u2714 [1/1] Built ' + module + '\n').encode())
            return types.SimpleNamespace(returncode=0)
        return run, builds

    def outputs(self, module):
        rel = module.replace('.', '/')
        for directory, extension in [('.lake/build/lib/lean/', '.olean'),
                                     ('.lake/build/lib/lean/', '.ilean'),
                                     ('.lake/build/ir/', '.c'),
                                     ('.lake/build/ir/', '.setup.json'),
                                     ('.lake/build/lib/lean/', '.trace')]:
            path = self.project / (directory + rel + extension)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(('fixture only ' + module + extension).encode())

    def normal(self, module, imports=(), context=None):
        return self.driver.normal_one(self.project, module, list(imports), self.receipts,
                                      self.helper, lambda: context or {'fixture_only': True})

    def test_interrupted_resume_reuses_complete_module_without_normal_replay(self):
        self.source('ImbalancedChen.Core', b'-- fixture core\n')
        self.source('ImbalancedChen.Guard', b'-- fixture guard\n')
        fake, first = self.fake_compiler(fail_module='ImbalancedChen.Guard')
        with patch.object(self.driver.subprocess, 'run', fake):
            self.normal('ImbalancedChen.Core')
            with self.assertRaisesRegex(RuntimeError, 'normal'):
                self.normal('ImbalancedChen.Guard', ['ImbalancedChen.Core'])
        self.assertEqual(first, ['ImbalancedChen.Core', 'ImbalancedChen.Guard'])
        fake, second = self.fake_compiler()
        with patch.object(self.driver.subprocess, 'run', fake):
            reused = self.normal('ImbalancedChen.Core')
            self.normal('ImbalancedChen.Guard', ['ImbalancedChen.Core'])
        self.assertTrue(reused['reused'])
        self.assertEqual(second, ['ImbalancedChen.Guard'])

    def test_ready_object_without_normal_provenance_is_not_rebuilt_or_credited(self):
        self.source('ImbalancedChen.Core', b'-- fixture core\n')
        self.outputs('ImbalancedChen.Core')
        fake, builds = self.fake_compiler()
        with patch.object(self.driver.subprocess, 'run', fake):
            with self.assertRaisesRegex(RuntimeError, 'READY_WITHOUT_NORMAL_PROVENANCE'):
                self.normal('ImbalancedChen.Core')
        self.assertEqual(builds, [])
        self.assertFalse(list(self.receipts.rglob('NORMAL_PASS.json')))

    def test_changed_dependency_binding_invalidates_receipt_without_rebuild(self):
        self.source('ImbalancedChen.Core', b'-- fixture core\n')
        fake, builds = self.fake_compiler()
        with patch.object(self.driver.subprocess, 'run', fake):
            self.normal('ImbalancedChen.Core', context={'dependency': 'original'})
            with self.assertRaisesRegex(RuntimeError, 'receipt'):
                self.normal('ImbalancedChen.Core', context={'dependency': 'changed'})
        self.assertEqual(builds, ['ImbalancedChen.Core'])

    def test_missing_guard_blocks_facade_without_building_it(self):
        self.source('ImbalancedChen.Facade', b'-- fixture facade\n')
        fake, builds = self.fake_compiler(unready=['ImbalancedChen.Guard'])
        with patch.object(self.driver.subprocess, 'run', fake):
            with self.assertRaisesRegex(RuntimeError, 'DEPENDENCIES_NOT_READY'):
                self.normal('ImbalancedChen.Facade', ['ImbalancedChen.Guard'])
        self.assertEqual(builds, [])

    def test_changed_command_copy_invalidates_receipt_without_normal_replay(self):
        self.source('ImbalancedChen.Core', b'-- fixture core\n')
        fake, builds = self.fake_compiler()
        with patch.object(self.driver.subprocess, 'run', fake):
            self.normal('ImbalancedChen.Core')
            path = self.receipts / 'normal/ImbalancedChen.Core/NORMAL_PASS.json'
            receipt = json.loads(path.read_bytes())
            receipt['normal_command']['log'] = '/tmp/unrelated-normal.log'
            path.write_text(json.dumps(receipt))
            with self.assertRaisesRegex(RuntimeError, 'receipt'):
                self.normal('ImbalancedChen.Core')
        self.assertEqual(builds, ['ImbalancedChen.Core'])

    def test_partial_pending_audit_does_not_claim_missing_higher_owner(self):
        self.source('ImbalancedChen.Core', b'-- fixture core\n')
        fake, _ = self.fake_compiler()
        with patch.object(self.driver.subprocess, 'run', fake):
            result = self.normal('ImbalancedChen.Core')
        spec = {'helper': self.helper,
                'higher_order': ['ImbalancedChen.Core', 'ImbalancedChen.Guard'],
                'raw_inputs': {self.driver.RUNNER_PATH: (REPO / self.driver.RUNNER_PATH).read_bytes()}}
        audit = self.driver.pending_audit(self.project, self.receipts, spec,
            {'ImbalancedChen.Core': [], 'ImbalancedChen.Guard': ['ImbalancedChen.Core']},
            {'ImbalancedChen.Core': digest(b'-- fixture core\n')}, {'ImbalancedChen.Core': result})
        plan = json.loads(Path(audit['plan']).read_bytes())
        commands = json.loads(Path(audit['commands']).read_bytes())
        self.assertEqual(set(plan['modules']), {'ImbalancedChen.Core'})
        self.assertFalse(plan['higher_partition_normal_complete'])
        self.assertEqual(plan['higher_missing_normal_modules'], ['ImbalancedChen.Guard'])
        self.assertFalse(plan['whole_P1_complete'])
        self.assertEqual(commands['run_only_populated_lane'][-2:], ['--lane', '0'])
        self.assertEqual(commands['status'], 'PENDING_NOT_EXECUTED')
        self.assertEqual(digest((Path(audit['plan']).parent / 'run_parallel_acceptance_multibatch.py').read_bytes()),
                         'e9dadb4ee5cd0a9ad50e298a77c6133fe5e0d012f8b194ae02bd5118460fc9e1')

    def test_changed_existing_guard_is_rejected_before_execution(self):
        paths = [Path(self.tmp.name) / name for name in ['guard.py', 'serializer.py', 'state0.json', 'state1.json', 'audit.lean']]
        for path in paths:
            path.write_bytes(b'fixture-only changed runtime\n')
        helper = types.SimpleNamespace(GUARD=str(paths[0]), SERIALIZER=str(paths[1]), STATES=paths[2:4])
        with patch.object(self.driver, 'AUDIT_TEMPLATE', paths[4]), \
             patch.object(self.driver, 'AUDIT_TEMPLATE_SHA', digest(paths[4].read_bytes())):
            with self.assertRaisesRegex(RuntimeError, 'guard'):
                self.driver.runtime_binding(helper)

    def test_serialized_worker_relay_preserves_full_log_and_exposes_only_stage_lines(self):
        directory = Path(self.tmp.name) / 'relay'
        directory.mkdir()
        output = io.StringIO()
        script = 'print(\'unabridged fixture diagnostic\'); print(\'{"stage":"NORMAL_START","module":"Fixture"}\')'
        with contextlib.redirect_stdout(output):
            try:
                result = self.driver.record_command(self.project, directory, 'worker',
                    [sys.executable, '-B', '-c', script], relay=True)
            except TypeError as error:
                self.fail('serialized worker live relay is not implemented: ' + str(error))
        self.assertEqual(result['exit_code'], 0)
        self.assertEqual(Path(result['log']).read_text(),
                         'unabridged fixture diagnostic\n{"stage":"NORMAL_START","module":"Fixture"}\n')
        self.assertEqual(output.getvalue(), '{"stage":"NORMAL_START","module":"Fixture"}\n')

    def test_source_snapshot_has_exact_75_targets_and_expected_higher_order(self):
        spec = self.driver.load_inputs(REPO)
        self.assertEqual(len(spec['updates']), 75)
        self.assertEqual(sum(row['before_sha256'] is None for row in spec['updates']), 52)
        self.assertEqual(spec['higher_order'][0], 'ImbalancedChen.P2OriginalSixthHigherMomentsCore')
        self.assertEqual(spec['higher_order'][-1], 'ImbalancedChen.P2OriginalSixthHigherMoments')
        self.assertEqual(len(spec['higher_order']), 53)


if __name__ == '__main__':
    unittest.main(verbosity=2)
