"""Local adversarial boundary tests. No Lean, remote execution or formal credit."""
import copy
import importlib.util
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

HERE = Path(__file__).parent
spec = importlib.util.spec_from_file_location('partition_adapter', HERE / 'run_partition.py')
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


class SourceBoundary(unittest.TestCase):
    def setUp(self):
        self.old = (HERE / 'original-source.lean').read_bytes()
        self.baseline = (HERE / 'parser-fixed-baseline.lean').read_bytes()
        self.saved = m.INPUTS

    def tearDown(self):
        m.INPUTS = self.saved

    def verify(self, candidate, baseline=None):
        m.INPUTS = {'source_bytes': len(candidate), 'source_sha256': m.digest(candidate)}
        m.verify_repair(self.old, self.baseline if baseline is None else baseline, candidate)

    def test_exact_reviewed_parser_fix(self):
        self.verify(self.baseline)
        self.assertEqual(m.proof_mask(self.baseline).count('<ORIGINAL_THEOREM_PROOF_BODY>'), 11)

    def test_proof_body_only_delta(self):
        candidate = self.baseline.replace(b' := by\n  induction carrier', b' := by\n  classical\n  induction carrier', 1)
        self.assertNotEqual(candidate, self.baseline)
        self.verify(candidate)

    def test_let_states_statement_is_fully_protected(self):
        original = b'let states := p1SignedExitStates retained h pre positive mass carrier'
        candidate = self.baseline.replace(original, original + b'.reverse', 1)
        self.assertNotEqual(candidate, self.baseline)
        with self.assertRaisesRegex(ValueError, 'complete theorem statement'):
            self.verify(candidate)

    def test_equation_definition_is_protected(self):
        candidate = self.baseline.replace(b'mass * h p', b'mass + h p', 1)
        with self.assertRaisesRegex(ValueError, 'complete theorem statement'):
            self.verify(candidate)

    def test_parser_baseline_is_not_arbitrary_whitespace(self):
        candidate = self.baseline.replace(b'positive := !positive, mass', b'positive := !positive,  mass', 1)
        with self.assertRaisesRegex(ValueError, 'reviewed record-literal layout'):
            self.verify(candidate, candidate)

    def test_visibility_names_namespace_and_comments(self):
        mutations = (
            (b'private theorem p1_sum_finite_fibres', b'theorem p1_sum_finite_fibres'),
            (b'theorem p1_mem_exitStates_rejected', b'theorem p1_mem_exitStates_rejected_new'),
            (b'namespace ImbalancedChen', b'namespace ImbalancedChenChanged'),
            (b'Every rejected selection is recorded once', b'Every rejected selection is recorded twice'),
        )
        for before, after in mutations:
            with self.subTest(before=before):
                candidate = self.baseline.replace(before, after, 1)
                self.assertNotEqual(candidate, self.baseline)
                with self.assertRaises(ValueError):
                    self.verify(candidate)

    def test_proof_escape_rejected(self):
        candidate = self.baseline.replace(b' := by\n  induction carrier', b' := by\n  sorry\n  induction carrier', 1)
        with self.assertRaisesRegex(ValueError, 'forbidden proof escape'):
            self.verify(candidate)


class InputBoundary(unittest.TestCase):
    def setUp(self):
        self.saved = m.INPUTS

    def tearDown(self):
        m.INPUTS = self.saved

    def valid(self):
        failure = {**m.FIRST_FAILURE, 'source_bytes': 15982, 'result_bytes': 1,
                   'directory': '/synthetic/failure', 'publication': 'failed-v1'}
        current = {'source_sha256': m.PARSER_FIXED_SHA, 'source_bytes': 15972,
                   'result_sha256': 'a' * 64, 'driver_sha256': 'b' * 64, 'log_sha256': 'c' * 64,
                   'job_id': 'job_' + 'd' * 32, 'result_bytes': 1, 'directory': '/synthetic/current'}
        return {'source_sha256': m.PARSER_FIXED_SHA, 'source_bytes': 15972,
                'probe': current, 'failed_probes': [failure]}

    def test_unbound_exits_before_git_or_helper_reads(self):
        m.INPUTS = None
        with patch.object(m, 'git', side_effect=AssertionError('Git must not run')) as mocked:
            with self.assertRaisesRegex(ValueError, 'UNBOUND'):
                m.load('a' * 40)
            with self.assertRaisesRegex(ValueError, 'UNBOUND'):
                m.main()
            mocked.assert_not_called()

    def test_first_real_failure_required(self):
        m.INPUTS = self.valid()
        m.validate_inputs()
        m.INPUTS['failed_probes'][0]['log_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'first and immutable'):
            m.validate_inputs()
        m.INPUTS = self.valid()
        m.INPUTS['failed_probes'] = []
        with self.assertRaisesRegex(ValueError, 'incomplete real source'):
            m.validate_inputs()

    def test_source_and_publication_binding(self):
        m.INPUTS = self.valid()
        m.INPUTS['probe']['source_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'source identity differs'):
            m.validate_inputs()
        m.INPUTS = self.valid()
        m.INPUTS['failed_probes'][0]['publication'] = '../other'
        with self.assertRaisesRegex(ValueError, 'publication directories'):
            m.validate_inputs()


class ProbeCompletionBoundary(unittest.TestCase):
    def setUp(self):
        self.source = b'synthetic source for receipt tests only'
        self.sha = m.digest(self.source)
        self.run = Path('/workspace/p1-complete-proof/20261127-p15-signed-exit-partition-probe-v99') / self.sha / 'attempt-00000'
        self.state = Path('/workspace/p15-partition-synthetic-runtime.json')
        self.raw = {str(self.state): b'synthetic immutable runtime'}
        self.files = {m.NAME: self.source, 'probe_driver.py': b'synthetic driver',
                      'probe.log': b'synthetic Lean output', 'serialized-probe.log': b'synthetic serializer output',
                      m.TARGET + '/direct-import-stock-readiness.log': b'synthetic existing import cache'}
        self.guard = lambda lane, argv: ['python3', 'guard', '--state', str(self.state)] + argv
        self.serialize = lambda lane, receipt, argv: ['python3', 'serialize', '--state', str(self.state), '--receipt', str(receipt)] + argv
        self.dependencies = {'forty_existing_inputs': 'unchanged'}
        self.reference = {'source_acceptance_commit': m.ORIGINAL_COMMIT}
        self.variation = {'status': 'REVALIDATED', 'original_acceptance': m.VARIATION_COMMIT}
        self.variation_owner = {'owned': 22, 'public': 21}
        self.native = {'required_existing_inputs': {'synthetic Piecewise input': 'unchanged'}}
        self.c = SimpleNamespace(commit='a' * 40,
            support=SimpleNamespace(native_input=lambda x: self.native),
            g=SimpleNamespace(snapshot=lambda s, spec: self.dependencies),
            s=SimpleNamespace(h=SimpleNamespace(guard=self.guard, serialize=self.serialize),
                api=SimpleNamespace(read_json=lambda p: json.loads(self.raw[str(p)]))),
            x=SimpleNamespace(spec=object(), retained=SimpleNamespace(reference=self.reference),
                variation=self.variation, c=object(), v=SimpleNamespace(accepted=lambda c: self.variation_owner)))
        self.worker = ['python3', '-B', str(self.run / 'probe_driver.py'), '--worker']
        self.probe = self.cmd('probe', self.guard(0, ['lake', '--no-build', 'env', 'lean', str(self.run / m.NAME)]))
        self.direct = self.cmd(m.TARGET + '/direct-import-stock-readiness',
            self.guard(0, ['lake', '--no-build', 'build'] + ['+' + name + ':olean' for name in m.IMPORTS]))
        self.outer = self.cmd('serialized-probe', self.serialize(0, self.run / 'LANE.json', self.worker))
        self.lane = {'status': 'VALIDATION_LANE_FINISHED', 'exit_code': 0, 'argv': self.worker,
            'state': str(self.state), 'state_sha256': m.digest(self.raw[str(self.state)]),
            'no_compiler_guard_runtime_or_memory_limit_changes': True,
            'whole_chain_including_original_checker_serialized': True}
        self.result = {'schema': 'p15_signed_exit_partition_no_output_probe_v1', 'target': m.TARGET,
            'source_base': m.ORIGINAL_COMMIT, 'source_path': m.LIVE, 'source_sha256': self.sha,
            'source_bytes': len(self.source), 'exit_code': 0, 'probe_passed': True, 'preservation_passed': True,
            'output_object_requested': False, 'new_owner_accepted': False, 'new_formal_credit': 0,
            'whole_P1_5_complete': False, 'direct_imports': m.IMPORTS, 'project_dependency_count': 40,
            'dependency_artifact_positions': 840, 'protected_dictionary_sources': 289,
            'protected_dictionary_dependency_artifact_positions': 6048, 'dictionary_reference': self.reference,
            'variation_original_acceptance': self.variation, 'command': self.probe,
            'direct_import_readiness': self.direct}
        self.before = {'actual_dependency_context': self.dependencies,
            'dictionary_acceptance_reference': self.reference, 'variation': self.variation_owner,
            'native_direct_import': copy.deepcopy(self.native)}

    def cmd(self, name, argv):
        raw = self.files[name + '.log']
        return {'argv': argv, 'cwd': str(m.PROJECT), 'exit_code': 0, 'actual_built_modules': [],
            'actual_failed_modules': [], 'log': str(self.run / (name + '.log')),
            'log_bytes': len(raw), 'log_sha256': m.digest(raw)}

    def execute(self):
        objects = {'PROBE_RESULT.json': self.result, 'probe-command.json': self.probe,
            m.TARGET + '/direct-import-stock-readiness-command.json': self.direct,
            'serialized-probe-command.json': self.outer, 'LANE.json': self.lane,
            'PRESERVED_BEFORE.json': self.before, 'PRESERVED_AFTER.json': self.before,
            'GIT_BEFORE.json': {'dirty': 'preserved'}, 'GIT_AFTER.json': {'dirty': 'preserved'}}
        self.files.update({name: json.dumps(obj, sort_keys=True).encode() for name, obj in objects.items()})
        self.raw.update({str(self.run / name): raw for name, raw in self.files.items()})
        row = {'directory': str(self.run), 'source_sha256': self.sha, 'source_bytes': len(self.source),
            'result_bytes': len(self.files['PROBE_RESULT.json']), 'result_sha256': m.digest(self.files['PROBE_RESULT.json']),
            'driver_sha256': m.digest(self.files['probe_driver.py']), 'log_sha256': m.digest(self.files['probe.log'])}
        published = {m.PACKET + '/probe/' + name: raw for name, raw in self.files.items()}
        with patch.object(m, 'regular', side_effect=lambda p: self.raw[str(p)]), \
             patch.object(m, 'git', side_effect=lambda commit, path: published[path]):
            return m.probe_record(self.c, row, 'probe', True)

    def test_complete_outer_control(self):
        self.assertIs(self.execute()['probe_passed'], True)

    def test_worker_success_outer_failure_rejected(self):
        self.outer['exit_code'] = 1
        with self.assertRaisesRegex(ValueError, 'command provenance'):
            self.execute()

    def test_worker_success_incomplete_lane_rejected(self):
        self.lane['status'] = 'VALIDATION_LANE_STARTED'
        with self.assertRaisesRegex(ValueError, 'outer serializer/lane'):
            self.execute()

    def test_runtime_lane_hash_rejected(self):
        self.lane['state_sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'outer serializer/lane'):
            self.execute()

    def test_dependency_build_rejected(self):
        self.outer['actual_built_modules'] = [m.PROJECT_IMPORTS[0]]
        with self.assertRaisesRegex(ValueError, 'command provenance'):
            self.execute()

    def test_dictionary_identity_reassignment_rejected(self):
        self.result['dictionary_reference'] = {'source_acceptance_commit': 'a' * 40}
        with self.assertRaisesRegex(ValueError, 'original dependency identities'):
            self.execute()

    def test_native_input_changed_after_probe_rejected(self):
        self.native['required_existing_inputs']['synthetic Piecewise input'] = 'different'
        with self.assertRaisesRegex(ValueError, 'input/preservation chain'):
            self.execute()


class ReadonlyLifecycleBoundary(unittest.TestCase):
    def test_fresh_check_does_not_compile_or_install(self):
        with tempfile.TemporaryDirectory() as root:
            c = SimpleNamespace(run=Path(root) / 'never-created', ident={'synthetic': True},
                s=SimpleNamespace(ops=SimpleNamespace(run=lambda *a, **k: self.fail('compiler must not run'))))
            with patch.object(m, 'fresh', return_value=None), patch.object(m, 'fixed', return_value={}), \
                 patch.object(m, 'install', side_effect=AssertionError('install must not run')):
                result = m.check(c)
            self.assertEqual(result['status'], 'FRESH')
            self.assertEqual(result['normal_or_kernel_commands_executed'], 0)
            self.assertFalse(c.run.exists())

    def test_partial_operation_is_retained_and_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            run = Path(root) / 'partial'
            run.mkdir()
            marker = run / 'failure.log'
            marker.write_bytes(b'original failure must survive')
            c = SimpleNamespace(run=run, s=SimpleNamespace(api=SimpleNamespace(read_json=lambda p: self.fail('not yet'))))
            with self.assertRaisesRegex(ValueError, 'partial/failed formal operation'):
                m.check(c)
            self.assertEqual(marker.read_bytes(), b'original failure must survive')


if __name__ == '__main__':
    unittest.main()
