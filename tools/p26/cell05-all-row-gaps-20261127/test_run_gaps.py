"""Local boundary tests. Real immutable metadata/helpers; no Lean or cloud calls."""
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
MATERIALS = HERE.parents[3]
PURE = MATERIALS / 'recovery-20261127/cell05-all-row-gaps/pure2'
SHAPE = HERE.parent / 'cell05-shape-completion-20261127'
spec = importlib.util.spec_from_file_location('accepted_shape_reference', SHAPE / 'complete_shape.py')
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)
OLD = MATERIALS / 'recovery-20261127/remaining9-v2-exact/stage'
R, V, E = S.bootstrap(OLD, OLD / S.OLD_TOOL.relative_to(S.OLD), json.loads((SHAPE / 'PINS.json').read_text()))
SHAPE_CONTEXT = json.loads((MATERIALS / 'recovery-20261127/shape-completion-v1/exact/verification/RUN.json').read_text())
G = None
if (HERE / 'run_gaps.py').exists():
    spec = importlib.util.spec_from_file_location('new_gap_runner', HERE / 'run_gaps.py')
    G = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(G)
MODULE = 'ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps'
SOURCE = HERE.parents[2] / 'ImbalancedChen/P2OriginalSaving19Cell05AllRowGaps.lean'
AUDIT = HERE.parents[4] / 'shape_completion_runner_next_gate/owned-audits/P2OriginalSaving19Cell05AllRowGaps.lean'


class PureJoin(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(G, 'New strict runner is not implemented')
        tmp = TemporaryDirectory(dir=HERE)
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / 'pure2'
        shutil.copytree(PURE, self.root)
        self.pin = R.fp(self.root / 'TRANSPORT.json')

    def test_actual_two_pure_chains_accept_without_added_owned_requirement(self):
        value = G.validate_pure2(R, self.root, self.pin, SHAPE_CONTEXT)
        self.assertEqual(set(value['dependencies']), {
            'ImbalancedChen.P2OriginalSaving19RowNumericsPure',
            'ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure'})
        self.assertEqual(value['accepted_old_normal_kernel_records'], 4)
        self.assertEqual(value['new_supplier_owned_audits'], 0)
        self.assertFalse(value['historical_loaded_inventory_claimed'])

    def test_altered_original_log_rejected_before_reuse(self):
        p = next(self.root.rglob('normal-namespace-v2.log'))
        p.write_bytes(p.read_bytes() + b'warning: changed\n')
        with self.assertRaises(ValueError):
            G.validate_pure2(R, self.root, self.pin, SHAPE_CONTEXT)

    def test_wrong_current_object_rejected_before_reuse(self):
        p = self.root / 'objects/ImbalancedChen/P2OriginalSaving19RowNumericsPure.olean'
        p.write_bytes(b'wrong same-name object')
        with self.assertRaises(ValueError):
            G.validate_pure2(R, self.root, self.pin, SHAPE_CONTEXT)

    def test_same_name_overlap_conflict_is_not_hidden_by_canonical_counts(self):
        ctx = json.loads(json.dumps(SHAPE_CONTEXT))
        ctx['dependencies']['ImbalancedChen.P2OriginalSaving19ArchiveSchema']['object']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            G.validate_pure2(R, self.root, self.pin, ctx)


class NewOwnerBoundary(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(G, 'New strict runner is not implemented')
        tmp = TemporaryDirectory(dir=HERE)
        self.addCleanup(tmp.cleanup)
        stage = Path(tmp.name)
        source = stage / 'project/ImbalancedChen/P2OriginalSaving19Cell05AllRowGaps.lean'
        source.parent.mkdir(parents=True)
        source.write_bytes(SOURCE.read_bytes())
        audit = stage / 'owned-audit.lean'
        audit.write_bytes(AUDIT.read_bytes())
        (stage / 'verification').mkdir()
        (stage / 'objects/ImbalancedChen').mkdir(parents=True)
        self.ctx = {'schema': 'cell05_all_row_gaps_run_v1', 'stage': str(stage),
            'cwd': str(stage / 'project'), 'environment': {},
            'runtime': {'lean_binary': {'path': '/pinned/lean'}, 'leanchecker_binary': {'path': '/pinned/leanchecker'}},
            'targets': [{'module': MODULE, 'source': R.fp(source), 'audit': R.fp(audit), 'transitive_dependencies': []}],
            'dependencies': {}, 'rss_limit_bytes': 12 * 1024**3, 'wall_limit_seconds': 900,
            'old_proof_commands': 0, 'P2_6_complete': False}
        R.dump_new(stage / 'verification/RUN.json', self.ctx)
        self.runner = G.Runner(stage, R, V, E, S, self.ctx)
        self.count = 0

    def names(self):
        names = []
        source = Path(self.ctx['targets'][0]['source']['path']).read_text()
        for line in source.splitlines():
            if line.startswith('#print axioms '):
                n = line.split()[-1]
                private = any(x.startswith('private ') and (' ' + n + ' ' in x or ' ' + n + ' :' in x)
                              for x in source.splitlines())
                names.append(('_private.' + MODULE + '.0.' if private else '') + MODULE + '.' + n)
        return names

    def normal_log(self):
        return ''.join("'" + n + "' depends on axioms: [propext, Quot.sound]\n" for n in self.names())

    def owned_log(self):
        names = self.names() + ['_private.' + MODULE + '.0.' + MODULE + '.generated_helper']
        lines = ['P26_GEOMETRY01_AUDIT_IMPORTS ' + json.dumps([MODULE]),
                 'P26_GEOMETRY01_AUDIT_INVENTORY ' + json.dumps({'module': MODULE, 'serialized': names, 'environment': names})]
        for name in names:
            lines.append('P26_GEOMETRY01_AUDIT_DECL ' + json.dumps({'name': name, 'module': MODULE,
                'unsafe': False, 'partial': False, 'axiom': False, 'type': 'Nat', 'axioms': ['propext']}))
        lines.append('P26_GEOMETRY01_AUDIT_COMPLETE ' + json.dumps({'module': MODULE, 'count': len(names)}))
        return '\n'.join(lines) + '\n'

    def simulate(self, argv, cwd, env, log):
        # The external Lean process is unavailable in local tests. Preserve its actual output/object effects.
        self.count += 1
        mode = 'kernel' if argv[0].endswith('leanchecker') else 'normal' if '-o' in argv else 'owned'
        if mode == 'normal':
            self.runner.object.write_bytes(b'one fixture object')
        with log.open('x') as f:
            f.write(self.normal_log() if mode == 'normal' else 'replaying ' + MODULE + '\n' if mode == 'kernel' else self.owned_log())
        return 0, None, 12, 0.01

    def test_only_new_target_strict_argv_and_stock_checker(self):
        c = self.runner.command_fields('normal', None)
        self.assertEqual(c['argv'][:3], ['/pinned/lean', '--trust=0', '-DwarningAsError=true'])
        self.assertEqual(c['argv'][-1], 'ImbalancedChen/P2OriginalSaving19Cell05AllRowGaps.lean')
        self.runner.object.write_bytes(b'object')
        self.assertEqual(self.runner.command_fields('kernel', {'fixture': True})['argv'],
                         ['/pinned/leanchecker', '--verbose', MODULE])
        self.assertIn('--trust=0', self.runner.command_fields('owned', {'fixture': True})['argv'])

    def test_private_prints_and_generated_owned_declarations_are_included(self):
        facts = self.runner.log_facts('normal', self.normal_log())
        self.assertEqual(len(facts['printed_declarations']), 20)
        owned = self.runner.log_facts('owned', self.owned_log())['owned']
        self.assertEqual(owned['owned_declaration_count'], 21)
        for bad in [self.normal_log().replace('propext', 'sorryAx', 1), self.normal_log().replace(MODULE, 'Wrong.Module', 1),
                    self.normal_log().rsplit("'", 2)[0], 'warning: issue\n' + self.normal_log()]:
            with self.subTest(bad=bad[:60]), self.assertRaises(ValueError):
                self.runner.log_facts('normal', bad)
        with self.assertRaises(ValueError):
            self.runner.log_facts('owned', self.owned_log().replace(json.dumps([MODULE]), json.dumps([MODULE, 'ImbalancedChen.Hidden']), 1))

    def test_two_mode_resume_does_not_launch_accepted_mode(self):
        with patch.object(self.runner, 'process', self.simulate):
            self.runner.execute('normal', None, lambda: None)
            first = self.runner.prior_steps()
            self.runner.execute('kernel', first[-1], lambda: None)
            accepted = self.runner.prior_steps()
            self.assertEqual(len(accepted), 2)
            with self.assertRaises(ValueError):
                self.runner.execute('normal', None, lambda: None)
        self.assertEqual(self.count, 2)

    def test_trailing_receipt_loss_keeps_durable_barrier_and_blocks_replay(self):
        with patch.object(self.runner, 'process', self.simulate):
            first = self.runner.execute('normal', None, lambda: None)
            self.runner.execute('kernel', first, lambda: None)
            for path in self.runner.step_paths('kernel'):
                path.unlink()
            with self.assertRaises(ValueError):
                self.runner.execute('kernel', first, lambda: None)
        self.assertTrue(self.runner.witness_path('kernel').is_file())
        self.assertEqual(self.count, 2)

    def test_changed_command_cannot_be_accepted_by_rebinding_its_seal(self):
        with patch.object(self.runner, 'process', self.simulate):
            self.runner.execute('normal', None, lambda: None)
        command = self.runner.step_paths('normal')[0]
        data = R.read(command); data['argv'].remove('--trust=0'); command.write_text(json.dumps(data))
        with self.assertRaises(ValueError):
            self.runner.prior_steps()

    def test_private_pretty_alias_is_bound_to_its_unique_full_owned_name(self):
        aliases = ''.join("'" + MODULE + '.' + n.rsplit('.', 1)[1] + "' depends on axioms: [propext]\n" for n in self.names())
        with patch.object(self, 'normal_log', lambda: aliases), patch.object(self.runner, 'process', self.simulate):
            accepted = []
            for mode in ('normal', 'kernel', 'owned'):
                try:
                    accepted.append(self.runner.execute(mode, accepted[-1] if accepted else None, lambda: None))
                except RuntimeError as exc:
                    self.fail('A valid private pretty alias must bind uniquely to the complete owned name: ' + str(exc))
            self.assertEqual(len(self.runner.prior_steps()), 3)

    def test_post_launch_input_change_retains_failed_result_and_never_retries(self):
        calls = 0
        def check():
            nonlocal calls
            calls += 1
            if calls > 1:
                raise ValueError('input changed after launch')
        with patch.object(self.runner, 'process', self.simulate):
            with self.assertRaises(RuntimeError):
                self.runner.execute('normal', None, check)
            self.assertEqual(R.read(self.runner.step_paths('normal')[2])['status'], 'failed')
            with self.assertRaises(ValueError):
                self.runner.execute('normal', None, lambda: None)
        self.assertEqual(self.count, 1)
        self.assertTrue((self.runner.receipts / 'STOPPED.json').is_file())

    def test_verify_of_unpublished_stage_is_readonly(self):
        before = {str(p.relative_to(self.runner.stage)): p.read_bytes() for p in self.runner.stage.rglob('*') if p.is_file()}
        with self.assertRaises(ValueError):
            self.runner.finish([], lambda: None, verify_only=True)
        after = {str(p.relative_to(self.runner.stage)): p.read_bytes() for p in self.runner.stage.rglob('*') if p.is_file()}
        self.assertEqual(before, after)

    def test_complete_three_mode_archive_rechecks_without_writing_or_relaunch(self):
        predecessor = self.runner.stage / 'predecessor-fixture'
        predecessor.mkdir()
        for name in ('RUN.json', 'SUCCESS.json', 'GUARD.json'):
            R.dump_new(predecessor / name, {'fixture': name})
        tool = self.runner.stage / G.TOOL_REL
        tool.mkdir(parents=True)
        (tool / 'fixture.txt').write_text('fixture artifact\n')
        R.dump_new(self.runner.stage / 'SUPPLIER_REUSE.json', {'fixture': True})
        self.ctx.update(shape_stage=str(predecessor), shape_run=R.fp(predecessor / 'RUN.json'),
                        shape_success=R.fp(predecessor / 'SUCCESS.json'),
                        pure2_reuse=R.fp(self.runner.stage / 'SUPPLIER_REUSE.json'),
                        predecessor_artifacts=[R.fp(p) for p in sorted(predecessor.iterdir())],
                        runtime_guard=R.fp(predecessor / 'GUARD.json'), recovery_certificate=R.fp(predecessor / 'GUARD.json'))
        self.runner.run.write_text(json.dumps(self.ctx))
        with patch.object(self.runner, 'process', self.simulate):
            accepted = []
            for mode in ('normal', 'kernel', 'owned'):
                accepted.append(self.runner.execute(mode, accepted[-1] if accepted else None, lambda: None))
            self.runner.finish(accepted, lambda: None)
            before = {str(p): p.read_bytes() for p in self.runner.stage.rglob('*') if p.is_file()}
            self.runner.finish(accepted, lambda: None, verify_only=True)
            self.assertEqual(before, {str(p): p.read_bytes() for p in self.runner.stage.rglob('*') if p.is_file()})
        self.assertEqual(self.count, 3)
        self.assertEqual(R.read(self.runner.receipts / 'owned-declarations.json')['owned_declaration_count'], 21)


class AuthenticatedWorker(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(G, 'New strict runner is not implemented')
        tmp = TemporaryDirectory(dir=HERE)
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        driver = self.root / 'complete_shape.py'
        driver.write_text('from pathlib import Path\nimport sys,json\nSTAGE=Path(' + repr(str(self.root)) + ')\nTOOL=STAGE\n'
            'def main():\n assert sys.argv[1:]==["verify","--recovery-binding-sha256",' + repr('a' * 64) + ']\n'
            ' print(json.dumps({"status":"READ_ONLY_ENTRYPOINT_REACHED"}))\n')
        configuration = self.root / 'PINS.json'; configuration.write_text('{}')
        binding = self.root / 'BINDING.json'; binding.write_text('{}')
        self.config = {'shape': {'stage': str(self.root), 'driver': R.fp(driver), 'configuration': R.fp(configuration),
                                'recovery_binding': R.fp(binding)}}

    def test_actual_isolated_historical_worker_selects_only_verify(self):
        # No Lean or original driver body is executed; this is an isolated launch contract fixture.
        p = Path(self.config['shape']['driver']['path'])
        p.write_text(p.read_text().replace('a' * 64, self.config['shape']['recovery_binding']['sha256']))
        self.config['shape']['driver'] = R.fp(p)
        code = ('import types,json\nfrom pathlib import Path\np=Path(' + repr(str(HERE / 'run_gaps.py')) + ')\n'
            'm=types.ModuleType("g");m.__file__=str(p);exec(compile(p.read_bytes(),str(p),"exec"),m.__dict__)\n'
            'm.historical_worker(json.loads(' + repr(json.dumps(self.config)) + '))\n')
        result = subprocess.run([sys.executable, '-I', '-S', '-B', '-c', code], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), {'status': 'READ_ONLY_ENTRYPOINT_REACHED'})

    def test_altered_predecessor_source_stops_before_child_creation(self):
        p = Path(self.config['shape']['driver']['path'])
        p.write_bytes(p.read_bytes() + b'\n')
        with patch.object(G.subprocess, 'run', side_effect=AssertionError('Must not create a child')):
            with self.assertRaises(ValueError):
                G.verify_shape(self.config, self.root, '0' * 64, R)


if __name__ == '__main__':
    unittest.main()
