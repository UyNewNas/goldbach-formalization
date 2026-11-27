"""Local-only receipt boundary tests. No Lean process or original cloud path is used."""
import importlib.util
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('complete_shape', HERE / 'complete_shape.py')
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)
OLD = HERE.parents[3] / 'recovery-20261127/remaining9-v2-exact/stage'
PINS = json.loads((HERE / 'PINS.json').read_bytes())
R, V, E = S.bootstrap(OLD, OLD / S.OLD_TOOL.relative_to(S.OLD), PINS)
SOURCE = HERE.parents[2] / 'ImbalancedChen' / (S.SHORT + '.lean')


class ReceiptBoundary(unittest.TestCase):
    def setUp(self):
        scratch = TemporaryDirectory(dir=HERE)
        self.addCleanup(scratch.cleanup)
        stage = Path(scratch.name)
        receipts = stage / 'verification'
        receipts.mkdir()
        obj = stage / 'objects' / S.REL.with_suffix('.olean')
        obj.parent.mkdir(parents=True)
        settings = patch.multiple(S, STAGE=stage, RECEIPTS=receipts, RUN=receipts / 'RUN.json', SOURCE=SOURCE, OBJECT=obj)
        settings.start()
        self.addCleanup(settings.stop)
        self.ctx = {'runtime': {'lean_binary': {'path': '/pinned/lean'}, 'leanchecker_binary': {'path': '/pinned/leanchecker'}},
                    'targets': [{'source': R.fp(SOURCE), 'audit': R.fp(HERE / 'owned-audits' / (S.SHORT + '.lean'))}],
                    'dependencies': {}, 'cwd': str(stage / 'project'), 'environment': {}}
        R.dump_new(S.RUN, self.ctx)

    def test_trust_and_checker_isolation(self):
        normal = S.command_fields(R, self.ctx, 'normal', None)
        self.assertIn('--trust=0', normal['argv'])
        self.assertIn('-DwarningAsError=true', normal['argv'])
        S.OBJECT.write_bytes(b'fixture')
        owned = S.command_fields(R, self.ctx, 'owned', {'fixture': True})
        self.assertIn('--trust=0', owned['argv'])
        self.assertEqual(S.command_fields(R, self.ctx, 'kernel', {'fixture': True})['argv'],
                         ['/pinned/leanchecker', '--verbose', S.MODULE])

    def test_reject_unreceipted_object_and_missing_seal(self):
        S.OBJECT.write_bytes(b'fixture')
        with self.assertRaisesRegex(ValueError, 'Unreceipted'):
            S.prior_steps(R, self.ctx)
        S.OBJECT.unlink()
        command, log, result, _ = S.step_paths('normal')
        R.dump_new(command, {})
        log.write_text('')
        R.dump_new(result, {'status': 'succeeded', 'exit_code': 0})
        with self.assertRaisesRegex(ValueError, 'without replay'):
            S.prior_steps(R, self.ctx)

    def test_retained_export_blocks_replay_when_receipts_are_lost(self):
        (S.STAGE / 'exports').mkdir()
        (S.STAGE / 'exports/shape-evidence.tar.xz').write_bytes(b'fixture')
        with self.assertRaisesRegex(ValueError, 'missing successful evidence'):
            S.prior_steps(R, self.ctx)

    def test_existing_run_must_match_expected_context(self):
        with self.assertRaisesRegex(ValueError, 'Existing evidence differs'):
            S.recorded(R, S.RUN, dict(self.ctx, environment={'LEAN_OPTS': 'extra'}))
        self.assertEqual(R.read(S.RUN), self.ctx)

    def test_source_and_namespace_fail_closed(self):
        bad = S.STAGE / 'repair.lean'
        bad.write_bytes(SOURCE.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'Frozen file changed'):
            S.verified_bytes(bad, PINS['repaired_source'])
        expected = 'ImbalancedChen/Only.olean'
        root = S.OBJECT.parents[1]
        p = root / expected
        p.write_bytes(b'fixture')
        S.actual_namespace(R, root, {expected}, {expected})
        (root / 'ImbalancedChen/Shadow.olean').write_bytes(b'extra')
        with self.assertRaisesRegex(ValueError, 'Unknown module'):
            S.actual_namespace(R, root, {expected}, {expected})

    def test_forbidden_axiom_missing_print_and_diagnostic(self):
        names = [line.split()[-1] for line in SOURCE.read_text().splitlines() if line.startswith('#print axioms ')]
        lines = [f"'{S.MODULE}.{n}' depends on axioms: [propext,\n Quot.sound]\n" for n in names]
        good = ''.join(lines)
        self.assertEqual(S.log_facts(R, self.ctx, 'normal', good)['printed_axioms'], ['Quot.sound', 'propext'])
        for bad in [good.replace('propext', 'sorryAx', 1), ''.join(lines[:-1]), 'warning: issue\n' + good]:
            with self.subTest(bad=bad[:45]), self.assertRaises(ValueError):
                S.log_facts(R, self.ctx, 'normal', bad)

    def test_clone_all_receipt_links_around_bad_argv_still_rejected(self):
        cmd_path, log, result_path, seal_path = S.step_paths('normal')
        command = S.command_fields(R, self.ctx, 'normal', None)
        command['argv'].remove('--trust=0')
        command['started_unix'] = 1
        R.dump_new(cmd_path, command)
        log.write_text('')
        S.OBJECT.write_bytes(b'object')
        R.dump_new(result_path, {'command': R.fp(cmd_path), 'run': R.fp(S.RUN), 'object': R.fp(S.OBJECT),
                                 'status': 'succeeded', 'exit_code': 0, 'log': R.fp(log)})
        R.dump_new(seal_path, {'run': R.fp(S.RUN), 'command': R.fp(cmd_path), 'result': R.fp(result_path)})
        with self.assertRaisesRegex(ValueError, 'execution plan'):
            S.prior_steps(R, self.ctx)

    def test_resume_revalidates_normal_without_replaying_and_binds_kernel_to_same_object(self):
        names = [line.split()[-1] for line in SOURCE.read_text().splitlines() if line.startswith('#print axioms ')]
        normal_log = ''.join(f"'{S.MODULE}.{n}' does not depend on any axioms\n" for n in names)

        def simulate(_, argv, cwd, env, log):
            if argv[0] == '/pinned/lean':
                self.assertFalse(S.OBJECT.exists())
                S.OBJECT.write_bytes(b'synthetic unit test object')
                log.write_text(normal_log)
            else:
                log.write_text('replaying ' + S.MODULE + '\n')
            return 0, None, 4096, 0.001

        with patch.object(S, 'run_process', side_effect=simulate) as launch:
            normal = S.execute(R, V, self.ctx, 'normal', None, lambda: None)
            self.assertEqual(S.prior_steps(R, self.ctx), [normal])
            with self.assertRaisesRegex(ValueError, 'repeat'):
                S.execute(R, V, self.ctx, 'normal', None, lambda: None)
            kernel = S.execute(R, V, self.ctx, 'kernel', normal, lambda: None)
            self.assertEqual(S.prior_steps(R, self.ctx), [normal, kernel])
            self.assertEqual(launch.call_count, 2)
        S.OBJECT.write_bytes(b'different object')
        with self.assertRaisesRegex(ValueError, 'changed'):
            S.prior_steps(R, self.ctx)

    def test_reject_changed_owned_project_closure(self):
        row = 'P2OriginalSaving19Geometry05ScalableShapeRows'
        log = (OLD / 'verification' / S.CONT / row / 'owned.log').read_text()
        other = 'ImbalancedChen.' + row
        with patch.object(S, 'MODULE', other), self.assertRaisesRegex(ValueError, 'project import closure'):
            S.log_facts(R, {'targets': [{'module': other, 'transitive_dependencies': []}]}, 'owned', log)


if __name__ == '__main__':
    unittest.main()
