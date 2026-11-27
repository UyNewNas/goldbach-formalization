"""Local-only receipt boundary tests. No Lean process or original cloud path is used."""
from contextlib import contextmanager, nullcontext
import importlib.util
import json
import subprocess
import tarfile
import sys
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
        S.publish_witness(R, 'normal', R.fp(cmd_path))
        log.write_text('')
        S.OBJECT.write_bytes(b'object')
        R.dump_new(result_path, {'command': R.fp(cmd_path), 'run': R.fp(S.RUN), 'object': R.fp(S.OBJECT),
                                 'status': 'succeeded', 'exit_code': 0, 'log': R.fp(log)})
        R.dump_new(seal_path, {'run': R.fp(S.RUN), 'command': R.fp(cmd_path), 'result': R.fp(result_path)})
        with self.assertRaisesRegex(ValueError, 'execution plan'):
            S.prior_steps(R, self.ctx)

    def accept_normal_and_kernel(self):
        names = [line.split()[-1] for line in S.SOURCE.read_text().splitlines() if line.startswith('#print axioms ')]
        normal_log = ''.join(f"'{S.MODULE}.{n}' does not depend on any axioms\n" for n in names)

        def simulate(_, argv, cwd, env, log):
            mode = 'normal' if argv[0] == '/pinned/lean' else 'kernel'
            command = S.step_paths(mode)[0]
            self.assertEqual(R.read(S.witness_path(mode)), S.witness_fields(R, mode, R.fp(command)))
            if mode == 'normal':
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
        return [normal, kernel]

    def test_resume_revalidates_normal_without_replaying_and_binds_kernel_to_same_object(self):
        self.accept_normal_and_kernel()
        S.OBJECT.write_bytes(b'different object')
        with self.assertRaisesRegex(ValueError, 'changed'):
            S.prior_steps(R, self.ctx)

    def test_witness_blocks_complete_loss_of_trailing_kernel_group(self):
        normal, _ = self.accept_normal_and_kernel()
        for path in S.step_paths('kernel'):
            path.unlink()
        self.assertTrue(S.witness_path('kernel').is_file())
        with patch.object(S, 'run_process') as launch:
            for action in (lambda: S.prior_steps(R, self.ctx),
                           lambda: S.execute(R, V, self.ctx, 'kernel', normal, lambda: None)):
                with self.assertRaisesRegex(ValueError, 'Orphan launch witness'):
                    action()
            launch.assert_not_called()

    def test_witness_mismatch_and_loss_rejected(self):
        self.accept_normal_and_kernel()
        path = S.witness_path('kernel')
        pin = R.read(path)
        with self.assertRaises(FileExistsError):
            S.publish_witness(R, 'kernel', R.fp(S.step_paths('kernel')[0]))
        for changed in (dict(pin, run={'path': 'wrong'}), dict(pin, command={'path': 'wrong'})):
            path.write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, 'disagrees'):
                S.prior_steps(R, self.ctx)
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'missing witness'):
            S.prior_steps(R, self.ctx)

    def test_verify_does_not_republish_missing_final_evidence(self):
        success = S.RECEIPTS / 'SUCCESS.json'
        index = S.STAGE / 'COMBINED_INDEX.json'
        archive = S.STAGE / 'exports/shape-evidence.tar.xz'
        archive.parent.mkdir()
        for path in (success, index, archive):
            path.write_bytes(b'retained fixture')
        S.require_published()
        for path in (success, index, archive):
            with self.subTest(path=path.name):
                path.unlink()
                before = {p: p.read_bytes() for p in R.tree_files(S.STAGE)}
                with self.assertRaisesRegex(ValueError, 'Missing retained final evidence'):
                    S.finish(R, E, self.ctx, [], lambda: None, verify_only=True)
                self.assertEqual(before, {p: p.read_bytes() for p in R.tree_files(S.STAGE)})
                path.write_bytes(b'retained fixture')

    def test_verify_main_preserves_damaged_directories_and_opens_existing_locks_readonly(self):
        def inventory(root):
            return {p.relative_to(root): None if p.is_dir() else p.read_bytes() for p in root.rglob('*')}

        for missing in ('objects', 'objects/ImbalancedChen', 'verification', 'EXECUTION.lock', 'old/EXECUTION.lock'):
            with self.subTest(missing=missing), TemporaryDirectory(dir=S.STAGE) as tmp:
                base = Path(tmp)
                stage, old = base / 'new', base / 'old'
                tool = stage / 'tools'
                tool.mkdir(parents=True)
                old.mkdir()
                driver = tool / 'complete_shape.py'
                driver.write_bytes((HERE / driver.name).read_bytes())
                (tool / 'PINS.json').write_bytes((HERE / 'PINS.json').read_bytes())
                for member in ('EXECUTION.lock', 'verification/RUN.json', 'verification/SUCCESS.json',
                               'PREFIX8_VALIDATED.json', 'COMBINED_INDEX.json', 'exports/shape-evidence.tar.xz'):
                    if Path(missing) in Path(member).parents or member == missing:
                        continue
                    path = stage / member
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_bytes(b'retained fixture')
                if missing != 'objects':
                    (stage / 'objects').mkdir()
                    if missing != 'objects/ImbalancedChen':
                        (stage / 'objects/ImbalancedChen').mkdir()
                if missing != 'old/EXECUTION.lock':
                    (old / 'EXECUTION.lock').touch()

                observed_lock_modes = []
                actual_open = Path.open

                def read_only_open(path, mode='r', *args, **kwargs):
                    self.assertFalse(any(c in mode for c in 'wax+'), f'verify opened {path} in {mode}')
                    if path.name == 'EXECUTION.lock':
                        observed_lock_modes.append((path, mode))
                    return actual_open(path, mode, *args, **kwargs)

                receipts = stage / 'verification'
                before = inventory(base)
                with (patch.multiple(S, OLD=old, STAGE=stage, RECEIPTS=receipts, RUN=receipts / 'RUN.json',
                                     PREFIX=stage / 'PREFIX8_VALIDATED.json', TOOL=tool, __file__=str(driver)),
                      patch.object(sys, 'argv', [str(driver), 'verify', '--recovery-binding-sha256', '0' * 64]),
                      patch.object(S, 'child_import_boundary', return_value=nullcontext()),
                      patch.object(S, 'bootstrap', return_value=(R, V, E)),
                      patch.object(S, 'validate_original', return_value=({}, {}, {}, {})),
                      patch.object(S, 'run_process') as launch, patch.object(Path, 'open', read_only_open)):
                    with self.assertRaises((ValueError, FileNotFoundError)):
                        S.main()
                    launch.assert_not_called()
                self.assertEqual(before, inventory(base))
                if missing.startswith('objects'):
                    self.assertEqual(observed_lock_modes,
                                     [(old / 'EXECUTION.lock', 'rb'), (stage / 'EXECUTION.lock', 'rb')])

    @contextmanager
    def recovery_fixture(self, tool):
        """Tiny retained inputs. The real recovery protocol is never executed."""
        root = S.STAGE / 'fixture-recovery'
        protocol = root / 'tools'
        protocol.mkdir(parents=True)
        old_guard = S.STAGE / 'fixture-original-guard.json'
        snapshot = S.STAGE / 'fixture-original-snapshot.json'
        R.dump_new(old_guard, {'old': 'guard'})
        R.dump_new(snapshot, {'old': 'snapshot'})
        anchors = {'original_guard': R.fp(old_guard), 'original_snapshot': R.fp(snapshot)}
        R.dump_new(protocol / 'ANCHORS.json', anchors)
        for name in ('recovery.py', 'protocol_core.py', 'recovery_worker.py'):
            (protocol / name).write_text('# fixture only\n')
        manifest = protocol / 'WORKFLOW_MANIFEST.json'
        R.dump_new(manifest, {'schema': 'p26_runtime_recovery_workflow_v1', 'files': [
            {'relative_path': p.name, **E.data_pin(p.read_bytes())} for p in sorted(protocol.iterdir())]})
        binding = {'schema': 'cell05_shape_recovery_binding_v1', 'protocol_manifest': R.fp(manifest)}
        for key, name in S.RECOVERY_NAMES.items():
            R.dump_new(root / name, {'synthetic': name})
            binding[key] = R.fp(root / name)
        binding_path = tool / 'RECOVERY_BINDING.json'
        R.dump_new(binding_path, binding)
        binding_pin = R.fp(binding_path)
        response = {k: v for k, v in binding.items() if k != 'schema'}
        response.update(schema='p26_runtime_recovery_verified_v1', status='PASS_EXPLICIT_RUNTIME_RECOVERY',
                        original_live_guard_validator_passed=False, original_evidence_rewritten=False, P2_6_complete=False, old_Lean_commands=0,
                        original_runtime_guard=anchors['original_guard'], original_snapshot=anchors['original_snapshot'],
                        original={'frozen_inputs': [anchors['original_guard']]}, frozen_inputs=[anchors['original_guard']],
                        target={'fixture': True}, dependencies=[], prefix8={'fixture': True})
        self.ctx['recovery_binding'] = binding_pin
        S.RUN.write_text(json.dumps(self.ctx))
        with patch.multiple(S, TOOL=tool, RECOVERY=root, PROTOCOL=protocol):
            yield binding_pin, response

    def test_recovery_authentication_precedes_invocation_and_binds_existing_run(self):
        tool = S.STAGE / 'tools'
        tool.mkdir()
        with self.recovery_fixture(tool) as (binding, _), patch.object(S.subprocess, 'run') as invoke:
            worker = S.PROTOCOL / 'recovery_worker.py'
            original = worker.read_bytes()
            worker.write_bytes(original.replace(b'fixture', b'changed'))
            with self.assertRaisesRegex(ValueError, 'workflow file changed'):
                S.verify_recovery(R, binding['sha256'])
            worker.write_bytes(original)
            (S.PROTOCOL / '__pycache__').mkdir()
            with self.assertRaisesRegex(ValueError, 'Unexpected namespace'):
                S.verify_recovery(R, binding['sha256'])
            (S.PROTOCOL / '__pycache__').rmdir()
            path = tool / 'RECOVERY_BINDING.json'
            path.write_bytes(path.read_bytes() + b' ')
            with self.assertRaisesRegex(ValueError, 'binding SHA'):
                S.verify_recovery(R, binding['sha256'])
            with self.assertRaisesRegex(ValueError, 'Existing RUN'):
                S.verify_recovery(R, R.fp(path)['sha256'])
            invoke.assert_not_called()

    def test_recovery_command_checks_artifacts_frozen_inputs_and_explicit_guard_boundary(self):
        tool = S.STAGE / 'tools'
        tool.mkdir()
        with self.recovery_fixture(tool) as (binding, response), patch.object(S.subprocess, 'run') as invoke:
            def answer(doc):
                invoke.return_value = subprocess.CompletedProcess([], 0, stdout=json.dumps(doc).encode(), stderr=b'')
            answer(response)
            view = S.verify_recovery(R, binding['sha256'])
            self.assertEqual(view['binding'], binding)
            self.assertEqual(invoke.call_args.args[0], [sys.executable, '-I', '-S', '-B', str(S.PROTOCOL / 'recovery.py'),
                'verify', '--certificate-sha256', response['certificate']['sha256'], '--certificate-bytes',
                str(response['certificate']['bytes'])])
            for updated in [{'certificate': response['history']}, {'current_runtime_guard': response['original_runtime_guard']},
                            {'original_live_guard_validator_passed': True}, {'old_Lean_commands': 1}, {'frozen_inputs': []}]:
                with self.subTest(keys=list(updated)), self.assertRaises(ValueError):
                    answer(dict(response, **updated))
                    S.verify_recovery(R, binding['sha256'])
            guard_file = Path(response['current_runtime_guard']['path'])
            guard_file.write_bytes(guard_file.read_bytes() + b' ')
            invoke.reset_mock()
            with self.assertRaisesRegex(ValueError, 'Wrong recovery artifact'):
                S.verify_recovery(R, binding['sha256'])
            invoke.assert_not_called()

    def test_recovered_dependency_pins_and_paths_match_raw_accepted_target(self):
        folder = OLD / 'verification' / S.CONT
        run = R.read(folder / 'RUN.json')['context']
        row = run['targets'][1]
        name = row['module']
        obj = R.read(folder / S.SHORT / 'normal-command.json')['dependency_objects'][name]
        source = dict(row['source'], path=run['cwd'] + '/' + name.replace('.', '/') + '.lean')
        dependency = {'module': name, 'source_path': source['path'], 'object_path': obj['path'],
                      'source': row['source'], 'object': obj, 'project_imports': row['project_imports']}
        S.compare_dependency(R, dependency, row, source, obj)
        for change in [dict(object_path=source['path']), dict(object=dict(obj, sha256='0'*64)), dict(module=S.MODULE),
                       dict(source_path=obj['path']), dict(project_imports=['ImbalancedChen.Unrelated'])]:
            with self.subTest(keys=list(change)), self.assertRaisesRegex(ValueError, 'Wrong recovered supplier'):
                S.compare_dependency(R, dict(dependency, **change), row, source, obj)

    def test_recovered_prefix_compares_exact_historical_modes_objects_and_failure(self):
        folder = OLD / 'verification' / S.CONT
        stopped = R.read(folder / 'STOPPED.json')
        records = stopped['records']
        objects = {}
        for record in records:
            seal = R.read(OLD / Path(record['accepted']['path']).relative_to(S.OLD))
            objects[record['module']] = seal['object']
        failed = R.read(folder / S.SHORT / 'normal-result.json')
        failure = {k: failed[k] for k in ('command', 'log', 'source', 'module', 'mode', 'status', 'exit_code', 'object')}
        failure.update(accepted=False, result=stopped['failed_result'])
        def old_identity(p):
            return {**R.fp(p), 'path': str(S.OLD / p.relative_to(OLD))}
        pilot = old_identity(OLD / 'verification' / S.PILOT / 'STOPPED.json')
        final = old_identity(folder / 'STOPPED.json')
        state = dict(accepted_steps=24, accepted_targets=8, records=records, objects=objects, failure=failure,
                     pilot_index=pilot, failed_index=final)
        S.compare_prefix(state, records, failure, objects, pilot, final)
        for change in [dict(records=records[1:]), dict(failure=dict(failure, exit_code=0)), dict(objects={}),
                       dict(pilot_index=final), dict(accepted_targets=9)]:
            with self.subTest(keys=list(change)), self.assertRaisesRegex(ValueError, 'failed original chain'):
                S.compare_prefix(dict(state, **change), records, failure, objects, pilot, final)

    def test_verify_retained_archive_checks_members_and_witnesses_read_only(self):
        tool = S.STAGE / 'tools'
        tool.mkdir()
        source = S.STAGE / 'project' / S.REL.with_suffix('.lean')
        source.parent.mkdir(parents=True)
        source.write_bytes(SOURCE.read_bytes())
        audit = tool / (S.SHORT + '.lean')
        audit.write_bytes((HERE / 'owned-audits' / audit.name).read_bytes())
        for name in ('complete_shape.py', 'PINS.json'):
            (tool / name).write_bytes((HERE / name).read_bytes())
        prefix = S.STAGE / 'PREFIX8_VALIDATED.json'
        R.dump_new(prefix, {'fixture': True})
        symbol = S.MODULE + '.fixture'
        owned = '\n'.join('P26_GEOMETRY01_AUDIT_' + label + ' ' + json.dumps(row) for label, row in [
            ('IMPORTS', [S.MODULE]), ('INVENTORY', {'module': S.MODULE, 'serialized': [symbol], 'environment': [symbol]}),
            ('DECL', {'module': S.MODULE, 'name': symbol, 'type': 'True', 'unsafe': False, 'partial': False,
                      'axiom': False, 'axioms': []}), ('COMPLETE', {'module': S.MODULE, 'count': 1})])

        def simulate_owned(_, argv, cwd, env, log):
            self.assertEqual(argv[-1], str(audit))
            log.write_text(owned)
            return 0, None, 4096, 0.001

        with (patch.multiple(S, TOOL=tool, SOURCE=source, AUDIT=audit, PREFIX=prefix),
              self.recovery_fixture(tool) as (binding, response)):
            _, _, artifacts = S.authenticate_recovery(R, binding['sha256'])
            self.ctx['recovery_artifacts'] = artifacts
            self.ctx['recovery_certificate'] = response['certificate']
            self.ctx['targets'] = [{'module': S.MODULE, 'source': R.fp(source), 'audit': R.fp(audit),
                                    'transitive_dependencies': []}]
            self.ctx['runtime_guard'] = {'fixture': True}
            S.RUN.write_text(json.dumps(self.ctx))
            accepted = self.accept_normal_and_kernel()
            with patch.object(S, 'run_process', side_effect=simulate_owned):
                accepted.append(S.execute(R, V, self.ctx, 'owned', accepted[-1], lambda: None))
            S.finish(R, E, self.ctx, accepted, lambda: None)
            with tarfile.open(S.STAGE / 'exports/shape-evidence.tar.xz', 'r:xz') as archive:
                for row in artifacts:
                    member = 'recovery/' + str(Path(row['path']).relative_to(S.RECOVERY))
                    self.assertEqual(E.data_pin(archive.extractfile(member).read()),
                                     {k: row[k] for k in ('bytes', 'sha256')})
            before = {p: R.fp(p) for p in R.tree_files(S.STAGE)}
            with patch.object(E, 'write_verified_archive', side_effect=AssertionError('verification attempted to publish')):
                S.finish(R, E, self.ctx, accepted, lambda: None, verify_only=True)
                self.assertEqual(before, {p: R.fp(p) for p in R.tree_files(S.STAGE)})
                index = S.STAGE / 'COMBINED_INDEX.json'
                index.write_text('{}')
                with self.assertRaisesRegex(ValueError, 'Retained final summary differs'):
                    S.finish(R, E, self.ctx, accepted, lambda: None, verify_only=True)
                self.assertEqual(index.read_text(), '{}')

    def test_isolated_child_entrypoints_require_clean_import_roots(self):
        # The actual frozen origin probe and prefix entrypoint occupy the same root as on P2.
        here = S.STAGE / 'remaining9-tools'
        here.mkdir()
        old_tool = OLD / S.OLD_TOOL.relative_to(S.OLD)
        for name in ('origin_probe.py', 'prefix_validator.py'):
            (here / name).write_bytes((old_tool / name).read_bytes())
        origins = {}
        roots = {}
        for family in ('prefix13', 'shape1'):
            stage = S.STAGE / family
            root = stage / 'tools'
            root.mkdir(parents=True)
            (stage / 'EXECUTION.lock').touch()
            helper = root / 'receipt_checks.py'
            helper.write_text('# harmless test fixture\n')
            verifier = root / 'VERIFIER.json'
            R.dump_new(verifier, {'workflow_files': [dict(R.fp(helper), relative_path=helper.name)]})
            origins[family] = {'stage': str(stage), 'tool_relative_path': 'tools', 'verifier': R.fp(verifier),
                               'verifier_name': verifier.name}
            roots[family] = root
        R.dump_new(here / 'BOUNDARY.json', {'origins': origins})
        rows = [dict(R.fp(path), relative_path=path.name) for path in here.iterdir()]
        m = here / 'REMAINING9_VERIFIER.json'
        R.dump_new(m, {'workflow_files': rows})
        pins = {'original_verifier': R.fp(m)}
        with S.child_import_boundary(here, pins):
            result = subprocess.run([sys.executable, '-I', '-B', str(here / 'origin_probe.py'), '--help'],
                                    capture_output=True, check=True)
            self.assertIn(b'--kind', result.stdout)
        for path in [here / '__pycache__/prefix_validator.cpython-fixture.pyc',
                     roots['prefix13'] / 'receipt_checks.pyc', roots['shape1'] / 'receipt_checks.so',
                     roots['shape1'] / 'package/__init__.py', roots['shape1'] / 'unlisted.py']:
            with self.subTest(path=path):
                path.parent.mkdir(exist_ok=True)
                path.write_bytes(b'inert fixture')
                with self.assertRaisesRegex(ValueError, 'child'):
                    with S.child_import_boundary(here, pins):
                        self.fail('child process would have been allowed to start')
                path.unlink()
                if path.parent.name in ('__pycache__', 'package'):
                    path.parent.rmdir()

    def test_reject_changed_owned_project_closure(self):
        row = 'P2OriginalSaving19Geometry05ScalableShapeRows'
        log = (OLD / 'verification' / S.CONT / row / 'owned.log').read_text()
        other = 'ImbalancedChen.' + row
        with patch.object(S, 'MODULE', other), self.assertRaisesRegex(ValueError, 'project import closure'):
            S.log_facts(R, {'targets': [{'module': other, 'transitive_dependencies': []}]}, 'owned', log)


if __name__ == '__main__':
    unittest.main()
