"""Audit orchestration fixtures only; never Lean or cloud acceptance evidence."""
from pathlib import Path
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
HELPER = HERE / 'audit_batches.py'


class AuditBatchTests(unittest.TestCase):
    def setUp(self):
        self.assertTrue(HELPER.is_file(), 'frozen audit subset helper is not implemented')
        spec = importlib.util.spec_from_file_location('audit_batch_fixture', HELPER)
        self.code = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self.code)
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.helper = None
        self.names = ['ImbalancedChen.Fixture' + str(i) for i in range(9)]
        self.base = {
            'schema': 'p1_completed_normal_multibatch_audit_plan_v1',
            'source_review_head': '99c1f8ba1dc453b21f47e30b667db0de93d73387',
            'project': str(self.root / 'project'), 'receipt_root': '/unused/original',
            'runtime_states': ['/fixture/state0.json', '/fixture/state1.json'],
            'audit_template': {'path': '/fixture/template.lean', 'sha256': 'template'},
            'modules': {m: {'source_sha256': 'source-' + m, 'normal_log': 'shared-normal',
                            'project_closure': [m, 'ImbalancedChen.Shared']} for m in self.names},
            'normal_logs': {'shared-normal': {'path': '/fixture/complete-normal.log',
                'sha256': 'normal-log', 'source_commit': '99c1f8ba1dc453b21f47e30b667db0de93d73387',
                'expected_built_modules': self.names}},
            'expected_project_sources': {m: 'source-' + m for m in self.names + ['ImbalancedChen.Shared']},
            'lanes': [{'id': 0, 'modules': self.names}, {'id': 1, 'modules': []}],
            'excluded_prior13': [], 'reused_complete_modules': [],
            'higher_missing_normal_modules': ['ImbalancedChen.P2OriginalSixthHigherMomentsCore'],
            'higher_partition_normal_complete': False, 'whole_P1_complete': False,
        }

    def test_subset_keeps_complete_shared_normal_log_binding(self):
        selected = self.names[:8]
        plan = self.code.subset_plan(self.base, selected, self.root / 'receipt', 'parent-hash', [])
        self.assertEqual(plan['modules'], {m: self.base['modules'][m] for m in selected})
        self.assertEqual(plan['normal_logs'], self.base['normal_logs'])
        self.assertEqual(plan['normal_logs']['shared-normal']['expected_built_modules'], self.names)
        self.assertEqual(set(plan['expected_project_sources']), set(selected + ['ImbalancedChen.Shared']))
        self.assertEqual(plan['lanes'], [{'id': 0, 'modules': selected[:4]}, {'id': 1, 'modules': selected[4:]}])
        self.assertFalse(plan['whole_P1_complete'])

    def test_final_single_owner_has_no_empty_lane_execution_target(self):
        plan = self.code.subset_plan(self.base, self.names[-1:], self.root / 'receipt', 'parent-hash', self.names[:8])
        self.assertEqual(self.code.populated_lanes(plan), [0])
        self.assertEqual(plan['reused_complete_modules'], self.names[:8])

    def test_selected_owner_cannot_also_be_excluded_as_completed(self):
        with self.assertRaisesRegex(RuntimeError, 'overlap'):
            self.code.subset_plan(self.base, self.names[:2], self.root / 'receipt', 'parent-hash', self.names[:1])

    def test_partial_lane_blocks_implicit_resume(self):
        lane = self.root / 'lane-0'
        lane.mkdir()
        (lane / 'MODULES.json').write_text(json.dumps(self.names[:4]))
        self.assertEqual(self.code.lane_state(lane), 'UNSTARTED')
        (lane / 'BEFORE_KERNEL.json').write_text('{}')
        self.assertEqual(self.code.lane_state(lane), 'PARTIAL_REQUIRES_INSPECTION')

    def test_result_file_alone_is_not_accepted_as_a_valid_receipt(self):
        lane = self.root / 'receipt/lane-0'
        lane.mkdir(parents=True)
        result = lane / 'VALIDATION_RESULTS.json'
        result.write_text(json.dumps({'status': 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS'}))
        driver_spec = importlib.util.spec_from_file_location('normal_driver_fixture', HERE / 'resume_batch10.py')
        driver = importlib.util.module_from_spec(driver_spec)
        driver_spec.loader.exec_module(driver)
        with self.assertRaises((RuntimeError, FileNotFoundError, KeyError)):
            self.code.completed_owners(result, self.base, driver, self.helper)

    def test_frozen_subset_is_directly_preparable_by_unchanged_e9(self):
        ds = importlib.util.spec_from_file_location('prepare_driver_fixture', HERE / 'resume_batch10.py')
        driver = importlib.util.module_from_spec(ds)
        ds.loader.exec_module(driver)
        helper = driver.load_helper((HERE.parents[3] / driver.HELPER_PATH).read_bytes())
        self.base['audit_template'] = {'path': str(driver.AUDIT_TEMPLATE), 'sha256': driver.AUDIT_TEMPLATE_SHA}
        self.base['runtime_states'] = list(map(str, helper.STATES))
        parent = self.root / 'parent'
        parent.mkdir()
        parent_plan = parent / 'AUDIT_PLAN.json'
        parent_plan.write_text(json.dumps(self.base))
        runner_name = 'run_parallel_acceptance_multibatch.py'
        runner = HERE.parents[3] / 'docs/p1/20261124/normal-supplement-audit' / runner_name
        (parent / runner_name).write_bytes(runner.read_bytes())
        project = Path(self.base['project'])
        project.mkdir()
        out = self.root / 'subsets'
        prepare = subprocess.run([sys.executable, '-B', str(HELPER), '--prepare',
            '--plan', str(parent_plan), '--out', str(out), '--driver', str(HERE / 'resume_batch10.py'),
            '--source-repo', str(HERE.parents[3])],
            capture_output=True, text=True)
        self.assertEqual(prepare.returncode, 0, prepare.stdout + prepare.stderr)
        manifest = json.loads((out / 'MANIFEST.json').read_bytes())
        first = manifest['chunks'][0]['plan']
        result = subprocess.run([sys.executable, '-B', str(out / runner_name), '--plan', first, '--prepare-only'],
                                cwd=project, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('lane_sizes [4, 4]', result.stdout)
        self.assertEqual(len(manifest['chunks']), 2)

    def complete_fixture(self):
        ds = importlib.util.spec_from_file_location('driver_fixture', HERE / 'resume_batch10.py')
        driver = importlib.util.module_from_spec(ds)
        ds.loader.exec_module(driver)
        module = self.names[0]
        project = Path(self.base['project'])
        rel = module.replace('.', '/')
        paths = [rel + '.lean', '.lake/build/lib/lean/' + rel + '.olean',
                 '.lake/build/lib/lean/' + rel + '.ilean', '.lake/build/ir/' + rel + '.c',
                 '.lake/build/ir/' + rel + '.setup.json', '.lake/build/lib/lean/' + rel + '.trace']
        for path in paths:
            target = project / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text('fixture only ' + path)
        (project / paths[0]).write_text('import ImbalancedChen.Dependency\n-- fixture only\n')
        source_hash = driver.fingerprint(project / paths[0])['sha256']
        dep = 'ImbalancedChen.Dependency'
        dep_source = project / 'ImbalancedChen/Dependency.lean'
        dep_source.write_text('fixture dependency source')
        dep_object = project / '.lake/build/lib/lean/ImbalancedChen/Dependency.olean'
        dep_trace = dep_object.with_suffix('.trace')
        dep_object.write_text('fixture dependency object')
        dep_trace.write_text('fixture dependency trace')
        dep_hash = driver.fingerprint(dep_source)['sha256']
        runtime = [self.root / n for n in ['state0.json', 'state1.json', 'template.lean', 'guard.py', 'serializer.py']]
        for file in runtime:
            file.write_text('fixture only ' + file.name)
        self.helper = driver.load_helper((HERE.parents[3] / driver.HELPER_PATH).read_bytes())
        self.helper.STATES = runtime[:2]
        self.helper.GUARD, self.helper.SERIALIZER = str(runtime[3]), str(runtime[4])
        driver.AUDIT_TEMPLATE = runtime[2]
        driver.AUDIT_TEMPLATE_SHA = driver.fingerprint(runtime[2])['sha256']
        driver.GUARD_SHA = driver.fingerprint(runtime[3])['sha256']
        driver.SERIALIZER_SHA = driver.fingerprint(runtime[4])['sha256']
        self.base['runtime_states'] = list(map(str, runtime[:2]))
        self.base['audit_template'] = {'path': str(runtime[2]), 'sha256': driver.fingerprint(runtime[2])['sha256']}
        for name in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']:
            (project / name).write_text('fixture only ' + name)
        self.base['modules'][module]['source_sha256'] = source_hash
        self.base['modules'][module]['project_closure'] = [module, dep]
        self.base['expected_project_sources'][module] = source_hash
        self.base['expected_project_sources'][dep] = dep_hash
        normal = self.root / 'normal' / module / 'attempt-0' / 'normal.log'
        normal.parent.mkdir(parents=True)
        normal.write_text('\u2714 [1/1] Built ' + module + '\n')
        self.base['normal_logs']['shared-normal'].update(path=str(normal),
            sha256=driver.fingerprint(normal)['sha256'], expected_built_modules=[module])
        receipt = self.root / 'receipt'
        lane = receipt / 'lane-0'
        lane.mkdir(parents=True)
        plan = self.code.subset_plan(self.base, [module], receipt, 'parent', [])
        plan_path = receipt / 'AUDIT_PLAN.json'
        plan_path.write_text(json.dumps(plan))
        plan_sha = driver.fingerprint(plan_path)['sha256']
        (receipt / 'PLAN_BINDING.json').write_text(json.dumps({'runner_sha256': driver.RUNNER_SHA, 'sha256': plan_sha}))
        snapshots = {module: driver.snapshot(project, module)}
        normal_command = {'exit_code': 0, 'argv': self.helper.guard(0, ['lake', 'build', '+' + module + ':olean']),
            'cwd': str(project), 'log': str(normal), 'log_sha256': driver.fingerprint(normal)['sha256'],
            'actual_built_modules': [module]}
        command_path = normal.parent / 'normal-command.json'
        command_path.write_text(json.dumps(normal_command))
        context = {'source_commit': driver.SOURCE_COMMIT, 'project_sources': {module: source_hash, dep: dep_hash},
            'dependency_objects_and_traces': {str(p.relative_to(project)): driver.fingerprint(p) for p in [dep_object, dep_trace]},
            'configuration': {n: driver.fingerprint(project / n) for n in ['lean-toolchain', 'lake-manifest.json', 'lakefile.toml']},
            'existing_runtime': {str(p): driver.fingerprint(p) for p in runtime}}
        (normal.parent.parent / 'NORMAL_PASS.json').write_text(json.dumps({'module': module,
            'source_commit': driver.SOURCE_COMMIT, 'status': 'NORMAL_PASS_AUDIT_PENDING',
            'source_plus_five_outputs': snapshots[module], 'dependency_context': context,
            'normal_command': dict(normal_command, command_receipt=str(command_path),
                                   command_sha256=driver.fingerprint(command_path)['sha256'])}))
        (lane / 'BEFORE_KERNEL.json').write_text(json.dumps(snapshots))
        record = {'name': module + '.fixture', 'module': module, 'kind': 'theorem',
                  'is_private': False, 'axioms': [], 'type': 'True', 'type_expression': 'fixture only'}
        audit_text = ('MEMBER_OWNED_NAMES ' + json.dumps({'names': [record['name']]}) + '\n' +
                      'AUDIT_RECORD ' + json.dumps(record) + '\n')
        (lane / 'OWNED_EXPORTS.json').write_text(json.dumps([record]))
        guard = ['python3', '/workspace/blue-build-tools/run_guarded.py', '--state', self.base['runtime_states'][0]]
        def command(name, tail, raw):
            log = lane / (name + '.log')
            log.write_text(raw)
            return {'exit_code': 0, 'argv': guard + tail, 'cwd': str(project), 'log': log.name,
                    'log_sha256': driver.fingerprint(log)['sha256']}
        ready_tail = ['lake', '--no-build', 'build', '+' + module + ':olean']
        result = {'status': 'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS',
                  'plan_sha256': plan_sha, 'modules': {module: source_hash},
                  'source_plus_five_outputs': snapshots, 'project_dependency_sources': {module: source_hash, dep: dep_hash},
                  'runtime_state': str(runtime[0]), 'runtime_state_sha256': driver.fingerprint(runtime[0])['sha256'],
                  'audit_template_sha256': self.base['audit_template']['sha256'],
                  'kernel_commands': {module: command('kernel', ['lake', 'env', 'leanchecker', '--verbose', module], 'fixture kernel\n')},
                  'audit_command': command('audit', ['lake', 'env', 'lean', '-DmaxRecDepth=100000',
                      '-DmaxHeartbeats=4000000', '--root=' + str(lane), str(lane / 'PublicAudit.lean')], audit_text),
                  'stock_readiness_before': command('before', ready_tail, 'fixture readiness\n'),
                  'stock_readiness_after': command('after', ready_tail, 'fixture readiness\n'),
                  'total_owned_exports': 1, 'total_public_exports': 1,
                  'full_owned_including_private_generated': True, 'only_standard_axioms': True,
                  'pp_all_true_no_elisions': True,
                  'source_plus_five_outputs_unchanged_across_kernel_and_audit': True,
                  'successful_normal_not_repeated': True, 'whole_P1_complete': False}
        path = lane / 'VALIDATION_RESULTS.json'
        path.write_text(json.dumps(result))
        return driver, module, path, project / paths[1], dep_object, runtime

    def test_complete_receipt_reuse_requires_current_outputs_and_raw_logs(self):
        driver, module, path, output, _, _ = self.complete_fixture()
        self.assertEqual(self.code.completed_owners(path, self.base, driver, self.helper), {module})
        output.write_text('changed output fixture')
        with self.assertRaisesRegex(RuntimeError, 'output'):
            self.code.completed_owners(path, self.base, driver, self.helper)

    def test_changed_dependency_object_invalidates_completed_receipt(self):
        driver, _, path, _, dependency, _ = self.complete_fixture()
        dependency.write_text('changed dependency object fixture')
        with self.assertRaisesRegex(RuntimeError, 'receipt|dependency'):
            self.code.completed_owners(path, self.base, driver, self.helper)

    def test_changed_runtime_invalidates_completed_receipt(self):
        driver, _, path, _, _, runtime = self.complete_fixture()
        runtime[0].write_text('changed runtime fixture')
        with self.assertRaisesRegex(RuntimeError, 'receipt|runtime'):
            self.code.completed_owners(path, self.base, driver, self.helper)

    def test_receipt_template_must_match_frozen_parent(self):
        driver, _, path, _, _, _ = self.complete_fixture()
        plan_path = path.parent.parent / 'AUDIT_PLAN.json'
        plan = json.loads(plan_path.read_bytes())
        plan['audit_template']['path'] = '/unrelated/template.lean'
        plan_path.write_text(json.dumps(plan))
        result = json.loads(path.read_bytes())
        result['plan_sha256'] = driver.fingerprint(plan_path)['sha256']
        path.write_text(json.dumps(result))
        binding = path.parent.parent / 'PLAN_BINDING.json'
        binding.write_text(json.dumps({'sha256': result['plan_sha256'], 'runner_sha256': driver.RUNNER_SHA}))
        with self.assertRaisesRegex(RuntimeError, 'template|runtime'):
            self.code.completed_owners(path, self.base, driver, self.helper)

    def test_inspection_rejects_replaced_prepared_plan_even_with_consistent_result(self):
        driver, _, path, _, _, _ = self.complete_fixture()
        plan_path = path.parent.parent / 'AUDIT_PLAN.json'
        frozen = self.root / 'frozen.json'
        frozen.write_bytes(plan_path.read_bytes())
        manifest = {'reused_receipts': [], 'chunks': [{'name': 'chunk-000', 'plan': str(frozen),
                     'sha256': driver.fingerprint(frozen)['sha256']}]}
        plan = json.loads(plan_path.read_bytes())
        plan['unexpected_change'] = 'fixture'
        plan_path.write_text(json.dumps(plan))
        result = json.loads(path.read_bytes())
        result['plan_sha256'] = driver.fingerprint(plan_path)['sha256']
        path.write_text(json.dumps(result))
        (path.parent.parent / 'PLAN_BINDING.json').write_text(json.dumps({
            'sha256': result['plan_sha256'], 'runner_sha256': driver.RUNNER_SHA}))
        with self.assertRaisesRegex(RuntimeError, 'plan'):
            self.code.inspect(manifest, self.base, driver, self.helper)

    def test_pending_owner_revalidates_full_normal_context_before_audit(self):
        driver, module, _, _, dependency, _ = self.complete_fixture()
        dependency.write_text('changed dependency object fixture')
        self.assertTrue(hasattr(self.code, 'validate_normal_owner'), 'pending normal provenance check missing')
        with self.assertRaisesRegex(RuntimeError, 'receipt|dependency'):
            self.code.validate_normal_owner(module, self.base, driver, self.helper)

    def test_parent_template_and_runtime_are_pinned_before_all_modes(self):
        driver, _, _, _, _, _ = self.complete_fixture()
        self.assertTrue(hasattr(self.code, 'validate_parent_bindings'), 'pinned parent metadata check missing')
        self.code.validate_parent_bindings(self.base, driver, self.helper)
        for field, value in [('audit_template', {'path': '/different/template.lean', 'sha256': driver.AUDIT_TEMPLATE_SHA}),
                             ('audit_template', {'path': str(driver.AUDIT_TEMPLATE), 'sha256': 'different'}),
                             ('runtime_states', ['/different/state0.json', '/different/state1.json'])]:
            with self.subTest(field=field, value=value):
                changed = dict(self.base, **{field: value})
                with self.assertRaisesRegex(RuntimeError, 'parent.*template|parent.*runtime'):
                    self.code.validate_parent_bindings(changed, driver, self.helper)

    def test_subset_preserves_parent_normal_coverage_and_labels_audit_scope_separately(self):
        self.base['higher_partition_normal_complete'] = True
        self.base['higher_missing_normal_modules'] = []
        higher = 'ImbalancedChen.P2OriginalSixthHigherMomentsCore'
        self.base['modules'][higher] = dict(self.base['modules'][self.names[0]])
        plan = self.code.subset_plan(self.base, self.names[:1], self.root / 'receipt', 'parent', [])
        self.assertTrue(plan['higher_partition_normal_complete'])
        self.assertEqual(plan['higher_missing_normal_modules'], [])
        self.assertEqual(plan['higher_audit_subset_missing'], [higher])


if __name__ == '__main__':
    unittest.main(verbosity=2)
