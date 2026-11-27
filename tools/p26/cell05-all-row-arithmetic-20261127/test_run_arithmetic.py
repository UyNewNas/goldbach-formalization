"""Local boundary tests. Real immutable metadata/helpers; no Lean or cloud calls."""
import importlib.util
import io
import json
from contextlib import redirect_stdout
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
MATERIALS = HERE.parents[3]
PURE = MATERIALS / 'recovery-20261127/cell05-all-row-arithmetic/fastdet'
SHAPE = HERE.parent / 'cell05-shape-completion-20261127'
spec = importlib.util.spec_from_file_location('accepted_shape_reference', SHAPE / 'complete_shape.py')
S = importlib.util.module_from_spec(spec)
spec.loader.exec_module(S)
OLD = MATERIALS / 'recovery-20261127/remaining9-v2-exact/stage'
R, V, E = S.bootstrap(OLD, OLD / S.OLD_TOOL.relative_to(S.OLD), json.loads((SHAPE / 'PINS.json').read_text()))
SHAPE_CONTEXT = json.loads((MATERIALS / 'recovery-20261127/shape-completion-v1/exact/verification/RUN.json').read_text())
G = None
if (HERE / 'run_arithmetic.py').exists():
    spec = importlib.util.spec_from_file_location('new_gap_runner', HERE / 'run_arithmetic.py')
    G = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(G)
MODULE = 'ImbalancedChen.P2OriginalSaving19Cell05AllRowArithmetic'
SOURCE = HERE.parents[2] / 'ImbalancedChen/P2OriginalSaving19Cell05AllRowArithmetic.lean'
AUDIT = HERE / 'owned-audits/P2OriginalSaving19Cell05AllRowArithmetic.lean'


class PureJoin(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(G, 'New strict runner is not implemented')
        tmp = TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name) / 'pure2'
        shutil.copytree(PURE, self.root)
        self.pin = R.fp(self.root / 'TRANSPORT.json')

    def test_actual_two_fastdet_modes_accept_without_added_owned_requirement(self):
        value = G.validate_fastdet(R, self.root, self.pin, SHAPE_CONTEXT)
        self.assertEqual(set(value['dependencies']), {
            'ImbalancedChen.P2Winner9FastDetPure'})
        self.assertEqual(value['accepted_old_normal_kernel_records'], 2)
        self.assertEqual(value['new_supplier_owned_audits'], 0)
        self.assertFalse(value['historical_loaded_inventory_claimed'])

    def test_altered_original_log_rejected_before_reuse(self):
        p = next(self.root.rglob('normal-namespace-v2.log'))
        p.write_bytes(p.read_bytes() + b'warning: changed\n')
        with self.assertRaises(ValueError):
            G.validate_fastdet(R, self.root, self.pin, SHAPE_CONTEXT)

    def test_wrong_current_object_rejected_before_reuse(self):
        p = self.root / 'objects/ImbalancedChen/P2Winner9FastDetPure.olean'
        p.write_bytes(b'wrong same-name object')
        with self.assertRaises(ValueError):
            G.validate_fastdet(R, self.root, self.pin, SHAPE_CONTEXT)

    def test_wrong_runtime_identity_rejected(self):
        ctx = json.loads(json.dumps(SHAPE_CONTEXT))
        ctx['runtime']['lean_binary']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            G.validate_fastdet(R, self.root, self.pin, ctx)


class NewOwnerBoundary(unittest.TestCase):
    def setUp(self):
        self.assertIsNotNone(G, 'New strict runner is not implemented')
        tmp = TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        stage = Path(tmp.name)
        source = stage / 'project/ImbalancedChen/P2OriginalSaving19Cell05AllRowArithmetic.lean'
        source.parent.mkdir(parents=True)
        source.write_bytes(SOURCE.read_bytes())
        audit = stage / 'owned-audit.lean'
        audit.write_bytes(AUDIT.read_bytes())
        (stage / 'verification').mkdir()
        (stage / 'objects/ImbalancedChen').mkdir(parents=True)
        self.ctx = {'schema': 'cell05_all_row_arithmetic_run_v1', 'stage': str(stage),
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
        self.assertEqual(c['argv'][-1], 'ImbalancedChen/P2OriginalSaving19Cell05AllRowArithmetic.lean')
        self.runner.object.write_bytes(b'object')
        self.assertEqual(self.runner.command_fields('kernel', {'fixture': True})['argv'],
                         ['/pinned/leanchecker', '--verbose', MODULE])
        self.assertIn('--trust=0', self.runner.command_fields('owned', {'fixture': True})['argv'])

    def test_private_prints_and_generated_owned_declarations_are_included(self):
        facts = self.runner.log_facts('normal', self.normal_log())
        self.assertEqual(len(facts['printed_declarations']), 15)
        owned = self.runner.log_facts('owned', self.owned_log())['owned']
        self.assertEqual(owned['owned_declaration_count'], 16)
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
        self.ctx.update(gaps_stage=str(predecessor), gaps_run=R.fp(predecessor / 'RUN.json'),
                        gaps_success=R.fp(predecessor / 'SUCCESS.json'),
                        fastdet_reuse=R.fp(self.runner.stage / 'SUPPLIER_REUSE.json'),
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
        self.assertEqual(R.read(self.runner.receipts / 'owned-declarations.json')['owned_declaration_count'], 16)


class PredecessorBoundary(unittest.TestCase):
    def setUp(self):
        temp = TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.tool = self.root / G.GAPS_TOOL_REL
        self.tool.mkdir(parents=True)
        (self.tool/'owned-audits').mkdir()
        bodies = {'run_gaps.py': 'raise AssertionError("fixture predecessor must never execute")',
                  'CONFIG.json': '{"schema":"p26_cell05_all_row_gaps_config_v1"}',
                  'owned-audits/P2OriginalSaving19Cell05AllRowGaps.lean': 'fixture audit',
                  'test_run_gaps.py': '# pinned additional Python'}
        for n,s in bodies.items():
            (self.tool/n).write_text(s)
        self.manifest = {'schema':'p26_cell05_all_row_gaps_workflow_v1',
                         'files':[{'relative_path':n, **R.fp(self.tool/n)} for n in bodies]}
        self.pins = {'driver':R.fp(self.tool/'run_gaps.py'),'configuration':R.fp(self.tool/'CONFIG.json')}

    def test_all_predecessor_workflow_sources_checked_before_execution(self):
        G.checked_gaps_manifest(self.tool,self.manifest,self.pins)
        (self.tool/'test_run_gaps.py').write_text('raise Exception()')
        with self.assertRaisesRegex(ValueError,'Pinned file changed'):
            G.checked_gaps_manifest(self.tool,self.manifest,self.pins)

    def test_unpinned_pyc_and_source_blocked(self):
        for n in ('other.py','other.pyc'):
            with self.subTest(n=n):
                p = self.tool/n
                p.write_bytes(b'not reviewed')
                with self.assertRaisesRegex(ValueError,'Unpinned Gaps executable'):
                    G.checked_gaps_manifest(self.tool,self.manifest,self.pins)
                p.unlink()

    def test_historical_entry_invokes_only_retained_verify_and_checks_all_code(self):
        driver = self.tool/'run_gaps.py'
        driver.write_text('import sys\ndef main():\n    print(sys.argv[1:])\n')
        config_path = self.tool/'CONFIG.json'
        config_path.write_text(json.dumps({'schema':'p26_cell05_all_row_gaps_config_v1','stage':str(self.root)}))
        self.manifest['files'] = [{'relative_path':r['relative_path'],**R.fp(self.tool/r['relative_path'])}
                                  for r in self.manifest['files']]
        (self.tool/'WORKFLOW_MANIFEST.json').write_text(json.dumps(self.manifest))
        with patch.object(G,'GAPS_STAGE',self.root):
            paths = G.gaps_paths()
            for p in paths.values():
                if not p.exists():
                    p.parent.mkdir(parents=True,exist_ok=True)
                    p.write_text('fixture')
            pins = {k:R.fp(p) for k,p in paths.items()}
            config = {'gaps':dict(pins,stage=str(self.root))}
            with patch.object(sys,'argv',list(sys.argv)), redirect_stdout(io.StringIO()) as buffer:
                try:
                    G.historical_worker(config)
                finally:
                    sys.modules.pop('accepted_gaps_readonly_driver',None)
            self.assertEqual(buffer.getvalue().strip(),str(['verify','--workflow-sha256',pins['workflow']['sha256']]))
            (self.tool/'test_run_gaps.py').write_text('# altered')
            with patch.object(G,'load_source',side_effect=AssertionError('unverified code invoked')):
                with self.assertRaisesRegex(ValueError,'Pinned file changed'):
                    G.historical_worker(config)

    def test_wrong_driver_binding_and_object_refused(self):
        wrong = dict(self.pins,driver=self.pins['configuration'])
        with self.assertRaisesRegex(ValueError,'binding differs'):
            G.checked_gaps_manifest(self.tool,self.manifest,wrong)
        obj = self.root/'gaps.olean'
        obj.write_bytes(b'fixture object')
        pin = R.fp(obj)
        run_pin = {'path':'/fiction/RUN.json','bytes':3,'sha256':'1'*64}
        config = {'gaps':{'stage':str(self.root),'workflow':{'sha256':'a'*64},'run':run_pin,'object':pin}}
        old = {'schema':'cell05_all_row_gaps_run_v1','stage':str(self.root),'workflow_sha256':'a'*64,
               'targets':[{'module':G.GAPS_MODULE,'source':pin}],
               'dependencies':{str(i):{'installed_source':pin,'installed_object':pin} for i in range(128)}}
        success = {'schema':'cell05_all_row_gaps_success_v1','status':'succeeded','accepted_targets':1,'accepted_steps':3,
                   'old_supplier_count':128,'project_closure_count':129,'old_proof_commands':0,'P2_6_complete':False,
                   'records':[{'module':G.GAPS_MODULE,'mode':m} for m in G.MODES],'run':run_pin,'object':pin}
        extra = {'dependencies':{G.FASTDET:{'source':pin,'object':pin}}}
        self.assertEqual(len(G.derive_dependencies(R,old,success,extra,config)),130)
        obj.write_bytes(b'changed object')
        with self.assertRaisesRegex(ValueError,'object or ordered chain'):
            G.derive_dependencies(R,old,success,extra,config)

    def test_reject_missing_retained_report_without_producing_config(self):
        report = self.root / 'not-retained.json'
        report.write_text('{"status":"STOPPED"}')
        archive = self.root/'no-evidence'
        archive.write_bytes(b'not an archive')
        result = subprocess.run([sys.executable,'-I','-S','-B',str(HERE/'bind_config.py'),
                   '--gaps-archive',str(archive),'--retained-report',str(report),'--retained-sha256',R.fp(report)['sha256'],
                   '--gaps-workflow-sha256','a'*64,'--package-dir',str(self.root)],capture_output=True)
        self.assertNotEqual(result.returncode,0)
        self.assertFalse((self.root/'CONFIG.json').exists())
        self.assertFalse((self.root/'WORKFLOW_MANIFEST.json').exists())

    def test_bind_only_consistent_verified_artifact_chain(self):
        spec = importlib.util.spec_from_file_location('arithmetic_binding_fixture', HERE/'bind_config.py')
        B = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(B)
        payload = {p.relative_to(self.root).as_posix():p.read_bytes()
                   for p in self.tool.rglob('*') if p.is_file()}
        data = B.output_bytes
        manifest = {'schema':'p26_cell05_all_row_gaps_workflow_v1',
                    'files':[{'relative_path':r['relative_path'],'bytes':r['bytes'],'sha256':r['sha256']}
                             for r in self.manifest['files']]}
        workflow = data(manifest)
        workflow_sha = B.identity(workflow)['sha256']
        payload[B.TOOL+'/WORKFLOW_MANIFEST.json'] = workflow
        run = {'stage':B.GAPS,'schema':'cell05_all_row_gaps_run_v1','workflow_sha256':workflow_sha,
               'dependencies':{str(i):{} for i in range(128)},'targets':[{'module':G.GAPS_MODULE}]}
        payload['verification/RUN.json'] = data(run)
        object_name = 'objects/'+G.GAPS_MODULE.replace('.','/')+'.olean'
        payload[object_name] = b'fixture-only-object'
        def pin(n):
            return {'path':B.GAPS+'/'+n,**B.identity(payload[n])}
        success = {'schema':'cell05_all_row_gaps_success_v1','status':'succeeded','run':pin('verification/RUN.json'),
                   'accepted_targets':1,'accepted_steps':3,'old_supplier_count':128,'project_closure_count':129,
                   'P2_6_complete':False,'old_proof_commands':0,'object':pin(object_name),
                   'records':[{'module':G.GAPS_MODULE,'mode':m} for m in G.MODES]}
        payload['verification/SUCCESS.json'] = data(success)
        payload['REUSE_INDEX.json'] = data({'fixture':True})
        def bind():
            stream = io.BytesIO()
            with tarfile.open(fileobj=stream,mode='w:xz') as tar:
                for n,body in payload.items():
                    ti = tarfile.TarInfo(n)
                    ti.size = len(body)
                    tar.addfile(ti, io.BytesIO(body))
            archive = stream.getvalue()
            report = data({'status':'RETAINED_EVIDENCE_VERIFIED','old_proof_commands':0,'accepted_targets':1,
                           'accepted_steps':3,'P2_6_complete':False,'archive':{'path':B.GAPS+'/exports/gaps-evidence.tar.xz',
                           **B.identity(archive)},'success':pin('verification/SUCCESS.json'),'reuse_index':pin('REUSE_INDEX.json')})
            return B.configuration(archive, report, B.identity(report)['sha256'], workflow_sha)
        self.assertEqual(bind()['gaps']['object'], pin(object_name))
        payload[object_name] = b'other-same-name-object'
        with self.assertRaisesRegex(ValueError,'object binding'):
            bind()


if __name__ == '__main__':
    unittest.main()


