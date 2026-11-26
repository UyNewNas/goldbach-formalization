from pathlib import Path
from types import ModuleType, SimpleNamespace as NS
from unittest.mock import patch
import copy, hashlib, json, os, subprocess, tempfile, unittest

BASE = Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
LOCAL = Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
SCRIPT = LOCAL / 'apply_allk_repair.py'

def module(raw, name, filename=None):
    m = ModuleType(name)
    m.__file__ = str(filename or name)
    exec(compile(raw, m.__file__, 'exec'), m.__dict__)
    return m

def original(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=BASE)

WRAPPER = SCRIPT.read_bytes()
probe = module(WRAPPER, 'allk_tests_pins', SCRIPT)
DRIVER = original(probe.O, probe.DRIVER)
assert probe.raw_fp(DRIVER) == probe.DRIVER_FP
_api = module(DRIVER, 'old_driver').helpers.__globals__
API = (BASE/_api['API']).read_bytes()
assert hashlib.sha256(API).hexdigest() == _api['API_SHA']
api_meta = module(API, 'old_api')
HELPERS = {k: (BASE/k).read_bytes() for k in api_meta.PINS}
assert all(hashlib.sha256(raw).hexdigest() == api_meta.PINS[k] for k,raw in HELPERS.items())

class Tests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='p15-allk-updater-', dir='/tmp')
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        m = self.m = module(WRAPPER, 'allk_test', SCRIPT)
        m.ROOT, m.PROJECT, m.OLD_ROOT = root/'archive', root/'project', root/'original-O'
        d = module(HELPERS[api_meta.PRIMITIVES], 'real_primitives')
        h = module(HELPERS[api_meta.HELPER], 'real_installer')
        api = module(API, 'real_reader')
        driver = module(DRIVER, 'real_driver')
        driver.PROJECT = m.PROJECT
        c = self.c = NS(commit='a'*40, s=NS(d=d, h=h, api=api), driver=driver)
        c.identity = {'execution_commit':c.commit, 'script':{'path':m.SCRIPT, **m.raw_fp(WRAPPER)},
            'source_repair_commit':m.P, 'published_evidence':m.PINS, 'failed_source_commit':m.O,
            'failed_job':m.OLD_JOB, 'module':m.TARGET, 'source_path':m.SOURCE,
            'source_before':m.BEFORE, 'source_after':m.AFTER}
        self.payload = b'exact failed AllK setup fixture\n'
        m.SETUP_FP = m.raw_fp(self.payload)
        c.identity['failed_setup'] = {'path':m.SETUP, **m.SETUP_FP}
        self.active = m.PROJECT/m.SETUP
        self.active.parent.mkdir(parents=True)
        self.active.write_bytes(self.payload)
        self.run = m.ROOT/c.commit/'runs/attempt-00000'
        self.run.mkdir(parents=True)
        self.state = NS(artifacts=m.artifact_inventory(c,[m.TARGET]), archives={})
        self.receipt = self.run/'FAILED_SETUP_ARCHIVE.json'
        self.archive = self.run/'failed-artifacts'/m.ARCHIVE_NAME

    def archive_once(self):
        return self.m.preserve_failed_setup(self.c,self.state,self.run)

    def test_real_pins_and_splices(self):
        m = self.m
        for key in ('REPAIR','METADATA','PROBE','PUBLIC'):
            path = getattr(m,key)
            self.assertEqual(m.raw_fp((LOCAL/Path(path).name).read_bytes()),m.PINS[path])
        before = original(m.O,m.SOURCE)
        after = (LOCAL/Path(m.SOURCE).name).read_bytes()
        self.assertEqual(m.raw_fp(before),m.BEFORE)
        self.assertEqual(m.raw_fp(after),m.AFTER)
        repair=json.loads((LOCAL/'REPAIR_CANDIDATE.json').read_bytes())
        out,end=[],0
        for s in repair['splices']:
            a,b=s['original_byte_start'],s['original_byte_end']
            self.assertEqual(before[a:b],s['before_utf8'].encode())
            out.extend([before[end:a],s['after_utf8'].encode()]);end=b
        self.assertEqual(b''.join(out)+before[end:],after)
        self.assertEqual(self.c.s.h.imports(before),self.c.s.h.imports(after))

    def test_archive_and_resume_same_identity(self):
        r=self.archive_once()
        self.assertEqual(r['action'],'EXACT_FAILED_SETUP_ARCHIVED_AND_REMOVED')
        self.assertEqual(self.archive.read_bytes(),self.payload)
        self.assertFalse(self.active.exists())
        self.state.artifacts=self.m.artifact_inventory(self.c,[self.m.TARGET])
        self.state.archives=self.m.prior_archive(self.c)
        self.assertEqual(r['bindings'],self.state.archives)
        second=self.m.ROOT/self.c.commit/'runs/attempt-00001'
        second.mkdir()
        resumed=self.m.preserve_failed_setup(self.c,self.state,second)
        self.assertEqual(resumed['action'],'ALREADY_ARCHIVED_AND_ABSENT')
        self.assertEqual(list(second.iterdir()),[])

    def test_absence_without_receipt_rejected(self):
        self.active.unlink()
        with self.assertRaises(RuntimeError): self.m.prior_archive(self.c)

    def test_each_identity_component_rejected(self):
        self.archive_once()
        value=json.loads(self.receipt.read_bytes())
        for key in ('execution_commit','source_repair_commit','failed_source_commit','module','source_path'):
            with self.subTest(key=key):
                changed=copy.deepcopy(value);changed['identity'][key]='wrong'
                self.receipt.write_text(json.dumps(changed))
                with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)
        for key in ('script','source_before','source_after','published_evidence','failed_setup'):
            with self.subTest(key=key):
                changed=copy.deepcopy(value);changed['identity'][key]={}
                self.receipt.write_text(json.dumps(changed))
                with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)
        self.receipt.write_text(json.dumps(value))
        self.m.prior_archive(self.c)

    def test_old_licensed_basename_rejected(self):
        self.archive_once()
        value=json.loads(self.receipt.read_bytes())
        value['archive_path']=str(self.archive.with_name('P5LicensedOriginalIntegerProfile.setup.json'))
        self.receipt.write_text(json.dumps(value))
        with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)

    def test_tampered_archive_rejected(self):
        self.archive_once();self.archive.write_bytes(b'wrong')
        with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)

    def test_archive_symlink_rejected(self):
        self.archive_once();self.archive.unlink()
        substitute=self.archive.parent/'substitute';substitute.write_bytes(self.payload)
        self.archive.symlink_to(substitute)
        with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)

    def test_setup_change_between_archive_and_unlink_rejected(self):
        original_binding=self.m.archive_binding
        def changed(c,path):
            result=original_binding(c,path)
            self.active.write_bytes(self.payload+b'racing writer')
            return result
        with patch.object(self.m,'archive_binding',changed):
            with self.assertRaises(RuntimeError):self.archive_once()
        self.assertTrue(self.active.exists())
        self.assertEqual(self.archive.read_bytes(),self.payload)

    def test_interruption_after_unlink_can_resume(self):
        sync=self.m.fsync_directory
        def interrupted(path):
            if path==self.active.parent:raise OSError('simulated interruption after unlink')
            sync(path)
        with patch.object(self.m,'fsync_directory',interrupted):
            with self.assertRaises(OSError):self.archive_once()
        self.assertFalse(self.active.exists())
        self.state.artifacts=self.m.artifact_inventory(self.c,[self.m.TARGET])
        self.state.archives=self.m.prior_archive(self.c)
        self.assertEqual(self.m.preserve_failed_setup(self.c,self.state,self.run)['action'],'ALREADY_ARCHIVED_AND_ABSENT')

    def test_archive_and_receipt_fsynced_before_unlink(self):
        synced=[];sync=os.fsync;unlink=Path.unlink
        def track_sync(fd):
            synced.append(os.readlink('/proc/self/fd/'+str(fd)));sync(fd)
        def track_unlink(path,*a,**kw):
            if path==self.active:
                self.assertIn(str(self.archive),synced)
                self.assertIn(str(self.receipt),synced)
                self.assertIn(str(self.run),synced)
                self.assertIn(str(self.m.ROOT),synced)
                self.assertEqual(self.archive.read_bytes(),self.payload)
            return unlink(path,*a,**kw)
        with patch.object(os,'fsync',track_sync), patch.object(Path,'unlink',track_unlink):
            self.archive_once()

    def test_original_installer_exact_single_write(self):
        m,c=self.m,self.c
        source=m.PROJECT/m.SOURCE;source.parent.mkdir(parents=True,exist_ok=True)
        before=original(m.O,m.SOURCE);after=(LOCAL/Path(m.SOURCE).name).read_bytes()
        source.write_bytes(before)
        other=source.parent/'Unrelated.lean';other.write_bytes(b'preserved other source\n')
        artifact_before=m.artifact_inventory(c,[m.TARGET])
        updates=[{'module':m.TARGET,'path':m.SOURCE,'before_sha256':m.BEFORE['sha256'],
                  'after_sha256':m.AFTER['sha256'],'cloud_source_mutation_required':True}]
        rows=c.s.h.install_sources(m.PROJECT,updates,{m.SOURCE:after},self.run/'backups')
        self.assertEqual([r['module'] for r in rows],[m.TARGET]);self.assertTrue(rows[0]['mutated'])
        self.assertEqual(source.read_bytes(),after)
        self.assertEqual((self.run/'backups'/m.SOURCE).read_bytes(),before)
        self.assertEqual(other.read_bytes(),b'preserved other source\n')
        self.assertEqual(m.artifact_inventory(c,[m.TARGET]),artifact_before)

    def test_preservation_rejects_unrelated_changes(self):
        m,c=self.m,self.c
        other='ImbalancedChen.Unrelated'
        source=m.PROJECT/m.SOURCE;source.parent.mkdir(parents=True,exist_ok=True)
        source.write_bytes(original(m.O,m.SOURCE))
        other_path=m.PROJECT/c.s.h.module_path(other);other_path.write_bytes(b'other source\n')
        oldbase=m.OLD_ROOT/m.O;oldbase.mkdir(parents=True);evidence=oldbase/'frozen.json';evidence.write_bytes(b'evidence')
        c.driver.snapshot=lambda *a:{'original':'snapshot'}
        c.driver.acceptance_binding=lambda *a:{'original':'acceptance'}
        c.s.d.original_git_state=lambda *a:{'head':'fixed','status_hex':'fixed'}
        st=NS(prior_spec=NS(graph={m.TARGET:[],other:[]},baseline={'original':'snapshot'}),watch={m.TARGET,other},
              accepted={'original':'acceptance'},retained={str(evidence):m.file_fp(c,evidence)},
              git=c.s.d.original_git_state(None),evidence=m.tree_inventory(c,oldbase))
        st.sources=m.source_inventory(c,st.prior_spec.graph);st.artifacts=m.artifact_inventory(c,st.watch)
        m.unchanged(c,st)
        cases=[(other_path,b'modified source'),(evidence,b'modified evidence'),
               (oldbase/'added.txt',b'added evidence'),
               (m.PROJECT/('.lake/build/lib/lean/'+other.replace('.','/')+'.olean'),b'new artifact')]
        for path,value in cases:
            with self.subTest(path=path.name):
                existed=path.exists();old=path.read_bytes() if existed else None
                path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(value)
                with self.assertRaises(RuntimeError):m.unchanged(c,st)
                if existed:path.write_bytes(old)
                else:path.unlink()
                m.unchanged(c,st)
        c.s.d.original_git_state=lambda *a:{'head':'changed','status_hex':'fixed'}
        with self.assertRaises(RuntimeError):m.unchanged(c,st)

    def test_O_remaining_supplier_scope(self):
        result=json.loads((LOCAL/'OLD_O_RESULT_CAPTURE.json').read_bytes())
        manifest=json.loads(original(self.m.O,self.m.MANIFEST))
        graph={m:r['imports'] for m,r in manifest['project_sources'].items()}
        old=self.c.s.h.closure(graph,result['targets'])
        remaining=self.c.s.h.closure(graph,self.m.REMAINING)
        self.assertEqual(old,remaining);self.assertEqual(len(old),157)
        suppliers=remaining & set(manifest['accepted_suppliers'])
        prior=remaining & set(manifest['previously_accepted_targets'])
        self.assertEqual((len(suppliers),len(prior)),(13,4))
        self.assertEqual(suppliers|prior,set(result['original_supplier_acceptance_bindings']))
        self.assertNotIn(self.m.PRIOR,result['original_supplier_acceptance_bindings'])
        self.assertEqual(self.c.s.d.compile_order([],self.m.REMAINING,graph),self.m.REMAINING)

    def test_failed_actual_O_preflight_stops_before_install(self):
        m,c=self.m,self.c
        source=m.PROJECT/m.SOURCE;source.parent.mkdir(parents=True,exist_ok=True)
        before=original(m.O,m.SOURCE);source.write_bytes(before)
        events=[]
        c.s.d.verify_lane=lambda h: events.append('lane')
        self.state.sources={m.TARGET:m.BEFORE};self.state.evidence={};self.state.retained={}
        self.state.accepted={};self.state.prior_spec=NS(baseline={})
        self.state.original_context={};self.state.git={}
        def failed_preflight(s,commit,selected):
            events.append('O13-preflight')
            self.assertEqual(commit,m.O);self.assertEqual(selected,m.REMAINING)
            self.assertFalse(self.active.exists())
            self.assertEqual(self.archive.read_bytes(),self.payload)
            self.assertEqual(source.read_bytes(),before)
            raise RuntimeError('simulated original preflight HOLD')
        with patch.object(m,'prepare',lambda _:self.state), \
             patch.object(m,'unchanged',lambda *a,**k:events.append('preservation-check')), \
             patch.object(c.driver,'preflight',failed_preflight), \
             patch.object(c.s.h,'install_sources') as installer:
            with self.assertRaises(RuntimeError):m.apply_repair(c,self.run)
            installer.assert_not_called()
        self.assertEqual(events,['lane','preservation-check','preservation-check','O13-preflight'])
        self.assertEqual(source.read_bytes(),before)
        self.m.prior_archive(self.c)

    def test_already_after_source_is_rejected_by_original_evidence_gate(self):
        m,c=self.m,self.c
        c.published={getattr(m,key):json.loads((LOCAL/Path(getattr(m,key)).name).read_bytes())
                     for key in ('REPAIR','METADATA','PROBE','PUBLIC')}
        metadata=c.published[m.METADATA]
        actual_base='/workspace/p1-complete-proof/20261126-p15-current-corrections-v1/'+m.O
        original_metadata=json.loads((LOCAL/'ACTUAL_O_METADATA.json').read_bytes())
        for row in metadata['records']:
            path=row['binding']['path']
            path=path.replace(actual_base,str(m.OLD_ROOT/m.O)).replace('/workspace/blue-member-build',str(m.PROJECT))
            row['binding']['path']=path
        bindings={r['binding']['path']:m.pin(r['binding']) for r in metadata['records']}
        m.SETUP_FP=bindings[str(m.PROJECT/m.SETUP)]
        capture=json.loads((LOCAL/'OLD_O_RESULT_CAPTURE.json').read_bytes())
        result={k:v for k,v in capture.items() if k not in ('batch6','path')}
        keys=next(r['keys'] for r in original_metadata['records'] if r['binding']['path'].endswith('/WORKER_RESULT.json'))
        worker={k:result[k] for k in keys}
        source=m.PROJECT/m.SOURCE;source.parent.mkdir(parents=True,exist_ok=True)
        source.write_bytes((LOCAL/Path(m.SOURCE).name).read_bytes())
        def fingerprint(_,path):
            if Path(path)==source:return m.raw_fp(source.read_bytes())
            if Path(path).name=='executed-driver.py':return m.DRIVER_FP
            return bindings[str(path)]
        def read(path):
            return {'RESULT.json':result,'WORKER_RESULT.json':worker,'CONTEXT_BEFORE.json':{}}[Path(path).name]
        with patch.object(m,'file_fp',fingerprint),patch.object(c.s.api,'read_json',read):
            with self.assertRaisesRegex(RuntimeError,'actual original evidence differs:.*Part3AllKLambdaChartCorrection.lean'):
                m.read_original_evidence(c)

if __name__=='__main__':
    unittest.main(verbosity=2)
