from pathlib import Path
from types import ModuleType, SimpleNamespace as NS
from unittest.mock import patch
import copy, hashlib, json, os, tempfile, unittest

LOCAL=Path('/workspace/scratch/08f9f00c627a/p15-resume-20261126')
BASE=Path('/workspace/scratch/76f3bdb16a38/goldbach-p15')
PUBLIC=Path('/tmp/p15-r-publication')
SCRIPT=LOCAL/'apply_family_repair.py'

def load(path,name):
    m=ModuleType(name);m.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),'exec'),m.__dict__)
    return m

class Tests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='family-updater-',dir='/tmp');self.addCleanup(self.tmp.cleanup)
        root=Path(self.tmp.name)
        m=self.m=load(SCRIPT,'family_updater')
        m.ROOT,m.PROJECT,m.OLD_ROOT=root/'new-evidence',root/'project',root/'old-evidence'
        d=load(BASE/'docs/p1/20261125/batch10-resume/resume_batch10.py','pinned_d')
        api=load(BASE/'docs/p1/20261125/batch13-repairs/run_repairs.py','pinned_api')
        h=load(BASE/api.HELPER,'pinned_h')
        driver=load(LOCAL/'entrypoint/run_selected.py','original_Q')
        assert m.raw_fp((LOCAL/'entrypoint/run_selected.py').read_bytes())==m.DRIVER_FP
        assert hashlib.sha256((BASE/'docs/p1/20261125/batch13-repairs/run_repairs.py').read_bytes()).hexdigest()==driver.API_SHA
        for p in (api.HELPER,api.PRIMITIVES):assert hashlib.sha256((BASE/p).read_bytes()).hexdigest()==api.PINS[p]
        driver.PROJECT=m.PROJECT
        c=self.c=NS(commit='b'*40,s=NS(d=d,api=api,h=h),driver=driver)
        c.before=(BASE/m.SOURCE).read_bytes();c.after=(LOCAL/Path(m.SOURCE).name).read_bytes()
        self.payload=b'exact Family setup fixture\n';m.SETUP_FP=m.raw_fp(self.payload)
        c.identity={'execution_commit':c.commit,'script':{'path':m.SCRIPT,**m.raw_fp(SCRIPT.read_bytes())},
                    'repair_source_commit':m.R,'failed_source_commit':m.Q,'failed_job':m.FAILED_JOB,
                    'module':m.TARGET,'source_path':m.SOURCE,'source_before':m.BEFORE,'source_after':m.AFTER,
                    'failed_setup':{'path':m.SETUP,**m.SETUP_FP},'published_R_inputs':m.PINS}
        self.active=m.PROJECT/m.SETUP;self.active.parent.mkdir(parents=True);self.active.write_bytes(self.payload)
        self.source=m.PROJECT/m.SOURCE;self.source.parent.mkdir(parents=True,exist_ok=True);self.source.write_bytes(c.before)
        self.run=m.ROOT/c.commit/'runs/attempt-00000';self.run.mkdir(parents=True)
        self.state=NS(artifacts=m.artifact_inventory(c,[m.TARGET]),archives={})
        self.receipt=self.run/'FAILED_SETUP_ARCHIVE.json';self.archive=self.run/'failed-artifacts'/m.ARCHIVE_NAME
    def archive_once(self):return self.m.archive_setup(self.c,self.state,self.run)
    def test_real_R_pins_six_splices_and_imports(self):
        m=self.m
        for p,fp in m.PINS.items():self.assertEqual(m.raw_fp((PUBLIC/Path(p).name).read_bytes()),fp)
        self.assertEqual(m.raw_fp(self.c.before),m.BEFORE);self.assertEqual(m.raw_fp(self.c.after),m.AFTER)
        repair=json.loads((PUBLIC/'REPAIR_CANDIDATE.json').read_bytes());parts=[];end=0
        self.assertEqual(len(repair['splices']),6)
        for s in repair['splices']:
            a,b=s['original_byte_start'],s['original_byte_end'];self.assertLessEqual(end,a)
            self.assertEqual(self.c.before[a:b],s['before_utf8'].encode());parts.extend((self.c.before[end:a],s['after_utf8'].encode()));end=b
        self.assertEqual(b''.join(parts)+self.c.before[end:],self.c.after)
        self.assertEqual(self.c.s.h.imports(self.c.before),self.c.s.h.imports(self.c.after))
    def test_archive_fsync_and_same_S_resume(self):
        synced=[];sync=os.fsync;unlink=Path.unlink
        def fsync(fd):synced.append(os.readlink('/proc/self/fd/'+str(fd)));sync(fd)
        def remove(path,*a,**kw):
            if path==self.active:
                for p in (self.archive,self.receipt,self.run,self.m.ROOT):self.assertIn(str(p),synced)
            return unlink(path,*a,**kw)
        with patch.object(os,'fsync',fsync),patch.object(Path,'unlink',remove):result=self.archive_once()
        self.assertFalse(self.active.exists());self.assertEqual(self.archive.read_bytes(),self.payload)
        self.state.artifacts=self.m.artifact_inventory(self.c,[self.m.TARGET]);self.state.archives=self.m.prior_archive(self.c)
        self.assertEqual(result['bindings'],self.state.archives)
        self.assertEqual(self.archive_once()['action'],'ALREADY_ARCHIVED_AND_ABSENT')
    def test_missing_setup_without_receipt_rejected(self):
        self.active.unlink()
        with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)
    def test_Q_R_S_script_and_source_identities_bound(self):
        self.archive_once();original=json.loads(self.receipt.read_bytes())
        for key in ('execution_commit','script','repair_source_commit','failed_source_commit','failed_job','module',
                    'source_path','source_before','source_after','failed_setup','published_R_inputs'):
            with self.subTest(key=key):
                record=copy.deepcopy(original);record['identity'][key]='wrong';self.receipt.write_text(json.dumps(record))
                with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)
        self.receipt.write_text(json.dumps(original));self.m.prior_archive(self.c)
    def test_old_AllK_basename_and_tampered_archive_rejected(self):
        self.archive_once();record=json.loads(self.receipt.read_bytes());original=copy.deepcopy(record)
        record['archive_path']=str(self.archive.with_name('Part3AllKLambdaChartCorrection.setup.json'))
        self.receipt.write_text(json.dumps(record))
        with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)
        self.receipt.write_text(json.dumps(original));self.archive.write_bytes(b'tampered')
        with self.assertRaises(RuntimeError):self.m.prior_archive(self.c)
    def test_setup_changed_between_archive_and_unlink_is_not_removed(self):
        binding=self.m.archive_binding
        def race(c,path):
            r=binding(c,path);self.active.write_bytes(self.payload+b'changed');return r
        with patch.object(self.m,'archive_binding',race):
            with self.assertRaises(RuntimeError):self.archive_once()
        self.assertTrue(self.active.exists());self.assertEqual(self.archive.read_bytes(),self.payload)
    def test_interruption_after_unlink_recovers_from_exact_receipt(self):
        sync=self.m.fsync_directory
        def fail(path):
            if path==self.active.parent:raise OSError('interruption after unlink')
            sync(path)
        with patch.object(self.m,'fsync_directory',fail):
            with self.assertRaises(OSError):self.archive_once()
        self.state.artifacts=self.m.artifact_inventory(self.c,[self.m.TARGET]);self.state.archives=self.m.prior_archive(self.c)
        self.assertEqual(self.archive_once()['action'],'ALREADY_ARCHIVED_AND_ABSENT')
    def test_source_after_and_source_symlink_are_held(self):
        self.m.require_preimage(self.c)
        self.source.write_bytes(self.c.after)
        with self.assertRaises(RuntimeError):self.m.require_preimage(self.c)
        other=self.source.with_name('elsewhere.lean');other.write_bytes(self.c.before)
        self.source.unlink();self.source.symlink_to(other)
        with self.assertRaises(RuntimeError):self.m.require_preimage(self.c)
    def test_actual_Q_preflight_call_failure_prevents_install(self):
        m,c=self.m,self.c;events=[]
        c.s.d.verify_lane=lambda h:events.append('lane')
        self.state.sources={m.TARGET:m.BEFORE};self.state.evidence={};self.state.retained={};self.state.accepted={}
        self.state.spec=NS(baseline={});self.state.context={};self.state.git={}
        def hold(s,q,selected):
            events.append('Q11');self.assertEqual(q,m.Q);self.assertEqual(selected,m.REMAINING)
            self.assertFalse(self.active.exists());self.assertEqual(self.archive.read_bytes(),self.payload)
            self.assertEqual(self.source.read_bytes(),c.before);raise RuntimeError('original Q HOLD')
        with patch.object(m,'prepare',lambda _:self.state),patch.object(m,'unchanged',lambda *a,**k:events.append('preserve')), \
             patch.object(c.driver,'preflight',hold),patch.object(c.s.h,'install_sources') as installer:
            with self.assertRaises(RuntimeError):m.apply_repair(c,self.run)
            installer.assert_not_called()
        self.assertEqual(events,['lane','preserve','preserve','Q11']);self.assertEqual(self.source.read_bytes(),c.before)
    def test_original_installer_single_Family_only(self):
        m,c=self.m,self.c
        other=m.PROJECT/c.s.h.module_path(m.ALLK);other.write_bytes(b'accepted AllK fixture\n')
        artifacts=m.artifact_inventory(c,[m.ALLK,m.TARGET])
        update={'module':m.TARGET,'path':m.SOURCE,'before_sha256':m.BEFORE['sha256'],
                'after_sha256':m.AFTER['sha256'],'cloud_source_mutation_required':True}
        rows=c.s.h.install_sources(m.PROJECT,[update],{m.SOURCE:c.after},self.run/'backups')
        self.assertEqual([r['module'] for r in rows],[m.TARGET]);self.assertTrue(rows[0]['mutated'])
        self.assertEqual(self.source.read_bytes(),c.after);self.assertEqual((self.run/'backups'/m.SOURCE).read_bytes(),c.before)
        self.assertEqual(other.read_bytes(),b'accepted AllK fixture\n');self.assertEqual(m.artifact_inventory(c,[m.ALLK,m.TARGET]),artifacts)
    def test_real_Q11_graph_and_supplier_evidence(self):
        manifest=json.loads((LOCAL/'entrypoint/SOURCE_MANIFEST.json').read_bytes());graph={k:r['imports'] for k,r in manifest['project_sources'].items()}
        m,c=self.m,self.c;active=c.s.h.closure(graph,m.REMAINING);prefix=c.s.h.closure(graph,m.ACCEPTED)
        self.assertEqual(active,c.s.h.closure(graph,m.ACCEPTED+m.REMAINING))
        self.assertEqual((len(active),len(active)-11,len(prefix),len(prefix)-2),(157,146,74,72))
        self.assertEqual(len(active|set(c.driver.TARGETS)),160)
        current=(active&set(c.driver.TARGETS))-set(manifest['previously_accepted_targets'])
        self.assertEqual(current,set(m.ACCEPTED+m.REMAINING));self.assertEqual(len(current),13)
        suppliers=(active&set(manifest['accepted_suppliers']))|(active&set(manifest['previously_accepted_targets']))
        result=next(r for r in json.loads(Path('/tmp/p15-q-evidence/Q_later_records.json').read_bytes()) if r.get('batch6')=='P15_CURRENT_CORRECTIONS_RESULT')
        self.assertEqual(suppliers,set(result['original_supplier_acceptance_bindings']));self.assertEqual(len(suppliers),18)
        self.assertEqual(c.s.d.compile_order([],m.REMAINING,graph),m.REMAINING)
    def test_tree_and_snapshot_encoding_matches_actual_collector(self):
        m,c=self.m,self.c;collector=load(LOCAL/'collect_q_acceptance.py','actual_collector')
        root=m.OLD_ROOT/m.Q;root.mkdir(parents=True);(root/'nested').mkdir();(root/'nested/data.json').write_bytes(b'{"frozen":true}\n')
        actual=m.tree_inventory(c);expected=collector.tree_inventory(root)
        self.assertEqual(actual,expected);self.assertEqual(m.value_fp(actual),collector.value_fp(expected))
        data={'bytes':1,'nested':{'a':[True,None,'x']}}
        self.assertEqual(m.value_fp(data),collector.value_fp(data))
    def test_unrelated_source_artifact_and_Q_evidence_changes_rejected(self):
        m,c=self.m,self.c;other='ImbalancedChen.Other'
        otherpath=m.PROJECT/c.s.h.module_path(other);otherpath.write_bytes(b'other')
        qroot=m.OLD_ROOT/m.Q;qroot.mkdir(parents=True);evidence=qroot/'old.json';evidence.write_bytes(b'evidence')
        c.driver.snapshot=lambda *a:{'old':'snapshot'}
        c.driver.acceptance_binding=lambda _s,_q,owner:{'owner':owner}
        c.s.d.original_git_state=lambda *a:{'head':'fixed'}
        st=NS(spec=NS(graph={m.TARGET:[],other:[]},baseline={'old':'snapshot'}),watch={m.TARGET,other},
              accepted={owner:{'owner':owner} for owner in m.ACCEPTED},retained={str(evidence):m.file_fp(c,evidence)},
              git={'head':'fixed'},evidence=m.tree_inventory(c))
        st.sources=m.source_inventory(c,st.spec.graph);st.artifacts=m.artifact_inventory(c,st.watch);m.unchanged(c,st)
        for path,payload in ((otherpath,b'changed'),(evidence,b'changed'),(qroot/'new.json',b'added'),
                             (m.PROJECT/('.lake/build/lib/lean/'+other.replace('.','/')+'.olean'),b'changed')):
            existed=path.exists();old=path.read_bytes() if existed else None
            path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(payload)
            with self.assertRaises(RuntimeError):m.unchanged(c,st)
            if existed:path.write_bytes(old)
            else:path.unlink()
            m.unchanged(c,st)
        c.s.d.original_git_state=lambda *a:{'head':'changed'}
        with self.assertRaises(RuntimeError):m.unchanged(c,st)

if __name__=='__main__':unittest.main(verbosity=2)
