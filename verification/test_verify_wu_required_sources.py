import tempfile, unittest, subprocess, json
from unittest.mock import patch
from pathlib import Path
from verify_wu_required_sources import AuditError, acyclic, blob_id, digest, stage_verified, parse_imports, verify

class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(); self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.origin = self.root/'research'/'A.lean'; self.origin.parent.mkdir()
        self.origin.write_text('import Mathlib\n')
        data = self.origin.read_bytes()
        self.row = {'origin_path':'research/A.lean','destination_path':'MathlibNt/A.lean',
            'sha256':digest(data),'origin_git_blob':blob_id(data)}
    def test_stage_exact_and_idempotent(self):
        stage_verified([self.row],self.root,True)
        self.assertEqual((self.root/self.row['destination_path']).read_bytes(),self.origin.read_bytes())
        stage_verified([self.row],self.root,False)
    def test_audit_does_not_create(self):
        with self.assertRaises(AuditError):stage_verified([self.row],self.root,False)
        self.assertFalse((self.root/'MathlibNt').exists())
    def test_changed_origin_rejected(self):
        self.origin.write_text('changed')
        with self.assertRaises(AuditError):stage_verified([self.row],self.root,True)
    def test_mismatch_not_overwritten(self):
        dest=self.root/self.row['destination_path']; dest.parent.mkdir();dest.write_text('user bytes')
        with self.assertRaises(AuditError):stage_verified([self.row],self.root,True)
        self.assertEqual(dest.read_text(),'user bytes')
    def test_complete_preflight(self):
        row2=dict(self.row,destination_path='B.lean');(self.root/'B.lean').write_text('other')
        with self.assertRaises(AuditError):stage_verified([self.row,row2],self.root,True)
        self.assertFalse((self.root/self.row['destination_path']).exists())
    def test_symlink_rejected(self):
        (self.root/'MathlibNt').mkdir();(self.root/self.row['destination_path']).symlink_to(self.origin)
        with self.assertRaises(AuditError):stage_verified([self.row],self.root,True)
    def test_symlink_parent_rejected(self):
        outside=self.root/'elsewhere';outside.mkdir()
        (self.root/'MathlibNt').symlink_to(outside,target_is_directory=True)
        with self.assertRaises(AuditError):stage_verified([self.row],self.root,True)
        self.assertFalse((outside/'A.lean').exists())
    def test_cycle_rejected(self):
        with self.assertRaises(AuditError):acyclic({'a':['b'],'b':['a']})
    def test_new_import_syntax(self):
        self.assertEqual(parse_imports('public meta import all Lean.Foo\nimport all Std\n/- import Fake -/'), ['Lean.Foo','Std'])
    def test_dag(self):acyclic({'a':['b','c'],'b':['c'],'c':[]})

class GraphIntegrationTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name);self.gold=self.root/'.lake/packages/goldbach';self.gold.mkdir(parents=True)
        origin=self.gold/'research/wu2008/src/MathlibNt/Example.lean';origin.parent.mkdir(parents=True);origin.write_text('-- pinned\n')
        self.rev=self.commit(self.gold)
        (self.root/'ImbalancedChen.lean').write_text('import MathlibNt.Example\n')
        (self.root/'lake-manifest.json').write_text(json.dumps({'packagesDir':'.lake/packages','packages':[{'name':'goldbach','type':'git','rev':self.rev}]}))
        self.commit(self.root)
        self.addCleanup(patch.stopall)
        patch('verify_wu_required_sources.GOLDBACH_PIN',self.rev).start()
        patch('verify_wu_required_sources.PRODUCTION_TARGET_COUNT',1).start()
    def commit(self, root):
        def run(*args):return subprocess.check_output(['git','-C',str(root),*args],stderr=subprocess.DEVNULL,text=True).strip()
        run('init');run('config','user.email','test@example.invalid');run('config','user.name','Test')
        run('add','.');run('commit','-qm','fixture');return run('rev-parse','HEAD')
    def test_official_scope_count_mismatch(self):
        with patch('verify_wu_required_sources.PRODUCTION_TARGET_COUNT',1358):
            with self.assertRaisesRegex(AuditError, 'Official production scope changed'):
                verify(self.root,stage=True,toolchain_source=self.root/'toolchain')
    def test_complete_verified_graph_stages(self):
        result=verify(self.root,stage=True,toolchain_source=self.root/'toolchain')
        self.assertEqual(result['staged_source_count'],1)
        self.assertTrue(result['required_graph_acyclic'])
        self.assertEqual(verify(self.root,toolchain_source=self.root/'toolchain')['status'],'passed')
    def test_unknown_import_fails_before_stage(self):
        (self.root/'ImbalancedChen.lean').write_text('import Unknown.Module\nimport MathlibNt.Example\n')
        with self.assertRaises(AuditError):verify(self.root,stage=True,toolchain_source=self.root/'toolchain')
        self.assertFalse((self.gold/'MathlibNt/Example.lean').exists())
    def test_changed_dependency_rejected(self):
        (self.gold/'research/wu2008/src/MathlibNt/Example.lean').write_text('-- changed')
        with self.assertRaises(AuditError):verify(self.root,stage=True,toolchain_source=self.root/'toolchain')
    def test_unknown_untracked_shadow(self):
        other=self.root/'.lake/packages/other';other.mkdir()
        (other/'README').write_text('fixture')
        rev=self.commit(other)
        (other/'MathlibNt').mkdir();(other/'MathlibNt/Example.lean').write_text('-- untracked')
        m=json.loads((self.root/'lake-manifest.json').read_text())
        m['packages'].append({'name':'other','type':'git','rev':rev})
        (self.root/'lake-manifest.json').write_text(json.dumps(m))
        with self.assertRaises(AuditError):verify(self.root,stage=True,toolchain_source=self.root/'toolchain')
    def test_pin_mismatch(self):
        m=json.loads((self.root/'lake-manifest.json').read_text());m['packages'][0]['rev']='0'*40
        (self.root/'lake-manifest.json').write_text(json.dumps(m))
        with self.assertRaises(AuditError):verify(self.root,stage=True,toolchain_source=self.root/'toolchain')
    def test_ambiguous_root_module(self):
        other=self.root/'.lake/packages/other';(other/'MathlibNt').mkdir(parents=True)
        (other/'MathlibNt/Example.lean').write_text('-- a')
        rev=self.commit(other)
        # A root copy tracked in goldbach now conflicts with another package.
        (self.gold/'MathlibNt').mkdir();(self.gold/'MathlibNt/Example.lean').write_text('-- b')
        revg=self.commit(self.gold)
        patch('verify_wu_required_sources.GOLDBACH_PIN',revg).start()
        m=json.loads((self.root/'lake-manifest.json').read_text());m['packages'][0]['rev']=revg
        m['packages'].append({'name':'other','type':'git','rev':rev})
        (self.root/'lake-manifest.json').write_text(json.dumps(m))
        with self.assertRaises(AuditError):verify(self.root,stage=True,toolchain_source=self.root/'toolchain')

if __name__=='__main__':unittest.main()
