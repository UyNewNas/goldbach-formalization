"""Local file/receipt-boundary tests. No Lean or cloud execution."""
import hashlib
import json
import subprocess
from pathlib import Path
import tempfile
from types import SimpleNamespace as NS
import unittest
from unittest.mock import patch

import run_variation as a


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and path.read_bytes() != data:
        raise ValueError('immutable entry changed')
    path.write_bytes(data)


def save(path, value):
    write(path, json.dumps(value, sort_keys=True).encode())


def fp(path):
    data=Path(path).read_bytes()
    return {'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}


def command(directory, name, argv):
    path=directory/(name+'.log')
    write(path,b'fixture only\n')
    h=fp(path)
    rec={'exit_code':0,'argv':argv,'actual_built_modules':[],'actual_failed_modules':[],
         'cwd':str(a.PROJECT),'log':str(path),'log_sha256':h['sha256'],'log_bytes':h['bytes']}
    save(directory/(name+'-command.json'),rec)
    return rec


class Boundaries(unittest.TestCase):
    def setUp(self):
        td=tempfile.TemporaryDirectory()
        self.addCleanup(td.cleanup)
        tmp=Path(td.name)
        root,project=tmp/'proof',tmp/'receiver'
        root.mkdir()
        (project/'ImbalancedChen').mkdir(parents=True)
        for name,value in [('ROOT',root),('PROJECT',project)]:
            changed=patch.object(a,name,value)
            changed.start()
            self.addCleanup(changed.stop)
        self.c=c=NS(commit='f'*40,base=root/('f'*40),ident={'fixture':True},old=b'old',
                      new=b'new',runner=b'fixture adapter',review={},spec=NS(graph={},sources={}))
        self.obj=project/'target.olean'
        self.failure=False
        c.run=c.base/'variation-operation'
        c.s=NS(d=NS(write_frozen=write,save=save,fingerprint=fp,verify_lane=lambda h:None,
               runtime_binding=lambda h:{},original_git_state=lambda repo:{'head':'fixture'}),
               api=NS(read_json=lambda p:json.loads(p.read_bytes())),
               h=NS(guard=lambda i,args:['guard',*args],serialize=lambda i,path,args:['serializer',str(path),*args]))
        c.g=NS(module_artifacts=lambda *_:{'obj':self.obj.exists()},
               require_fresh_owner=lambda t,b:a.need(not b['obj'],'existing target artifact'))
        def ready(s,spec,m,run):
            return command(run/m,'direct-import-stock-readiness',s.h.guard(0,['lake','--no-build','build','+Mathlib:olean']))
        def run_owner(*args):
            (c.base/a.TARGET).mkdir()
            if self.failure: raise RuntimeError('fixture owner failure')
        c.g.direct_import_readiness=ready
        c.g.run_owner=run_owner
        def serialized(run,name,argv,relay):
            with patch.object(a,'__file__',str(run/'executed.py')):
                a.worker(c)
            return command(run,name,argv)
        c.s.ops=NS(run=serialized)
        for name,value in [('fixed',lambda c:{'native':{'x':'fixture'},'environment':{'g':True},'protected_metadata':{}}),
                           ('accepted',lambda c:{'owned':1,'public':1,'axioms':[],'binding':'fixture'})]:
            changed=patch.object(a,name,value)
            changed.start()
            self.addCleanup(changed.stop)

    def test_fresh_read_is_inert(self):
        self.assertEqual(a.check(self.c)['status'],'FRESH')
        self.assertFalse(self.c.base.exists())

    def test_existing_object_rejected(self):
        self.obj.touch()
        with self.assertRaises(ValueError): a.dispatch(self.c)
        self.assertFalse(self.c.base.exists())

    def test_existing_owner_rejected(self):
        (a.ROOT/('a'*40)/a.TARGET).mkdir(parents=True)
        with self.assertRaises(ValueError): a.dispatch(self.c)

    def test_unexpected_live_source_rejected(self):
        (a.PROJECT/a.LIVE).write_bytes(b'unknown')
        with self.assertRaises(ValueError): a.dispatch(self.c)
        self.assertEqual((a.PROJECT/a.LIVE).read_bytes(),b'unknown')

    def test_existing_original_is_backed_up(self):
        (a.PROJECT/a.LIVE).write_bytes(self.c.old)
        a.dispatch(self.c)
        self.assertEqual(a.check(self.c)['status'],'REVALIDATED')
        self.assertEqual((self.c.run/'original-installed.lean').read_bytes(),self.c.old)

    def test_absent_install_and_duplicate_rejected(self):
        a.dispatch(self.c)
        self.assertFalse((self.c.run/'original-installed.lean').exists())
        self.assertEqual((a.PROJECT/a.LIVE).read_bytes(),self.c.new)
        with self.assertRaises(ValueError): a.dispatch(self.c)

    def test_replay_rejects_native_log_change(self):
        a.dispatch(self.c)
        (self.c.run/a.TARGET/'direct-import-stock-readiness.log').write_text('changed')
        with self.assertRaises(ValueError): a.check(self.c)

    def test_failure_preserved(self):
        self.failure=True
        with self.assertRaises(RuntimeError): a.dispatch(self.c)
        self.assertTrue((self.c.run/'INSTALL.json').is_file())
        self.assertTrue((self.c.run/'PRESERVED_AFTER.json').is_file())
        self.assertFalse((self.c.run/'PASS.json').exists())
        with self.assertRaises(ValueError): a.check(self.c)
        with self.assertRaises(ValueError): a.dispatch(self.c)


class SourceProvenance(unittest.TestCase):
    def setUp(self):
        self.base=Path(__file__).parent
        name=a.NAME
        original=self.base/'..'/name
        old=original.read_bytes() if original.exists() else subprocess.check_output(
            ['git','show',a.BASE+':'+a.LIVE],cwd=self.base)
        self.inputs=[old,(self.base/'failed-v1'/name).read_bytes(),
                     (self.base/'failed-v1'/'probe-v1.log').read_bytes(),
                     (self.base/'failed-v2'/name).read_bytes(),
                     (self.base/'failed-v2'/'probe-v2.log').read_bytes(),(self.base/name).read_bytes()]

    def test_exact_archives_and_repaired_interfaces(self):
        a.verify_repair(*self.inputs)
        left,right=a.interfaces(self.inputs[0]),a.interfaces(self.inputs[-1])
        self.assertEqual([name for name in left if left[name]!=right[name]],['profile_hasDerivAt'])
        self.assertEqual(left['physicalProfile_variation_le'],right['physicalProfile_variation_le'])

    def test_repaired_source_or_failed_log_tampering_rejected(self):
        for i in (2,4,5):
            altered=self.inputs.copy()
            altered[i]+=b' '
            with self.subTest(i=i),self.assertRaises(ValueError):
                a.verify_repair(*altered)


class ProbeBoundary(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self.run = root/a.NEW_SHA/'runs'/'attempt-00000'
        self.run.mkdir(parents=True)
        self.source = (Path(__file__).parent/a.NAME).read_bytes()
        self.native = NS(h=NS(guard=lambda _,args:['guard',*args],
                              serialize=lambda _,lane,args:['serialize',str(lane),*args]))
        self.files = {a.PACKET+'/probe/probe_driver.py':b'fixture driver',
                      a.PACKET+'/probe/probe.log':b'fixture compiler log'}
        (self.run/a.NAME).write_bytes(self.source)
        (self.run/'probe.log').write_bytes(self.files[a.PACKET+'/probe/probe.log'])
        guard=self.native.h.guard(0,['lake','--no-build','env','lean',str(self.run/a.NAME)])
        self.result={'schema':'p15_mellin_variation_mathlib_only_probe_v3',
            'previous_failed_task':'job_a24eb1c578aa420083048ec97e864642',
            'previous_failed_source_sha256':a.FAILED_V2_SHA,'proof_body_unchanged':False,
            'final_conclusion_unchanged':True,'argv':self.native.h.serialize(0,self.run/'PROBE_LANE.json',guard),
            'cwd':str(a.PROJECT),'source_commit_base':a.BASE,'source_sha256':a.NEW_SHA,
            'source_bytes':len(self.source),'original_source_sha256':a.OLD_SHA,
            'imports':['Mathlib'],'project_dependencies':[],'exit_code':0,'probe_passed':True,
            'output_object_requested':False,'new_owner_accepted':False,'whole_P1_5_complete':False,
            'log_path':str(self.run/'probe.log'),'log_bytes':len((self.run/'probe.log').read_bytes()),
            'log_sha256':fp(self.run/'probe.log')['sha256']}
        (root/'driver.py').write_bytes(b'fixture driver')
        for name,value in [('PROBE_ROOT',root),('PROBE_DRIVER_PATH',root/'driver.py'),('PROBE_DRIVER_SHA',a.digest(b'fixture driver')),
                           ('PROBE_JOB_ID','fixture-only'),('git',lambda _,path:self.files[path])]:
            changed=patch.object(a,name,value)
            changed.start()
            self.addCleanup(changed.stop)

    def verify(self):
        data = json.dumps(self.result).encode()
        (self.run/'PROBE_RESULT.json').write_bytes(data)
        self.files[a.PACKET+'/probe/PROBE_RESULT.json']=data
        with patch.object(a,'PROBE_RESULT_SHA',a.digest(data)),patch.object(a,'PROBE_RESULT_BYTES',len(data)):
            return a.verified_probe('fixture-only',self.source,self.native)

    def test_exact_no_output_probe(self):
        self.assertFalse(self.verify()['formal_owner_accepted'])

    def test_failing_probe_rejected(self):
        self.result.update(exit_code=1,probe_passed=False)
        with self.assertRaises(ValueError): self.verify()

    def test_formal_credit_in_probe_rejected(self):
        self.result['new_owner_accepted']=True
        with self.assertRaises(ValueError): self.verify()

    def test_substituted_argv_rejected(self):
        self.result['argv'].append('-o')
        with self.assertRaises(ValueError): self.verify()

    def test_observed_output_rejected(self):
        (self.run/'Fake.olean').touch()
        with self.assertRaises(ValueError): self.verify()

    def test_compiler_log_substitution_rejected(self):
        (self.run/'probe.log').write_text('changed')
        with self.assertRaises(ValueError): self.verify()

    def test_unbound_probe_rejected(self):
        with patch.object(a,'PROBE_RESULT_SHA',None),self.assertRaises(ValueError):
            a.verified_probe('fixture-only',self.source,self.native)


if __name__=='__main__':
    unittest.main()
