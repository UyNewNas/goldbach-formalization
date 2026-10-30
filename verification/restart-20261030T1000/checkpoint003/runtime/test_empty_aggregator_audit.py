from pathlib import Path
import sys,json,time,hashlib,fcntl
from rss_supervisor import supervise
import empty_aggregator_binding as binding
b=Path(__file__).resolve().parent;root=b.parent/'goldbach-formalization';out=b/'empty-audit-tests002';out.mkdir(exist_ok=False)
lock=(b/'batch.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
start=time.monotonic();template=(b/'EmptyAggregatorAudit.lean').read_text()
r={'status':'RUNNING','scope':'fresh dedicated audit utility fixtures, not production external-module acceptance','auditTemplateSha256':sha(b/'EmptyAggregatorAudit.lean'),'bindingHelperSha256':sha(b/'empty_aggregator_binding.py'),'runnerSha256':sha(Path(__file__)),'tests':[]}
def save(): (out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
def pycase(name,thunk,expected=True):
 try:thunk();ok=True;error=None
 except Exception as e:ok=False;error=str(e)
 t={'name':name,'kind':'python allowlist binding','expectedSuccess':expected,'passed':ok==expected,'error':error};r['tests'].append(t);save();assert t['passed'],name
source=root/'.lake/packages/goldbach/MathlibNt/SieveTheory/LinearSieve.lean';data=source.read_bytes()
pycase('exact-fixed-source-allowed',lambda:binding.validate_source(binding.MODULE,data))
pycase('reject-different-module',lambda:binding.validate_source('EmptyAggregatorFixture.Empty',data),False)
pycase('reject-wrong-sha',lambda:binding.validate_source(binding.MODULE,data+b'\n'),False)
pycase('reject-changed-import',lambda:binding.validate_source(binding.MODULE,data.replace(b'FiniteWeights',b'RosserChains',1)),False)
pycase('reject-added-declaration-source',lambda:binding.validate_source(binding.MODULE,data+b'\ntheorem forbidden : True := True.intro\n'),False)
fixtures=out/'fixtures';objects=[]
def run(name,cmd,expected,deadline):
 with (out/(name+'.log')).open('w') as f:
  result=supervise(cmd,cwd=root,stdout=f,memory_bytes=6144*1024**2,timeout_seconds=max(.01,deadline-time.monotonic()),batch_deadline=min(start+16200,deadline),poll_seconds=.02)
 passed=result['reason']=='completed' and result['termination_verified'] and ((result['exit_code']==0)==expected)
 r['tests'].append({'name':name,'command':cmd,'expectedSuccess':expected,'passed':passed,'supervision':result,'logSha256':sha(out/(name+'.log'))});save();print(name,result['exit_code'],passed,flush=True);assert passed,name
try:
 for suffix,text,changed,expected in [('Empty','import Std\n',None,True),('Nonempty','import Std\ntheorem not_empty : True := True.intro\n',None,False),('Changed','import Std\n','import Lean\n',False)]:
  deadline=time.monotonic()+1800;m='EmptyAggregatorFixture.'+suffix;p=fixtures/(m.replace('.','/')+'.lean');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
  obj=root/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
  run(suffix+'-compile',['lake','env','lean','-R',str(fixtures),'-o',str(obj),str(p)],True,deadline)
  objects.append(obj);before={str(q):sha(q) for q in obj.parent.glob(obj.stem+'.*')}
  if changed:p.write_text(changed)
  audit=out/(suffix+'Audit.lean')
  generated=template.replace('MathlibNt.SieveTheory.LinearSieve',m).replace('.lake/packages/goldbach/MathlibNt/SieveTheory/LinearSieve.lean',str(p))
  audit.write_text(generated)
  run(suffix+'-audit',['lake','env','lean','-R',str(out),str(audit)],expected,deadline)
  if not expected:
   diagnostic='Empty aggregator has environment declarations' if suffix=='Nonempty' else 'Source/header imports differ from serialized actual imports'
   assert diagnostic in (out/(suffix+'-audit.log')).read_text(), 'negative test failed for unrelated reason'
   r['tests'][-1]['requiredDiagnostic']=diagnostic;save()
  assert before=={str(q):sha(q) for q in obj.parent.glob(obj.stem+'.*')}
  if expected:
   run(suffix+'-exact-replay',['lake','env','flock',str(b/'runtime/compiler.lock'),str(b/'exact-replay'),m],True,deadline)
 assert sha(b/'EmptyAggregatorAudit.lean')==r['auditTemplateSha256'] and sha(b/'empty_aggregator_binding.py')==r['bindingHelperSha256']
 r['status']='PASS_EMPTY_AGGREGATOR_AUDIT_TESTS'
except BaseException as e:r['status']='FAILED';r['failure']=str(e)
finally:save()
sys.exit(0 if r['status']=='PASS_EMPTY_AGGREGATOR_AUDIT_TESTS' else 1)
