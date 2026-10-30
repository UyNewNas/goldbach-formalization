from pathlib import Path
import subprocess,hashlib,json,datetime,time,sys,fcntl,os,signal
from rss_supervisor import supervise
root=Path('/workspace/scratch/ec89760698e5/goldbach-formalization'); base=Path(__file__).parent
batch=sys.argv[1]; modules=sys.argv[2:];out=base/batch;out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
r={'status':'RUNNING','started':now(),'base':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'modules':modules,'stages':[],'policy':{'trust':0,'memoryMiB':6144,'threads':2,'memoryScope':'Lean -M6144 plus sampled aggregate process-tree RSS6144MiB; transient peaks may be missed, not a kernel hard cap','perSourceSeconds':1800,'totalSeconds':16200,'serialCompiler':True},'runnerSha256':sha(Path(__file__)),'rssSupervisorSha256':sha(base/'rss_supervisor.py'),'rssSupervisorTestsSha256':sha(base/'rss-supervisor-test-results.json'),'auditTemplateSha256':sha(root/'verification/parts/p0/queue/AuditTemplate.lean'),'guardLogStart':len((base/'runtime/compiler-commands.jsonl').read_text().splitlines()),'dependencyScope':'Exact pinned official mathlib cache; selected project modules freshly compiled; no full-root claim'}
toolTests=json.loads((base/'exact-tests001/receipt.json').read_text());toolComparison=json.loads((base/'ExactReplay-source-comparison.json').read_text())
assert toolTests['status']=='PASS_AUDIT_UTILITY_TESTS' and all(x['passed'] for x in toolTests['tests'])
assert sha(base/'exact-replay')==toolTests['binarySha256'] and sha(base/'ExactReplay.lean')==toolTests['sourceSha256']==toolComparison['candidate_source_sha256']
assert toolComparison['copied_function_identical']
r['kernelEntry']={'mode':'exact target, official replayFromImports copied byte-for-byte; no prefix enumeration or parallel target scheduling','sourceSha256':sha(base/'ExactReplay.lean'),'binarySha256':sha(base/'exact-replay'),'functionSha256':toolComparison['function_sha256'],'sourceComparisonSha256':sha(base/'ExactReplay-source-comparison.json'),'testReceiptSha256':sha(base/'exact-tests001/receipt.json'),'buildReceiptSha256':sha(base/'exact-build001/receipt.json'),'scope':'all own target declarations from most-private data replayed against imported environment, not fresh replay of imports'}
start=time.monotonic(); lock=open(base/'batch.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def save(): (out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
def freeze():
 return {str(p.relative_to(root)):sha(p) for p in sorted((root/'ImbalancedChen').rglob('*.lean'))}|{v['source']:sha(root/v['source']) for v in json.loads((base/'next21-cross-package-closure.json').read_text())['nodes'].values() if v.get('source') and v.get('package') in ['goldbach','LeanArchitect']}|{p:sha(root/p) for p in ['ImbalancedChen.lean','lean-toolchain','lakefile.toml','lake-manifest.json']}
def run(label,cmd,limit=1800):
 remaining=int(16200-(time.monotonic()-start));assert remaining>0
 t=time.monotonic(); stage={'label':label,'command':cmd,'started':now()};r['active']=stage;save()
 with (out/(label+'.log')).open('w') as f:
  supervision=supervise(cmd,cwd=root,stdout=f,memory_bytes=6144*1024*1024,timeout_seconds=min(limit,remaining),batch_deadline=start+16200,poll_seconds=0.02)
  stage['supervision']=supervision;code=supervision['exit_code']
  if not supervision['termination_verified']: code=125
 stage.update(exitCode=code,seconds=time.monotonic()-t,logSha256=sha(out/(label+'.log')));r['stages'].append(stage);r.pop('active');save();print(label,code,flush=True)
 if code: raise RuntimeError(label+' failed '+str(code))
try:
 before=freeze();(out/'source-before.json').write_text(json.dumps(before,sort_keys=True));r['sourceBeforeSha256']=sha(out/'source-before.json');save()
 template=(root/'verification/parts/p0/queue/AuditTemplate.lean').read_text()
 for i,m in enumerate(modules):
  source=m.replace('.','/')+'.lean';obj='.lake/build/lib/lean/'+m.replace('.','/')+'.olean';(root/obj).parent.mkdir(parents=True,exist_ok=True)
  run(f'{i}-compile',['lake','env','lean','-o',obj,source])
  audit=root/'verification/rebuild-20261030'/f'{m.split(".")[-1]}Audit.lean';audit.parent.mkdir(exist_ok=True);audit.write_text(template.replace('TARGET_IMPORT',m).replace('TARGET_NAME',m))
  run(f'{i}-axioms',['lake','env','lean',str(audit.relative_to(root))])
  run(f'{i}-kernel',['lake','env','flock',str(base/'runtime/compiler.lock'),str(base/'exact-replay'),m])
  r.setdefault('objects',{})[m]={str(p.relative_to(root)):sha(p) for p in (root/obj).parent.glob((root/obj).stem+'.*')};save()
 after=freeze();(out/'source-after.json').write_text(json.dumps(after,sort_keys=True));r['sourceAfterSha256']=sha(out/'source-after.json');assert before==after,'source changed during acceptance'
 run('runtime-audit',['python3',str(base/'runtime_guard.py'),'audit','--state',str(base/'runtime/state.json'),'--require-source'])
 r['guardLogEnd']=len((base/'runtime/compiler-commands.jsonl').read_text().splitlines()); r['auditSourceSha256']={str(p.relative_to(root)):sha(p) for p in (root/'verification/rebuild-20261030').glob('*Audit.lean')}; r['status']='PASS_SELECTED_MODULES'
except BaseException as e:r['status']='FAILED';r['failure']=str(e)
finally:r['finished']=now();save()
sys.exit(0 if r['status']=='PASS_SELECTED_MODULES' else 1)
