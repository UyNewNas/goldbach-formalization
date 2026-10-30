from pathlib import Path
import subprocess,hashlib,json,datetime,time,sys,fcntl,os,signal
from rss_supervisor import supervise
root=Path('/workspace/scratch/ec89760698e5/goldbach-formalization'); base=Path(__file__).parent
graph=json.loads((base/'next21-cross-package-closure.json').read_text()); nodes=graph['nodes']
batch=sys.argv[1]; modules=sys.argv[2:];out=base/batch;out.mkdir(exist_ok=False)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
r={'status':'RUNNING','started':now(),'base':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'modules':modules,'stages':[],'policy':{'trust':0,'memoryMiB':6144,'threads':2,'memoryScope':'Lean -M6144 plus all-stage sampled aggregate process-tree RSS 6144 MiB threshold; not a kernel hard cap, transient peaks may be missed' ,'perSourceSeconds':1800,'totalSeconds':16200,'serialCompiler':True},'runnerSha256':sha(Path(__file__)),'rssSupervisorSha256':sha(base/'rss_supervisor.py'),'rssSupervisorTestsSha256':sha(base/'rss-supervisor-test-results.json'),'dependencyGraphSha256':sha(base/'next21-cross-package-closure.json'),'guardLogStart':len((base/'runtime/compiler-commands.jsonl').read_text().splitlines()),'dependencyScope':'Unmodified pinned external dependency source compile and selected-module kernel replay; no complete declaration inventory audit; project target transitive-axiom audit remains mandatory'}
start=time.monotonic(); lock=open(base/'batch.lock','a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
def save(): (out/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
def freeze():
 return {v['source']:sha(root/v['source']) for v in nodes.values() if v.get('source') and (root/v['source']).is_file()}|{str(p.relative_to(root)):sha(p) for package in {nodes[m]['package'] for m in modules} for name in ['lean-toolchain','lakefile.toml','lakefile.lean','lake-manifest.json'] if (p:=root/'.lake/packages'/package/name).is_file()}|{p:sha(root/p) for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
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
 manifest=json.loads((root/'lake-manifest.json').read_text()); pins={x['name']:x['rev'] for x in manifest['packages']}
 r['packages']={}
 for package in sorted({nodes[m]['package'] for m in modules}):
  packageRoot=root/'.lake/packages'/package
  head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=packageRoot,text=True).strip(); assert head==pins[package], 'package HEAD differs from pin'
  r['packages'][package]={'head':head,'expectedPin':pins[package]}
 before=freeze();(out/'source-before.json').write_text(json.dumps(before,sort_keys=True));r['sourceBeforeSha256']=sha(out/'source-before.json');save()
 for i,m in enumerate(modules):
  node=nodes[m]; assert node['package'] not in ['project','toolchain'], 'external dependency only'
  source=node['source']; obj=node['olean']; packageRoot=root/'.lake/packages'/node['package']; relative=m.replace('.','/')+'.lean'
  assert node['module']==m and (root/source)==packageRoot/relative, 'source module mapping mismatch'
  assert Path(obj)==packageRoot/'.lake/build/lib/lean'/(m.replace('.','/')+'.olean'), 'output module mapping mismatch'
  assert sha(root/source)==node['source_sha256'], 'dependency source altered'
  pinned=subprocess.check_output(['git','show','HEAD:'+relative],cwd=packageRoot)
  assert hashlib.sha256(pinned).hexdigest()==sha(root/source), 'selected package source not pinned Git blob' 
  (root/obj).parent.mkdir(parents=True,exist_ok=True)
  run(f'{i}-compile',['lake','env','lean','-R',str(root/'.lake/packages'/node['package']),'-o',obj,source])
  run(f'{i}-kernel',['lake','env','flock',str(base/'runtime/compiler.lock'),'leanchecker','--verbose',m])
  assert Path(obj).is_file(), 'expected olean absent'
  r.setdefault('objects',{})[m]={str(p.relative_to(root)):sha(p) for p in (root/obj).parent.glob((root/obj).stem+'.*')};save()
 after=freeze();(out/'source-after.json').write_text(json.dumps(after,sort_keys=True));r['sourceAfterSha256']=sha(out/'source-after.json');assert before==after,'source changed during acceptance'
 run('runtime-audit',['python3',str(base/'runtime_guard.py'),'audit','--state',str(base/'runtime/state.json'),'--require-source'])
 r['guardLogEnd']=len((base/'runtime/compiler-commands.jsonl').read_text().splitlines()); r['status']='PASS_PINNED_DEPENDENCY_BUILD'
except BaseException as e:r['status']='FAILED';r['failure']=str(e)
finally:r['finished']=now();save()
sys.exit(0 if r['status']=='PASS_PINNED_DEPENDENCY_BUILD' else 1)
