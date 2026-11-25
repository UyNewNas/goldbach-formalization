python3 - <<'P25_CELL00_DECODED_001'
from pathlib import Path
import json,hashlib,os,subprocess,time,shutil
root=Path('/workspace/p25-q96-20261125')
pub='4b7aaff36b55a7c7098fb6abf0e8f51a47efa948'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert head in ['52098e403ac4b28c72ec5958fd738ae93d785ac5',pub]
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True).strip()
if head!=pub:
 subprocess.run(['git','fetch','--no-tags','origin',pub],cwd=root,check=True)
 subprocess.run(['git','checkout','--detach',pub],cwd=root,check=True)
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==pub
base=root/'.lake/diagnostic/p25-cell00-canonical-attempt001'
out=root/'.lake/diagnostic/p25-cell00-decoded-attempt002'
assert not out.exists(),'preserve prior attempt'
out.mkdir()
old=json.loads((base/'charparse/RESULT.json').read_text())
assert json.loads((base/'canonical/RESULT.json').read_text())['accepted'] is True
module='ImbalancedChen.P2Saving16Cell00Decoded'
src=out/'src';lib=out/'lib';audit=out/'audit'
for p in [src/'ImbalancedChen',lib/'ImbalancedChen',audit]:p.mkdir(parents=True)
source=(root/'docs/source-only/20261126-p2-5-cell00-decoded/ImbalancedChen/P2Saving16Cell00Decoded.lean').read_text()
assert hashlib.sha256(source.encode()).hexdigest()=='6e9f549c3b186a0c85fb5cf9592ca544ee5737c93ff0401f7e3013a8ed047524'
f=src/'ImbalancedChen/P2Saving16Cell00Decoded.lean';f.write_text(source)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
deps={m:r for m,r in old['dependency_objects'].items() if m not in ['ImbalancedChen.P2OriginalSaving16OriginalInput','ImbalancedChen.P2Saving16CanonicalCell00Binding','ImbalancedChen.P2OriginalSaving19SourceJsonCharInput','ImbalancedChen.P2OriginalSaving19CharInputBridge']}
for m,r in deps.items():
 p=Path(r['path']);assert h(p)==r['sha256'];q=lib/(m.replace('.','/')+'.olean');shutil.copyfile(p,q);assert h(q)==r['sha256']
a=(base/'charparse/audit/Audit.lean').read_text().replace('ImbalancedChen.P2Saving16CanonicalCell00ParseDiagnostic',module)
(audit/'Audit.lean').write_text(a)
lean='/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean';checker=lean.replace('/lean','/leanchecker') if False else str(Path(lean).with_name('leanchecker'))
env=dict(os.environ);env.pop('LEAN_SRC_PATH',None);env['LEAN_SYSROOT']=str(Path(lean).parent.parent);env['LEAN_PATH']=':'.join([str(lib),*old['approved_LEAN_PATH'].split(':')[1:]])
flags=['-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=1000000','-DmaxHeartbeats=80000000']
state={'status':'STARTED','accepted':False,'module':module,'source_sha256':h(f),'source':source,'dependencies':deps,'lean_sha256':h(Path(lean)),'checker_sha256':h(Path(checker)),'approved_LEAN_PATH':env['LEAN_PATH'],'original_cell00_sha256':h(Path('/workspace/goldbach-research/eighth-prefix-family-20261009-cell-00.witness.json')),'Q96_proved':False,'P2_5_proved':False}
write=lambda:(out/'RESULT.json').write_text(json.dumps(state,indent=2)+'\n')
write()
reproduce=[('ImbalancedChen.P2OriginalSaving19SourceJsonFuel','0c98bd29f628bade9657a6828772fa2499c9be8dd2d3b16bfea5cd206405c1e4','9928b1cd0dd91cc93ff2055f00d0d147d455dd8d27783cf110e58df3d61bd088'),('ImbalancedChen.P2Saving16Cell00DirectParse','fa1c92a5fd127b913958a6a10373e8a041433ac74a4a8c36ab06da709356956c','52cf731b62270e0fdfee8468d813aacfe373853e51035b88c669dd8713393f2a')]
state['publication_commit']=pub;state['reproduced_accepted_objects']=[]
for m,source_sha,object_sha in reproduce:
 sp=root/(m.replace('.','/')+'.lean');assert h(sp)==source_sha
 cp=src/(m.replace('.','/')+'.lean');shutil.copyfile(sp,cp)
 obj=lib/(m.replace('.','/')+'.olean');log=out/(m.split('.')[-1]+'-REPRODUCE.log')
 start=time.monotonic();print('P25_REPRODUCE_ACCEPTED_START',m,flush=True)
 with log.open('w') as stream:r=subprocess.run([lean,*flags,'--root='+str(src),'-o',str(obj),str(cp)],cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=600)
 assert r.returncode==0,(m,log.read_text()[-3000:])
 assert h(obj)==object_sha,('accepted object reproduction differs',m,h(obj),object_sha)
 deps[m]={'path':str(obj),'sha256':object_sha,'source_sha256':source_sha,'provenance':'byte-identical reproduction of accepted local compiled/replayed/fully-audited object'}
 state['reproduced_accepted_objects'].append({'module':m,'object_sha256':object_sha,'source_sha256':source_sha,'seconds':round(time.monotonic()-start,3),'log_sha256':h(log),'exact_accepted_object_match':True})
 write();print('P25_REPRODUCE_ACCEPTED_MATCH',m,flush=True)
commands=[('normal',[lean,*flags,'--root='+str(src),'-o',str(lib/(module.replace('.','/')+'.olean')),str(f)]),('replay',[checker,'--verbose',module]),('audit',[lean,*flags,'--root='+str(audit),str(audit/'Audit.lean')])]
for label,cmd in commands:
 start=time.monotonic();print('P25_CELL00_DECODED_START',label,flush=True)
 log=out/(label.upper()+'.log')
 with log.open('w') as stream:
  try:r=subprocess.run(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=600);code=r.returncode;timed=False
  except subprocess.TimeoutExpired:code=124;timed=True
 state[label]={'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'timed_out':timed,'log_sha256':h(log)}
 write();print('P25_CELL00_DECODED_RESULT',label,json.dumps(state[label]),log.read_text()[-2500:],flush=True)
 if code:state['status']=label.upper()+'_FAILED';write();raise SystemExit(code)
rows=[json.loads(line.split('P0_QUEUE_DECL ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_DECL ')]
inv=[json.loads(line.split('P0_QUEUE_INVENTORY ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_INVENTORY ')]
assert len(inv)==1 and sorted(inv[0]['environment'])==sorted(inv[0]['serialized'])==sorted(r['name'] for r in rows)
assert all(not any(r.get(k) for k in ['axiom','unsafe','partial']) and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)
assert any(r['name']==module+'.cell00_decode' for r in rows)
for m,r in deps.items():assert h(lib/(m.replace('.','/')+'.olean'))==r['sha256'] and h(Path(r['path']))==r['sha256']
state.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',accepted=True,owned_declarations=rows,owned_count=len(rows),object_sha256=h(lib/(module.replace('.','/')+'.olean')))
write();print('P25_CELL00_DECODED_ACCEPTED',len(rows),flush=True)
P25_CELL00_DECODED_001
