python3 - <<'P25_CELL00_ORIGINAL_JSON_001'
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
out=root/'.lake/diagnostic/p25-cell00-original-json-attempt001'
assert not out.exists(),'preserve prior attempt'
out.mkdir()
old=json.loads((base/'charparse/RESULT.json').read_text())
assert json.loads((base/'canonical/RESULT.json').read_text())['accepted'] is True
module='ImbalancedChen.P2Saving16Cell00OriginalJson'
src=out/'src';lib=out/'lib';audit=out/'audit'
for p in [src/'ImbalancedChen',lib/'ImbalancedChen',audit]:p.mkdir(parents=True)
import base64
source=base64.b64decode('aW1wb3J0IEltYmFsYW5jZWRDaGVuLlAyT3JpZ2luYWxTYXZpbmcxOVNvdXJjZUpzb25GdWVsQnJpZGdlCmltcG9ydCBJbWJhbGFuY2VkQ2hlbi5QMlNhdmluZzE2Q2Fub25pY2FsQ2VsbDAwQmluZGluZwppbXBvcnQgSW1iYWxhbmNlZENoZW4uUDJTYXZpbmcxNkNlbGwwMFNlZ21lbnRlZFBhcnNlCgovLSEKVGhlIHVuY2hhbmdlZCBvcmlnaW5hbCBzdHJpbmcgcGFyc2VyIHJldHVybnMgdGhlIGV4YWN0IGNvbXBsZXRlIGNlbGwwMCBKU09OCnZhbHVlLiBUaGlzIGNvbXBvc2VzIHRoZSBjaGVja2VkIGNhbm9uaWNhbCB0ZXh0IGJpbmRpbmcgYW5kIHRoZSBjaGVja2VkCnJlYWRlciBjZXJ0aWZpY2F0ZTsgaXQgbWFrZXMgbm8gY2xhaW0gYWJvdXQgdGhlIHR5cGVkIGRlY29kZXIgb3IgUTk2IGd1YXJkcy4KLS8KbmFtZXNwYWNlIEltYmFsYW5jZWRDaGVuLlAyU2F2aW5nMTZDZWxsMDBPcmlnaW5hbEpzb24KCm9wZW4gUDJPcmlnaW5hbFNhdmluZzE5QXJjaGl2ZSAoU291cmNlSnNvbikKb3BlbiBQMk9yaWdpbmFsU2F2aW5nMTZPcmlnaW5hbEFyY2hpdmUgKG9yaWdpbmFsVGV4dCkKb3BlbiBQMlNhdmluZzE2U3RyaW5nQ2hhckJpbmRpbmcwMCAoY2hhcnMwMCkKb3BlbiBQMlNhdmluZzE2Q2Fub25pY2FsQ2VsbDAwQmluZGluZyAob2ZMaXN0X2NoYXJzMDBfZXFfY2Fub25pY2FsVGV4dDApCm9wZW4gUDJTYXZpbmcxNkNlbGwwMFNlZ21lbnRzIChyb290VmFsdWUgY2hhcnMwMF9sZW5ndGggY2VsbDAwX3ZhbHVlMzcxKQoKdGhlb3JlbSBjZWxsMDBfb3JpZ2luYWxfanNvbiA6CiAgICBTb3VyY2VKc29uLnBhcnNlIChvcmlnaW5hbFRleHQgKDAgOiBGaW4gMTQpKSA9IC5vayByb290VmFsdWUgOj0gYnkKICBhcHBseSBTb3VyY2VKc29uLnBhcnNlX29mX3ZhbHVlX29mX29mTGlzdF9lcQogICAgKG9yaWdpbmFsVGV4dCAoMCA6IEZpbiAxNCkpIGNoYXJzMDAgMzcxIHJvb3RWYWx1ZSBbJ1xyJywgJ1xuJ10KICAgIG9mTGlzdF9jaGFyczAwX2VxX2Nhbm9uaWNhbFRleHQwCiAgwrcgcncgW2NoYXJzMDBfbGVuZ3RoXQogICAgZGVjaWRlCiAgwrcgZXhhY3QgY2VsbDAwX3ZhbHVlMzcxCiAgwrcgcmZsCgojcHJpbnQgYXhpb21zIGNlbGwwMF9vcmlnaW5hbF9qc29uCgplbmQgSW1iYWxhbmNlZENoZW4uUDJTYXZpbmcxNkNlbGwwME9yaWdpbmFsSnNvbgo=').decode()
assert hashlib.sha256(source.encode()).hexdigest()=='3543baacddde3ff81b566b1f1c597251dd27d0981ba95161eeb25a8563ea3fda'
f=src/'ImbalancedChen/P2Saving16Cell00OriginalJson.lean';f.write_text(source)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
deps=dict(old['dependency_objects'])
reproduced=json.loads((root/'.lake/diagnostic/p25-cell00-decoded-attempt002/RESULT.json').read_text())
for row in reproduced['reproduced_accepted_objects']:
 assert row['exact_accepted_object_match'] is True
 m=row['module'];deps[m]={'path':str(root/'.lake/diagnostic/p25-cell00-decoded-attempt002/lib'/(m.replace('.','/')+'.olean')),'sha256':row['object_sha256'],'source_sha256':row['source_sha256'],'provenance':'byte-identical accepted object reproduced by prior task'}
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
reproduce=[('ImbalancedChen.P2OriginalSaving19SourceJsonFuelBridge','a6dfc833fd01f1c7463cfb694b1d77da21dd9aab1120f2d7fa6840c7229a4d52','58bedf6929e16767ea9283b0385f168765bd206d8dbe959ce8527bbeb663015d'),('ImbalancedChen.P2Saving16Cell00SegmentedParse','a08f64469fc99999bfdec271b700cd9b566dbc897eaf2a4dc6ee1f95ea88e680','a24cfc8ab4abd43bfb422e6d0b40dc19a43315eba90a96101523150a44715106')]
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
 start=time.monotonic();print('P25_CELL00_ORIGINAL_JSON_START',label,flush=True)
 log=out/(label.upper()+'.log')
 with log.open('w') as stream:
  try:r=subprocess.run(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=600);code=r.returncode;timed=False
  except subprocess.TimeoutExpired:code=124;timed=True
 state[label]={'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'timed_out':timed,'log_sha256':h(log)}
 write();print('P25_CELL00_ORIGINAL_JSON_RESULT',label,json.dumps(state[label]),log.read_text()[-2500:],flush=True)
 if code:state['status']=label.upper()+'_FAILED';write();raise SystemExit(code)
rows=[json.loads(line.split('P0_QUEUE_DECL ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_DECL ')]
inv=[json.loads(line.split('P0_QUEUE_INVENTORY ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_INVENTORY ')]
assert len(inv)==1 and sorted(inv[0]['environment'])==sorted(inv[0]['serialized'])==sorted(r['name'] for r in rows)
assert all(not any(r.get(k) for k in ['axiom','unsafe','partial']) and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)
assert any(r['name']==module+'.cell00_original_json' for r in rows)
for m,r in deps.items():assert h(lib/(m.replace('.','/')+'.olean'))==r['sha256'] and h(Path(r['path']))==r['sha256']
state.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',accepted=True,owned_declarations=rows,owned_count=len(rows),object_sha256=h(lib/(module.replace('.','/')+'.olean')))
write();print('P25_CELL00_ORIGINAL_JSON_ACCEPTED',len(rows),flush=True)
P25_CELL00_ORIGINAL_JSON_001
