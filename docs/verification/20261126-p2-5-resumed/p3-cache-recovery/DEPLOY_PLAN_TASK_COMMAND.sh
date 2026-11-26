python3 - <<'PY'
import hashlib,json,os,subprocess,sys
from pathlib import Path
repo=Path('/workspace/p25-q96-20261125')
delivery=Path('/workspace/p25-cell00-recovery-delivery')
payload=delivery/'objects-local-only.tar.xz'
publication='58b652df0144a0726818775e61d188c23ae40072'
def require(ok,msg):
 if not ok: raise RuntimeError(msg)
def git(*args): return subprocess.check_output(['git',*args],cwd=repo,text=True).strip()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
require(payload.is_file() and payload.stat().st_size==2640212 and sha(payload)=='b0719bd03bab9be02756e298cfef4bc44fa61cabbff722d00025ae460fe3ea80','Exact delivered object payload is unavailable')
initial=git('rev-parse','HEAD')
require(initial in ['be20f0b050bb787ecb98f9afdd9b6a386706f45a',publication],'Unexpected P3 checkout; stop before checkout')
dirty_raw=subprocess.check_output(['git','status','--porcelain','--untracked-files=no','-z'],cwd=repo)
if dirty_raw:
 require(initial=='be20f0b050bb787ecb98f9afdd9b6a386706f45a','Unexpected initial HEAD for tracked-source restoration')
 require(hashlib.sha256(dirty_raw).hexdigest()=='a711cf1d9ee98cbd886f9273baa77aba316f86258f81271dbe30cb97ad0553a6','Tracked worktree differs from the read-only deletion inventory')
 require(not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=repo).strip(),'Index has existing edits')
 rows=[s.decode() for s in dirty_raw.split(b'\0') if s]
 require(len(rows)==18 and all(s.startswith(' D .lake/proof-continuation/source-reviews/drafts/') for s in rows),'Only the eighteen observed missing tracked historical files may be restored')
 prepared=[]
 for row in rows:
  relative=row[3:]
  target=repo/relative
  require(not os.path.lexists(target),'Refuse to overwrite an existing tracked path')
  for p in [target,*target.parents]: require(not p.is_symlink(),'Symlink path refused')
  mode=git('ls-files','-s','--',relative).split()[0]
  require(mode=='100644','Unexpected tracked file mode')
  data=subprocess.check_output(['git','show',initial+':'+relative],cwd=repo)
  prepared.append((relative,target,data))
 receipt={'schema':'p25-missing-tracked-source-restore-v1','head':initial,'readonly_task':'c36101f1b3d244169cd882ed734ba095','before_status_sha256':hashlib.sha256(dirty_raw).hexdigest(),'files':[{'path':rel,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()} for rel,target,data in prepared],'compiled':False,'new_formal_credit':False}
 receipt_path=delivery/'tracked-source-restoration-58b652df.json'
 with receipt_path.open('x') as stream: json.dump(receipt,stream,indent=2);stream.write('\n')
 for relative,target,data in prepared:
  target.parent.mkdir(parents=True,exist_ok=True)
  with target.open('xb') as stream: stream.write(data)
  require(sha(target)==hashlib.sha256(data).hexdigest(),'Restored tracked bytes differ')
 print('P25_TRACKED_SOURCES_RESTORED '+json.dumps({'files':len(prepared),'receipt':str(receipt_path),'receipt_sha256':sha(receipt_path),'bytes':sum(len(data) for _,_,data in prepared)}),flush=True)
require(not git('status','--porcelain','--untracked-files=no'),'Tracked P3 checkout is dirty')
subprocess.run(['git','fetch','origin',publication],cwd=repo,check=True)
if initial!=publication:
 subprocess.run(['git','merge-base','--is-ancestor',initial,publication],cwd=repo,check=True)
 subprocess.run(['git','checkout','--detach',publication],cwd=repo,check=True)
pkg=repo/'docs/source-only/20261126-p2-5-cache-rematerialization'
pins={'restore_p3_cache.py':'d6d895b80f07c9bd499501cce3e275a271ccd8ddfc166826942953afa960d542','RECOVERY_SELECTION.json':'cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf','bootstrap_receipts.py':'46fa4a87040115bd8a1fa59abb598836063363374c2878992e4b7ac6ad000293','RECEIPT_BOOTSTRAP_SELECTION.json':'845ebbb50bc889d05d6ecb81e41b44eb2e95ffafa187dc7c82bae4181170cf31','P3_LOCAL_ONLY_DRIVER_PAYLOAD_MANIFEST.json':'24cf2b46e8850bf2147ac5e751049a3915466ab6131d12ab07405cb9478f0c5d'}
for f,h in pins.items(): require(sha(pkg/f)==h,'Published deployment hash mismatch: '+f)
boot=[sys.executable,'-B',str(pkg/'bootstrap_receipts.py'),'--repository',str(repo),'--manifest',str(pkg/'RECEIPT_BOOTSTRAP_SELECTION.json'),'--manifest-sha',pins['RECEIPT_BOOTSTRAP_SELECTION.json'],'--apply','--publication',publication,'--runner-sha',pins['bootstrap_receipts.py']]
subprocess.run(boot,cwd=repo,check=True)
out=delivery/'recovery-plan-58b652df.json'
err=delivery/'recovery-plan-58b652df.stderr.log'
require(not out.exists() and not err.exists(),'Preserve previous deployment plan output')
cmd=[sys.executable,'-B',str(pkg/'restore_p3_cache.py'),'--plan','--repository',str(repo),'--selection',str(pkg/'RECOVERY_SELECTION.json'),'--selection-sha',pins['RECOVERY_SELECTION.json'],'--payload-manifest',str(pkg/'P3_LOCAL_ONLY_DRIVER_PAYLOAD_MANIFEST.json'),'--payload-manifest-sha',pins['P3_LOCAL_ONLY_DRIVER_PAYLOAD_MANIFEST.json'],'--payload-archive',str(payload)]
with out.open('xb') as so,err.open('xb') as se: rc=subprocess.run(cmd,cwd=repo,stdout=so,stderr=se).returncode
summary={'publication':publication,'initial_head':initial,'plan_exit_code':rc,'plan_path':str(out),'plan_sha256':sha(out),'plan_bytes':out.stat().st_size,'stderr_path':str(err),'stderr_sha256':sha(err),'new_formal_credit':False,'P2_5_proved':False}
try:
 d=json.loads(out.read_text())
 for k in ['requirements','unique_required_hashes','exact_existing_paths','exact_available_unique_hashes','missing_object_modules','missing_objects_are_within_approved_ten','p3_object_inventory_complete','existing_conflicting_paths','future_v7_forbidden_existing_paths']:
  summary[k]=d.get(k)
 summary['missing_nonobject_payload_mappings']=d.get('missing_nonobject_payload_mappings')
 summary['runtime']=d.get('runtime')
 summary['rejected_source_candidate_count']=len(d.get('rejected_source_candidates',[]))
except Exception as e: summary['plan_parse_error']=str(e);summary['stderr_tail']=err.read_text()[-8000:]
print('P25_RECOVERY_PLAN_RESULT '+json.dumps(summary,sort_keys=True),flush=True)
raise SystemExit(rc)

PY