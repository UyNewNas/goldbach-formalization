python3 - <<'PY'
import hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
repo=Path('/workspace/p2-saving16-20261125')
carrier='929fd05e4c8e57243e1517f6396975b0f03bbef9'
round7='1e80a5fa2fa2dbb346dbdef5760a7361a8001a46'
def require(ok,msg):
 if not ok: raise RuntimeError(msg)
def git(*args): return subprocess.check_output(['git',*args],cwd=repo)
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
require(git('rev-parse','HEAD').decode().strip()=='7926999deb30b63976739355b3076990b370e66f','P2 current source changed')
require(not git('status','--porcelain','--untracked-files=no').strip(),'P2 tracked files changed')
require(not (repo/'.lake/p25-followup-repairs-attempt007').exists(),'Preserve any existing attempt007')
subprocess.run(['git','fetch','origin',carrier],cwd=repo,check=True)
def deploy(path,source_commit,source_path,expected):
 data=git('show',source_commit+':'+source_path)
 require(hashlib.sha256(data).hexdigest()==expected,'Published runner SHA mismatch')
 if path.exists(): require(path.is_file() and not path.is_symlink() and path.read_bytes()==data,'Existing deployed runner differs')
 else:
  with path.open('xb') as stream: stream.write(data)
 return path
storage=deploy(Path('/workspace/p25-p2-baseline-storage-v2-20261126.py'),carrier,'docs/verification/20261126-p2-5-resumed/p2-baseline-storage-v2/recover_p2_baseline_documents_v2.py','201a0c21486552f8a20196bfc1adbd3bbcfb6bc3d249684397ed80346fa349c4')
r7=deploy(Path('/workspace/p25-round7-20261126.py'),round7,'docs/verification/20261126-p2-5-resumed/run_p2_round7.py','7599eb65dd43cf83d9664a719216f546be3b0c7c91100a42ae30de3c7174b8a0')
plan=Path('/workspace/p25-p2-baseline-storage-v2-20261126-plan001')
apply=Path('/workspace/p25-p2-baseline-storage-v2-20261126-apply001')
require(not plan.exists() and not apply.exists(),'Preserve any previous storage evidence')
base=[sys.executable,'-B',str(storage),'--runner-sha256','201a0c21486552f8a20196bfc1adbd3bbcfb6bc3d249684397ed80346fa349c4','--minimum-reclaim-bytes','536870912']
rc=subprocess.run(base+['--output',str(plan)],cwd=repo).returncode
require(rc==0,'Read-only baseline storage plan failed; no apply or Lean')
result=json.loads((plan/'RESULT.json').read_text())
require(result['status']=='READ_ONLY_PLAN_VERIFIED' and result['mutation_started'] is False and result['apply_requested'] is False,'Read-only plan is not a completed unmodified plan')
plan_sha=sha(plan/'PLAN.json')
require(result['plan_sha256']==plan_sha,'Actual plan SHA differs from successful result')
rc=subprocess.run(base+['--apply','--plan',str(plan/'PLAN.json'),'--plan-sha256',plan_sha,'--output',str(apply)],cwd=repo).returncode
require(rc==0,'Baseline storage apply did not complete; no Lean')
restored=json.loads((apply/'RESULT.json').read_text())
require(restored['status']=='BASELINE_DOCUMENT_RECOVERY_VERIFIED_NO_LEAN' and restored['storage_recovery_verified'] is True,'Storage recovery not verified')
require(shutil.disk_usage(repo).free >= 1073741824,'Unchanged 1 GiB compilation gate is not met')
print('P25_STORAGE_TO_ROUND7 '+json.dumps({'storage_plan_sha256':plan_sha,'storage_result_sha256':sha(apply/'RESULT.json'),'normal_scope':377,'owned_scope':69,'round7_publication':round7}),flush=True)
rc=subprocess.run([sys.executable,'-B',str(r7),round7,'--runner-sha256','7599eb65dd43cf83d9664a719216f546be3b0c7c91100a42ae30de3c7174b8a0','--selection-sha256','a50d75f57d17a781b4330d41249c168e1fabfbca1af979ec2a451ec791fd7269'],cwd=repo).returncode
raise SystemExit(rc)

PY
