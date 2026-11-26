python3 -B - <<'PY'
import hashlib,json,os,subprocess,sys
from pathlib import Path
root=Path('/workspace/p25-q96-20261125')
pub='2106ae104bb98cd3d647a202df069b380e2de5bc'
prior='d212b7588e534bfd31fa1c304d03275033cce449'
runner_sha='ffcc4aff64705a29d9fa94faf44350753d4ba6faf2abbd0c748d634baf363beb'
selection_sha='1be717f81e2886e5291bdff7f129dbff8d75453656d6afa88c54cfd8168f01ca'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
require(git('rev-parse','HEAD').decode().strip()==prior,'Preserve unexpected P3 HEAD')
require(not git('status','--porcelain','--untracked-files=no').strip(),'Preserve tracked P3 changes')
require(not (root/'.lake/diagnostic/p25-cell00-four-consumers-attempt008').exists(),'Preserve attempt008')
subprocess.run(['git','fetch','origin',pub],cwd=root,check=True)
subprocess.run(['git','merge-base','--is-ancestor',prior,pub],cwd=root,check=True)
path='docs/verification/20261126-p2-5-resumed/run_cell00_four_consumers_v8.py'
raw=git('show',pub+':'+path)
require(hashlib.sha256(raw).hexdigest()==runner_sha,'Published v8 runner mismatch')
selection='docs/verification/20261126-p2-5-resumed/cell00-fresh-context/FRESH_CONTEXT_SELECTION.json'
require(hashlib.sha256(git('show',pub+':'+selection)).hexdigest()==selection_sha,'Published selection mismatch')
subprocess.run(['git','checkout','--detach',pub],cwd=root,check=True)
require(not git('status','--porcelain','--untracked-files=no').strip(),'New publication not clean')
target=Path('/workspace/p25-four-consumers-v8-20261126.py')
if target.exists():require(target.is_file() and not target.is_symlink() and target.read_bytes()==raw,'Preserve existing deployed runner')
else:
 with target.open('xb') as f:f.write(raw)
log=Path('/workspace/p25-cell00-fresh-context-plan-20261126.log')
require(not log.exists(),'Preserve previous read-only plan log')
command=[sys.executable,'-B',str(target),pub,'--runner-sha256',runner_sha,'--selection-sha256',selection_sha,'--plan']
p=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
with log.open('xb') as f:f.write(p.stdout)
sys.stdout.buffer.write(p.stdout);sys.stdout.flush()
print('P25_V8_PLAN_PROCESS '+json.dumps({'publication_commit':pub,'exit_code':p.returncode,'log':str(log),'bytes':len(p.stdout),'sha256':hashlib.sha256(p.stdout).hexdigest(),'attempt008_created':(root/'.lake/diagnostic/p25-cell00-four-consumers-attempt008').exists(),'Lean_executed':False}),flush=True)
raise SystemExit(p.returncode)
PY
