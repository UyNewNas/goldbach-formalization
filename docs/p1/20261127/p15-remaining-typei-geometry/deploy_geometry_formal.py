"""Deploy and execute the exact reviewed formal stager from its publication."""
from pathlib import Path
import hashlib,json,os,re,subprocess,sys
S=sys.argv[1]
assert __debug__ and re.fullmatch('[0-9a-f]{40}',S)
REPO=Path('/workspace/goldbach-formalization')
def run(*a):return subprocess.check_output(a,cwd=REPO)
def fp(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def gitstate():
 return {k:fp(run(*v)) for k,v in {
 'head':['git','rev-parse','HEAD'],'status':['git','status','--porcelain=v1','--untracked-files=all'],
 'worktree_diff':['git','diff','--binary'],'index_diff':['git','diff','--cached','--binary']}.items()}
def put(p,b):
 p.parent.mkdir(parents=True,exist_ok=True)
 assert p.parent.resolve()==p.parent
 if os.path.lexists(p):
  assert not p.is_symlink() and p.is_file() and p.read_bytes()==b
 else:
  fd=os.open(p,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o644)
  with os.fdopen(fd,'wb') as f:f.write(b);f.flush();os.fsync(f.fileno())
  fd=os.open(p.parent,os.O_RDONLY|os.O_DIRECTORY)
  try:os.fsync(fd)
  finally:os.close(fd)
before=gitstate()
subprocess.run(['git','-c','maintenance.auto=false','fetch','--no-tags','--no-write-fetch-head','origin',S],cwd=REPO,check=True)
assert subprocess.run(['git','merge-base','--is-ancestor','45e8de70fb3045b04f3ef3ad2ff364c7ee2f390c',S],cwd=REPO).returncode==0
source='docs/p1/20261127/p15-remaining-typei-geometry/stage_geometry_formal.py'
b=run('git','show',S+':'+source)
assert fp(b)=={'bytes':5625,'sha256':'219070bce656fff8fb4e66740d4c7d7571cdc524ba2fe4a2322a489e7a0c94ec'}
p=Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')/S/'published-entrypoints/stage_geometry_formal.py'
put(p,b)
assert gitstate()==before
subprocess.run([sys.executable,'-B',str(p),'--publication',S],cwd=REPO,check=True)
assert gitstate()==before
