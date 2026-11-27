"""Deploy the published geometry probe without checkout or source installation."""
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
assert subprocess.run(['git','merge-base','--is-ancestor','d4f88a20262af7d54ed0e6e58dfc533496c595e3',S],cwd=REPO).returncode==0
source='docs/p1/20261127/p15-remaining-typei-geometry/probe_geometry.py'
b=run('git','show',S+':'+source)
assert fp(b)=={'bytes': 15058, 'sha256': '9013f4e056232a48364a2d1c7ebcca8f406d9457bdf52c3da41cfae3c97866b1'}
root=Path('/workspace/p1-complete-proof/20261127-p15-remaining-typei-geometry-probe-v1')/S/'published-entrypoints'
p=root/'probe_geometry.py'
put(p,b)
after=gitstate();assert before==after
receipt={'status':'EXACT_GEOMETRY_PROBE_PUBLICATION_STAGED','commit':S,
 'files':[{'source':source,'path':str(p),**fp(b)}],
 'original_git_state_unchanged':True,'git_state':after,'new_lean_acceptance':False,
 'canonical_source_installed':False}
put(root/'STAGING_RECEIPT.json',(json.dumps(receipt,indent=2,sort_keys=True)+'\n').encode())
print(json.dumps(receipt))
