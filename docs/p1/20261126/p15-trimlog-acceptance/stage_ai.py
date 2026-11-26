from pathlib import Path
import hashlib,json,os,subprocess
S='6d9072f7b33332eaf5ecfff22876e0404cd6ab51'
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
items=[
('docs/p1/20261126/p15-trimlog-accuracy/run_trimlog.py','20261126-p15-current-corrections-v1','run_trimlog.py',36541,'0c6307af83c197123bd2da678bfd4ac6b76916169d6d457f83733461725b8272'),
('docs/p1/20261126/p15-trimlog-accuracy/install_trimlog_source.py','20261126-p15-trimlog-source-install-v1','install_trimlog_source.py',8033,'ffa793a57558cc114985e3188f8e382b445f79618a19d82a8e8e027638f6f502')]
records=[]
for source,kind,name,size,digest in items:
 b=run('git','show',S+':'+source);assert fp(b)=={'bytes':size,'sha256':digest}
 p=Path('/workspace/p1-complete-proof')/kind/S/'published-entrypoints'/name
 put(p,b);records.append({'source':source,'path':str(p),**fp(b)})
after=gitstate();assert before==after
receipt={'status':'EXACT_AI_PUBLICATIONS_STAGED','commit':S,'files':records,'original_git_state_unchanged':True,'git_state':after,'new_lean_acceptance':False}
b=(json.dumps(receipt,indent=2,sort_keys=True)+'\n').encode()
put(Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')/S/'published-entrypoints/STAGING_RECEIPT.json',b)
print(json.dumps(receipt))
