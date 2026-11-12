"""Remote-only Y18 adapter for the existing exact-byte P4 generic stage.

No Lean/Lake invocation. The root driver must bind this bundle before calling it.
Origin checkouts must be supplied explicitly; this script does not fetch Git data.
"""
from pathlib import Path
import hashlib,json,os,subprocess,sys
HERE=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def checked(b,r):
 assert (len(b),sha(b),raw(b))==(r['bytes'],r['sha256'],r['git_blob_sha1'])
 return b
def safe(root,rel):
 p=root/rel;assert not Path(rel).is_absolute() and p.resolve().is_relative_to(root.resolve()) and not p.is_symlink(),rel
 return p
def main():
 assert os.environ.get('GITHUB_ACTIONS')=='true','Root-authorized remote staging only'
 mb=(HERE/'Y18_MANIFEST.json').read_bytes();assert sha(mb)==os.environ['EXPECTED_MANIFEST']
 m=json.loads(mb);assert not m['missing'] and m['project_modules']==[r['module'] for r in m['files']]
 origins=json.loads(Path(os.environ['Y18_ORIGINS']).read_text())
 project=Path(os.environ['PROJECT']);view=Path(os.environ['Y18_SOURCE_VIEW']);logs=Path(os.environ['LOGS'])
 assert not project.exists() and not view.exists(),'New isolated roots required'
 for commit in {r['origin']['commit'] for r in m['files']}:
  p=Path(origins[commit]);assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==commit
  assert not subprocess.check_output(['git','-C',str(p),'diff','HEAD','--'])
 view.mkdir(parents=True);logs.mkdir(parents=True,exist_ok=True)
 for r in m['files']:
  origin=r.get('pre_input',r);o=origin.get('origin',r['origin']);repo=Path(origins[o['commit']])
  b=checked(subprocess.check_output(['git','-C',str(repo),'show',o['commit']+':'+o['path']]),origin)
  for t in r.get('transform',[]):
   a,c=t['old'].encode(),t['new'].encode();assert b.count(a)==t['count'];b=b.replace(a,c)
  checked(b,r);p=safe(view,r['install_path']);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 for r in m['configuration']:
  b=checked((HERE/r['path']).read_bytes(),r);safe(view,r['install_path']).write_bytes(b)
 # Only the project lakefile pin differs from the original 1294B P4 stage.
 subprocess.run([sys.executable,str(HERE/'stage_p4_y18.py'),'--source',str(view),'--manifest',str(HERE/'Y18_MANIFEST.json'),'--dest',str(project)],check=True)
 for r in m['audit_sources']:
  safe(project,r['install_path']).write_bytes(checked((HERE/r['path']).read_bytes(),r))
 provenance={'schema':'Y18_SOURCE_PROVENANCE_V1','source_commit':m['source_commit'],'manifest_sha256':sha(mb),'target':{'modules':m['project_modules'],'external_imports':json.loads((HERE/'PROJECT_SOURCE_SELECTION.json').read_text())['external_imports']},'compiled':False,'kernel_verified':False}
 (project/'Y18_PROVENANCE.json').write_text(json.dumps(provenance,indent=2)+'\n')
 (logs/'Y18_STAGE_RECEIPT.json').write_text(json.dumps({'manifest_sha256':sha(mb),'origins':origins,'project_modules':m['project_modules'],'configuration':m['configuration'],'uncompiled':True},indent=2)+'\n')
if __name__=='__main__':main()
