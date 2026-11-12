"""Remote source/pre-post census, including ignored physical project .lean files."""
from pathlib import Path
import hashlib,json,os,sys
HERE=Path(__file__).resolve().parent
LOADABLE={'.lean','.olean','.ilean','.ir','.so','.dll','.dylib','.bc','.o','.a','.c'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert os.environ.get('GITHUB_ACTIONS')=='true'
 manifest=HERE/'Y18_MANIFEST.json';assert sha(manifest)==os.environ['EXPECTED_MANIFEST'];m=json.loads(manifest.read_text())
 project=Path(os.environ['PROJECT']).resolve();logs=Path(os.environ['LOGS']);mode=sys.argv[1];assert mode in ['pre_compile','post_compile']
 actual={p.relative_to(project).as_posix() for p in (project/'ImbalancedChen').rglob('*.lean') if p.is_file()};expected={r['install_path'] for r in m['files']};assert actual==expected
 assert not any(p.is_symlink() for p in (project/'ImbalancedChen').rglob('*'))
 # Observe the whole active project source root, including ignored bare-name
 # files. Only .git metadata and .lake's separately bound objects are excluded.
 active={};links=[]
 def fail(e):raise e
 for directory,dirs,names in os.walk(project,followlinks=False,onerror=fail):
  base=Path(directory)
  if base==project:dirs[:]=[d for d in dirs if d not in {'.git','.lake'}]
  for d in list(dirs):
   if (base/d).is_symlink():links.append((base/d).relative_to(project).as_posix());dirs.remove(d)
  for name in names:
   p=base/name;relative=p.relative_to(project).as_posix()
   if p.is_symlink():links.append(relative)
   elif p.is_file() and (p.suffix in LOADABLE or any(x in p.name for x in ['.olean.','.ilean.','.ir.','.so.'])):active[relative]=sha(p)
 assert not links
 assert set(active)==expected|{r['install_path'] for r in m['audit_sources']},('Unexpected root loadable shadow',sorted(set(active)-expected))
 for r in m['files']+m['audit_sources']:
  p=project/r['install_path'];b=p.read_bytes();assert len(b)==r['bytes'] and sha(p)==r['sha256']
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob_sha1']
 for r in m['configuration']:assert sha(project/r['install_path'])==r['sha256']
 record={'mode':mode,'source_commit':m['source_commit'],'manifest_sha256':sha(manifest),'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'files':{r['install_path']:r['sha256'] for r in m['files']+m['audit_sources']},'project_observed_source_set':sorted(actual),'whole_project_root_loadable_census':active,'pre_source_receipt_binding':None}
 if mode=='post_compile':
  pre=logs/'SOURCE_PRE.json';r=json.loads(pre.read_text());assert r['mode']=='pre_compile' and r['files']==record['files'] and r['project_observed_source_set']==record['project_observed_source_set'] and r['whole_project_root_loadable_census']==active;assert all(r[k]==record[k] for k in ['source_commit','manifest_sha256','run_id','run_attempt'])
  record['pre_source_receipt_binding']={'sha256':sha(pre)}
 out=logs/('SOURCE_PRE.json' if mode=='pre_compile' else 'SOURCE_POST.json');assert not out.exists();out.write_text(json.dumps(record,indent=2)+'\n')
if __name__=='__main__':main()
