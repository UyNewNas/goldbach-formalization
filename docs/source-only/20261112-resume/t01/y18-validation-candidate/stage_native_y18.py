"""Remote-only exact460 research overlay and seven-library config adapter.

Preserves canonical09b sources. Every one of the selected1348 canonical paths is
read back before/after compilation, including all61 alternate-source choices.
This produces source receipts only, never proof/cache/ABI acceptance.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess
HERE=Path(__file__).resolve().parent
LOADABLE={'.lean','.olean','.ilean','.ir','.so','.dll','.dylib','.bc','.o','.a','.c'}
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def checked(b,r):
 assert (len(b),sha(b),raw(b))==(r['bytes'],r['sha256'],r['git_blob_sha1'])
 return b
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def tree(package,tracked):
 result={};links=[]
 def fail(e):raise e
 for directory,dirs,names in os.walk(package,followlinks=False,onerror=fail):
  base=Path(directory)
  if base==package:dirs[:]=[d for d in dirs if d not in {'.git','.lake'}]
  for d in list(dirs):
   if (base/d).is_symlink():links.append((base/d).relative_to(package).as_posix());dirs.remove(d)
  for n in names:
   p=base/n;r=p.relative_to(package).as_posix()
   if p.is_symlink():links.append(r)
   elif p.is_file() and r not in tracked:
    b=p.read_bytes();result[r]={'bytes':len(b),'sha256':sha(b),'git_blob_sha1':raw(b),'loadable':p.suffix in LOADABLE or any(x in p.name for x in ['.olean.','.ilean.','.ir.','.so.'])}
 return {'untracked_files':result,'unfollowed_symlinks':sorted(links)}
def main():
 assert os.environ.get('GITHUB_ACTIONS')=='true','Root-authorized remote source gate only'
 a=argparse.ArgumentParser();a.add_argument('mode',choices=['install','verify_existing']);a.add_argument('--receipt',type=Path,required=True);a.add_argument('--pre-receipt',type=Path);args=a.parse_args()
 mb=(HERE/'Y18_MANIFEST.json').read_bytes();assert sha(mb)==os.environ['EXPECTED_MANIFEST'];m=json.loads(mb)
 project=Path(os.environ['PROJECT']).resolve();package=project/'.lake/packages/goldbach';git=['git','-C',str(package)]
 assert not args.receipt.exists(),'Refuse to overwrite a source receipt'
 assert subprocess.check_output(git+['rev-parse','HEAD'],text=True).strip()==m['native_rev']
 tracked=set(subprocess.check_output(git+['ls-files','-z']).decode().split('\0'))-{''}
 overlay={r['install_path'] for r in m['native_sources']};assert len(overlay)==460 and not overlay&tracked
 before=tree(package,tracked);assert not before['unfollowed_symlinks']
 active={p for p,r in before['untracked_files'].items() if r['loadable']};assert active<=overlay
 cfg=m['native_configuration'];selected=checked((HERE/cfg['selected']['path']).read_bytes(),cfg['selected'])
 original=checked((HERE/cfg['original']['path']).read_bytes(),cfg['original'])
 changed=subprocess.check_output(git+['diff','--name-only','HEAD','--'],text=True).splitlines()
 if args.mode=='install':
  assert not args.pre_receipt and not args.receipt.exists() and not changed
  assert (package/'lakefile.toml').read_bytes()==original
 else:
  assert args.pre_receipt and active==overlay and changed==['lakefile.toml']
  assert (package/'lakefile.toml').read_bytes()==selected
  pre=read(args.pre_receipt)
  assert pre['mode']=='install' and pre['manifest_sha256']==sha(mb) and pre['run_id']==os.environ['GITHUB_RUN_ID'] and pre['run_attempt']==os.environ['GITHUB_RUN_ATTEMPT']
  assert pre['after_source_tree_census']==before
 records=[]
 for r in m['all_native_sources']:
  source=subprocess.check_output(git+['show',m['native_rev']+':'+r['path']]);checked(source,r)
  p=package/r['install_path'];assert p.resolve().is_relative_to(package.resolve()) and not p.is_symlink()
  present=p.is_file()
  if not present:
   assert args.mode=='install' and r['install_path'] in overlay
   p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(source)
  assert checked(p.read_bytes(),r)==source
  records.append({'module':r['module'],'original_revision':m['native_rev'],'original_research_path':r['path'],'installed_relative_path':r['install_path'],'installed_path':str(p.resolve()),'bytes':r['bytes'],'sha256':r['sha256'],'git_blob_sha1':r['git_blob_sha1'],'canonical_readback_verified':True,'preexisting_identical':present,'role':r['role']})
 if args.mode=='install':(package/'lakefile.toml').write_bytes(selected)
 after=tree(package,tracked);assert not after['unfollowed_symlinks']
 assert {p for p,r in after['untracked_files'].items() if r['loadable']}==overlay
 assert {p:r for p,r in before['untracked_files'].items() if p not in overlay}=={p:r for p,r in after['untracked_files'].items() if p not in overlay}
 assert subprocess.check_output(git+['diff','--name-only','HEAD','--'],text=True).splitlines()==['lakefile.toml']
 assert checked((package/'lakefile.toml').read_bytes(),cfg['selected'])==selected
 receipt={'schema':'Y18_NATIVE_SOURCE_PRE_POST_V1','mode':args.mode,'source_commit':m['source_commit'],'native_commit':m['native_rev'],'manifest_sha256':sha(mb),'acceptance_manifest_sha256':sha(mb),'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'files':records,'before_source_tree_census':before,'after_source_tree_census':after,'observed_research_overlay_paths':sorted(overlay),'tracked_configuration':cfg,'pre_install_receipt_binding':{'sha256':sha(args.pre_receipt.read_bytes())} if args.pre_receipt else None,'compiled':False,'kernel_verified':False}
 args.receipt.parent.mkdir(parents=True,exist_ok=True);args.receipt.write_text(json.dumps(receipt,indent=2)+'\n')
if __name__=='__main__':main()
