#!/usr/bin/env python3
"""Read the registered native43 into a separate source view, not the native gate."""
import argparse,hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];PLAN=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/NATIVE_RESEARCH_OVERLAY.json'
raw=PLAN.read_bytes();assert hashlib.sha256(raw).hexdigest()=='fe5c4f8720d9649ab500589273a21c64f982a85ad724d84191a5df3b659267b9';plan=json.loads(raw);rev=plan['native_commit'];assert rev=='09b97db5764ade1246bfb77206baa1b124760958'
ap=argparse.ArgumentParser();ap.add_argument('--git-dir',type=Path,required=True);ap.add_argument('--view',type=Path,required=True);args=ap.parse_args();gitdir=args.git_dir.resolve(strict=True);view=args.view.resolve();assert ROOT not in view.parents and not view.exists();view.mkdir(parents=True)
def git(*args):return subprocess.run(['git','--git-dir='+str(gitdir),*args],capture_output=True,check=True).stdout
assert git('cat-file','-t',rev).strip()==b'commit';modules={x['module']:x for x in plan['files']};assert len(modules)==43
pending=[plan['root_module']];seen=set()
while pending:
 n=pending.pop()
 if n in seen or n not in modules:continue
 seen.add(n);pending.extend(modules[n]['imports'])
assert len(seen)==43
rows=[];other=set()
for module in sorted(seen):
 x=modules[module];b=git('show',rev+':'+x['path']);blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert len(b)==x['bytes'] and blob==x['git_blob_sha1'];imports=[]
 for line in b.decode('utf-8-sig').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:imports+=m.group(1).split()
 assert imports==x['imports'],(module,imports,x['imports']);other.update(y for y in imports if y not in modules)
 dest=view/x['install_path'];assert not dest.exists();dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b);assert dest.read_bytes()==b
 rows.append({'module':module,'source_path':x['path'],'view_path':x['install_path'],'bytes':len(b),'git_blob_sha1':blob,'sha256':hashlib.sha256(b).hexdigest(),'imports':imports})
print(json.dumps({'status':'ISOLATED_SOURCE_VIEW_ONLY_NOT_OFFICIAL_GATE_OR_INSTALL','native_commit':rev,'plan_sha256':hashlib.sha256(raw).hexdigest(),'root':plan['root_module'],'sources':len(rows),'bytes':sum(x['bytes'] for x in rows),'external_direct_imports':sorted(other),'files':rows},indent=2))
