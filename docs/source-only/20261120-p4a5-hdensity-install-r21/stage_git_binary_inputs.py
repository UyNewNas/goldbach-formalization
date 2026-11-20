#!/usr/bin/env python3
"""Recover two original source-relative binaries from their pinned Git trees."""
import argparse,hashlib,json,subprocess,tempfile,os
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];MAN=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json';AUD=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r20/IMPORT_AUDIT.json'
def filehash(p,kind='sha256'):
 h=hashlib.new(kind)
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
raw=MAN.read_bytes();assert hashlib.sha256(raw).hexdigest()=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9';a=json.loads(AUD.read_bytes());inputs=json.loads(raw)['data_inputs'];mods=['ImbalancedChen.P5OriginalFourthFifthSourceInputs','ImbalancedChen.P4AOriginalSavedSixthArchive'];ap=argparse.ArgumentParser();ap.add_argument('--lean',type=Path,required=True);arg=ap.parse_args();lean=arg.lean.resolve(strict=True);assert ROOT not in lean.parents and lean!=ROOT
records=[]
with tempfile.TemporaryDirectory(prefix='p4a5-r21-',dir=lean.parent) as tmp:
 for mod in mods:
  matches=[x for x in inputs if x.get('consuming_module')==mod and x['origin'].get('kind')=='git'];assert len(matches)==1;x=matches[0];rel=Path(x['install_path']);assert not rel.is_absolute() and '..' not in rel.parts
  loader=lean/'ImbalancedChen'/(mod.split('.')[-1]+'.lean');assert filehash(loader)==a['visited'][mod]['sha256']
  o=x['origin'];blob=subprocess.check_output(['git','rev-parse',o['commit']+':'+o['path']],cwd=ROOT,text=True).strip();assert blob==x['git_blob_sha1'];temp=Path(tmp)/rel.name
  with temp.open('wb') as f:subprocess.run(['git','cat-file','blob',blob],cwd=ROOT,stdout=f,check=True)
  assert temp.stat().st_size==x['bytes'] and filehash(temp)==x['sha256'];target=lean/rel;assert not target.is_symlink()
  if target.exists():assert target.is_file() and target.stat().st_size==x['bytes'] and filehash(target)==x['sha256']
  records.append((mod,x,temp,target))
 # Validate both sources before placing either.
 result=[]
 for mod,x,temp,target in records:
  target.parent.mkdir(parents=True,exist_ok=True)
  if not target.exists():os.replace(temp,target)
  assert filehash(target)==x['sha256'];result.append({'consumer':mod,'loader_sha256':a['visited'][mod]['sha256'],'install_path':x['install_path'],'bytes':x['bytes'],'sha256':x['sha256'],'git_blob_sha1':x['git_blob_sha1'],'origin':x['origin']})
print(json.dumps({'scope':'original binary byte identity and source placement only; no Lean or numerical evaluation','inputs':result},indent=2))
