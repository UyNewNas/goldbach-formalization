#!/usr/bin/env python3
"""Recover exact registered frontier sources from immutable local Git objects."""
import hashlib
import json
import re
import subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
REG=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
def load(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);return json.loads(b)
a=load(HERE/'PRE_GIT2_IMPORT_AUDIT.json','a4ad9b02f1878cd4ce67c1cc4a9c29e7e0bf1f86274314f7da2edde13f270429')
r=load(REG,'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9')
f={x['module']:x for x in r['files']};out=[];pending=[]
for mod in sorted(a['missing_project_modules']):
 x=f.get(mod)
 if not x:continue
 o=x['origin'];assert o['kind']=='git' and o['commit'] in ('be2efd01c561080672e6c0ad0ba21638837afe4c','d5f392f6717227ab94ad4004044a037ac83be877')
 parents=[{'module':n,'sha256':v['sha256'],'origin':v['origin']} for n,v in a['visited'].items()
          if mod in v['imports'] and n in f and f[n]['sha256']==v['sha256'] and mod in f[n]['imports']]
 assert parents
 data=subprocess.run(['git','show',o['commit']+':'+o['path']],cwd=ROOT,check=True,capture_output=True).stdout
 assert len(data)==x['bytes'] and hashlib.sha256(data).hexdigest()==x['sha256']
 assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==x['git_blob_sha1']
 imports=[]
 for line in data.decode('utf-8-sig').splitlines():
  q=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if q:imports+=q.group(1).split()
 assert imports==x['imports']
 target=HERE/'pinned'/Path(*mod.split('.')[1:]).with_suffix('.lean')
 assert not target.exists() or target.read_bytes()==data
 pending.append((target,data));out.append({'module':mod,'recorded_origin':o,'source':str(target.relative_to(ROOT)),
   'sha256':x['sha256'],'git_blob_sha1':x['git_blob_sha1'],'bytes':len(data),'imports':imports,'actual_exact_parents':parents})
assert len(pending)==8
for target,data in pending:
 target.parent.mkdir(parents=True,exist_ok=True)
 if not target.exists():target.write_bytes(data)
print(json.dumps({'scope':'exact immutable Git-source bytes and prior literal edges; no Lean compatibility or proof-object claim','sources':out},indent=2))
