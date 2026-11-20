#!/usr/bin/env python3
"""List remaining source candidates by recorded hashes; do not select them."""
import hashlib,json,subprocess
from pathlib import Path
from collections import defaultdict
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parent
A=json.loads((HERE/'IMPORT_AUDIT.json').read_text())
missing=A['missing_project_modules']; names={m.split('.')[-1]:m for m in missing}
def walk(x):
 if isinstance(x,dict):
  yield x
  for v in x.values(): yield from walk(v)
 elif isinstance(x,list):
  for v in x: yield from walk(v)
paths=subprocess.run(['rg','--files','docs/source-only/20261110-yellow-closure-10t','-g','*REGISTRY*.json'],cwd=ROOT,check=True,text=True,capture_output=True).stdout.splitlines()
index=defaultdict(list)
for p in paths:
 try:r=json.loads((ROOT/p).read_text(encoding='utf-8-sig'))
 except (ValueError,UnicodeError):continue
 for v in walk(r):
  sha=v.get('sha256'); path=v.get('path')
  if not isinstance(sha,str) or len(sha)!=64 or not isinstance(path,str):continue
  basename=path.replace('\\','/').rsplit('/',1)[-1]
  name=basename.removesuffix('.lean')
  if name not in names:continue
  matches=[]
  for local in ROOT.glob('docs/source-only/20261110-yellow-closure-10t/**/'+basename):
   b=local.read_bytes()
   if hashlib.sha256(b).hexdigest()==sha:matches.append(str(local.relative_to(ROOT)))
  index[name].append({'registry':p,'registry_sha256':hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),'registered_path':path,'sha256':sha,'matching_local_paths':matches})
rows=[]
for name,mod in sorted(names.items()):
 parents=[{'module':p,'sha256':r['sha256']} for p,r in A['visited'].items() if mod in r['imports']]
 rows.append({'module':mod,'actual_importers':parents,'candidate_registry_records':index[name]})
print(json.dumps({'scope':'candidate discovery only; no parent-edge compatibility claim, no source selected','rows':rows},indent=2,ensure_ascii=False))
