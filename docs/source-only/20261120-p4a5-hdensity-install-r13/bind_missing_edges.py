#!/usr/bin/env python3
"""Install distinct missing hash-recorded edges, not a Lean compatibility claim."""
import hashlib
import json
import re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
PREV=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r12'
BASE=ROOT/'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density'
def read(path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return json.loads(b)
g=read(BASE/'G3_REGISTRY.json','c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d')
j=read(BASE/'REGISTRY.json','7242b3ae59e3c171eef6d0366f81824a95d41daaca5c0ea29d2876682bc1e4ea')
edges=read(PREV/'REGISTERED_EDGE_AUDIT.json','47b5f5d8af0afa4e655998ac738775e0db12e1eee568102468a4f031b2cc0fe6')
a=read(PREV/'IMPORT_AUDIT.json','2d86add163805bb27e2fc5880cf732ecfc596f1553a357ade345a223e9f86d5c')
m=read(PREV/'INSTALL_MANIFEST.json','b9f31ac7fa3f4a288ad660b980c69d544acef06cf34a9822c78b9e92cec1424e')
m['baseline']='103617db065bd29e61d6f5b87846348ef0bc7f46'
m['scope']='partial source-only install; missing exact registry edges conditionally staged; mismatch retained'
names=sorted({x['dependency'] for x in edges['edges'] if x['status']=='missing'})
assert len(names)==6
out=[]
for mod in names:
 wanted=[x for x in edges['edges'] if x['status']=='missing' and x['dependency']==mod]
 expected={x['expected_sha256'] for x in wanted};assert len(expected)==1
 candidates=[]
 if mod in g['direct_imports_by_module']:candidates.append((g['direct_imports_by_module'][mod],BASE/'G3_REGISTRY.json'))
 for x in j['primary_sources']:
  for y in x.get('direct_imports',[]):
   if isinstance(y,dict) and y.get('module')==mod:candidates.append((y,BASE/'REGISTRY.json'))
 candidates=[(x,r) for x,r in candidates if x.get('sha256') in expected]
 assert candidates
 item,registry=candidates[0];src=item['repository_path'];target='/'.join(mod.split('.'))+'.lean'
 assert a['missing_project_modules'][mod]==target
 data=(ROOT/src).read_bytes();assert len(data)==item['bytes'] and hashlib.sha256(data).hexdigest()==item['sha256']
 imports=[k.group(1) for line in data.decode().splitlines() if (k:=re.fullmatch(r'\s*import\s+([A-Za-z0-9_.]+)\s*',line))]
 importers=[{'module':p,'sha256':v['sha256'],'origin':v['origin'],'path':v['path']} for p,v in a['visited'].items() if mod in v['imports']]
 assert importers
 m['records'].append({'source':src,'target':target,'sha256':item['sha256'],'hash_registry':str(registry.relative_to(ROOT)),
  'selection':'conditional_registered_edge_pending_full_elaboration',
  'selection_evidence':'r12 matched-parent direct input registry SHA and actual missing edge; Lean compatibility unverified'})
 out.append({'module':mod,'source':src,'target':target,'sha256':item['sha256'],'bytes':len(data),
  'source_registry':str(registry.relative_to(ROOT)),'direct_imports_observed':imports,'importers':importers,'required_edges':wanted})
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'scope':'source identities and literal missing edges only; no Lean elaboration','sources':out},indent=2))
