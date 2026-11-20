#!/usr/bin/env python3
"""Compare reachable selected sources to their recorded direct-input hashes."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
BASE=ROOT/'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density'
def read(path,sha):
    b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path)
    return json.loads(b)
g=read(BASE/'G3_REGISTRY.json','c0da5890b26433b464fd52cb278e8987b41b70873666bd23edd9bcdbdf63886d')
j=read(BASE/'REGISTRY.json','7242b3ae59e3c171eef6d0366f81824a95d41daaca5c0ea29d2876682bc1e4ea')
a=json.loads((HERE/'IMPORT_AUDIT.json').read_text())
parents=[];edges=[]
def audit(parent,dep,expected,source):
    actual=a['visited'].get(dep)
    row={'parent':parent,'dependency':dep,'registry':source,'expected_sha256':expected,
         'actual_sha256':actual['sha256'] if actual else None,
         'actual_origin':actual['origin'] if actual else None,
         'status':'missing' if not actual else ('match' if expected==actual['sha256'] else 'mismatch')}
    edges.append(row)
for x in g['supplement_sources']:
    name=x['module']; cur=a['visited'].get(name)
    if not cur or cur['sha256']!=x['sha256']:continue
    parents.append({'module':name,'registry':'G3_REGISTRY.json','sha256':x['sha256']})
    for dep in x['direct_imports']:
        expected=g['direct_imports_by_module'].get(dep,{}).get('sha256')
        if expected:audit(name,dep,expected,'G3_REGISTRY.json')
for x in j['primary_sources']:
    name=x.get('module');cur=a['visited'].get(name)
    if not cur or cur['sha256']!=x.get('sha256'):continue
    parents.append({'module':name,'registry':'REGISTRY.json','sha256':x['sha256']})
    for dep in x.get('direct_imports',[]):
        if isinstance(dep,dict) and dep.get('module') and dep.get('sha256'):
            audit(name,dep['module'],dep['sha256'],'REGISTRY.json')
print(json.dumps({'scope':'reachable exact-parent source-only registry edges with recorded SHA only; no typecheck or semantic equivalence',
 'counts':{s:sum(x['status']==s for x in edges) for s in ('match','missing','mismatch')},
 'parents':parents,'edges':edges},indent=2))
