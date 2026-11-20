#!/usr/bin/env python3
"""Iterate literal edges only with matching parent/child source-only registry.

Ambiguous differing source hashes are left unselected. No Lean evaluation.
"""
import hashlib,json,re,subprocess,sys
from collections import defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parent
OUT=Path(sys.argv[1]).resolve(); assert ROOT not in OUT.parents and not OUT.exists();OUT.mkdir(parents=True)
def sha(b):return hashlib.sha256(b).hexdigest()
def imports(b):
 o=[]
 for line in b.decode('utf-8-sig').splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:o+=m.group(1).split()
 return o
def walk(x):
 if isinstance(x,dict):
  yield x
  for y in x.values():yield from walk(y)
 elif isinstance(x,list):
  for y in x:yield from walk(y)
regs=subprocess.check_output(['rg','--files','docs/source-only/20261110-yellow-closure-10t','-g','*REGISTRY*.json','-g','*INSTALL_MANIFEST*.json'],cwd=ROOT,text=True).splitlines()
records=[]
for p in sorted(regs):
 try:
  raw=(ROOT/p).read_bytes(); obj=json.loads(raw.decode('utf-8-sig'))
 except (UnicodeError,ValueError):continue
 rows=obj['selected_files'] if 'SELECTED_INSTALL_MANIFEST' in p and isinstance(obj,dict) and isinstance(obj.get('selected_files'),list) else walk(obj)
 bymod=defaultdict(list)
 for r in rows:
  if isinstance(r,dict) and isinstance(r.get('module'),str) and isinstance(r.get('sha256'),str):bymod[r['module']].append(r)
 if bymod:records.append((p,sha(raw),bymod))
paths=subprocess.check_output(['rg','--files','-g','*.lean'],cwd=ROOT,text=True).splitlines();bybase=defaultdict(list)
for p in sorted(paths):bybase[Path(p).name].append(p)
cache={}
def get(p):
 if p not in cache:cache[p]=(ROOT/p).read_bytes()
 return cache[p]
manifest=json.loads((HERE/'CROSS_INSTALL_MANIFEST.json').read_bytes()); audit=json.loads((HERE/'CROSS_IMPORT_AUDIT.json').read_bytes()); evidence=[]
for wave in range(1,21):
 selected=[]; unresolved=[]
 for mod in sorted(audit['missing_project_modules']):
  parents=[(m,p) for m,p in audit['visited'].items() if mod in p['imports']];possible=[]
  for rp,rhash,by in records:
   matching=[{'module':m,'sha256':p['sha256']} for m,p in parents if any(v['sha256']==p['sha256'] and mod in v.get('imports',v.get('direct_imports',[])) for v in by.get(m,[]))]
   if not matching:continue
   for c in by.get(mod,[]):
    for path in bybase[mod.split('.')[-1]+'.lean']:
     b=get(path)
     if sha(b)!=c['sha256'] or ('bytes' in c and len(b)!=c['bytes']):continue
     ci=c.get('imports',c.get('direct_imports'))
     if ci is not None and imports(b)!=ci:continue
     if c.get('git_blob_sha1') and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=c['git_blob_sha1']:continue
     possible.append({'source':path,'sha256':c['sha256'],'registry':rp,'registry_sha256':rhash,'parents':matching,'imports':imports(b),'bytes':len(b)})
  unique={p['sha256'] for p in possible}
  if len(unique)!=1:
   unresolved.append({'module':mod,'candidate_hashes':sorted(unique),'reason':'no_exact_local_source_or_parent' if not unique else 'ambiguous_registered_hashes'});continue
  choice=sorted(possible,key=lambda x:(x['registry'],x['source']))[0]
  selected.append({'module':mod,'choice':choice,'evidence':possible,'actual_parents':[{'module':n,'sha256':p['sha256']} for n,p in parents]})
 if not selected:
  evidence.append({'wave':wave,'selected':[],'unresolved':unresolved});break
 for x in selected:
  c=x['choice'];manifest['records'].append({'source':c['source'],'target':audit['missing_project_modules'][x['module']],'sha256':c['sha256'],'hash_registry':c['registry'],'selection':'conditional_historical_exact_parent_and_child_pending_P4A5_elaboration','selection_evidence':'r19 iterative missing edge with at least one exact SHA parent and child in same source-only registry'})
 (HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(manifest,indent=2,ensure_ascii=False)+'\n')
 proc=subprocess.run([sys.executable,str(HERE/'stage_and_audit.py'),str(OUT/('stage'+str(wave)))],cwd=ROOT,capture_output=True,text=True,check=True)
 new=json.loads(proc.stdout); evidence.append({'wave':wave,'selected':selected,'unresolved':unresolved,'before':len(audit['missing_project_modules']),'after':len(new['missing_project_modules'])});audit=new
 print('wave',wave,'selected',len(selected),'missing',len(audit['missing_project_modules']),flush=True)
else:raise RuntimeError('wave guard exceeded')
(HERE/'IMPORT_AUDIT.json').write_text(json.dumps(audit,indent=2,ensure_ascii=False,sort_keys=True)+'\n')
(HERE/'POST_CROSS_EDGE_EVIDENCE.json').write_text(json.dumps({'scope':'conditional registered source selections; no Lean elaboration','waves':evidence},indent=2,ensure_ascii=False)+'\n')
print('staged',audit['staged_count'],'visited',audit['visited_project_modules'],'missing',len(audit['missing_project_modules']),'external',len(audit['external_modules']))
