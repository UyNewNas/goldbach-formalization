#!/usr/bin/env python3
"""Stage reachable original saved87 registry sources, not a Lean verifier."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parent
BASE='docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/'
REG=BASE+'FINAL_REGISTRY.json'
PREV='docs/source-only/20261119-p4a5-hdensity-install-r5/'
def data(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(data(p))
def imports(b):
 out=[]
 for line in b.decode().splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:out.extend(m.group(1).split())
 return out

def main():
 reg=js(REG);entries=reg['authored_sources'];prev=js(PREV+'INSTALL_MANIFEST.json');audit=js(PREV+'IMPORT_AUDIT.json')
 if len(entries)!=16:raise ValueError('unexpected saved87 registry')
 if reg['p1_topic']!='be2efd01c561080672e6c0ad0ba21638837afe4c':raise ValueError('wrong saved87 source pin')
 by={}
 for rec in entries:
  mod=rec['module'];b=data(BASE+rec['file'])
  if len(b)!=rec['bytes'] or sha(b)!=rec['sha256'] or imports(b)!=rec['imports']:
   raise ValueError('source identity or imports mismatch: '+mod)
  if mod in by:raise ValueError('duplicate module')
  by[mod]=rec
 selected={r['target']:r for r in prev['records']};queue=list(audit['visited'])+list(audit['missing_project_modules']);seen=set();bound=added=0;conflicts=[]
 while queue:
  mod=queue.pop()
  if mod in seen:continue
  seen.add(mod)
  if mod not in by:continue
  r=by[mod];target='ImbalancedChen/'+r['file']; current=selected.get(target)
  if current:
   actual=sha(data(current['source']))
   if actual!=r['sha256'] or current['sha256']!=r['sha256']:
    conflicts.append({'module':mod,'expected':r['sha256'],'actual':actual});continue
   if 'selection'in current:del current['selection'];bound+=1
   current['hash_registry']=REG
   current['selection_evidence']='actual reachable saved87 source, exact original final registry SHA/bytes/imports; SOURCE_ONLY'
  elif (ROOT/target).is_file():
   actual=sha(data(target))
   if actual!=r['sha256']:
    conflicts.append({'module':mod,'expected':r['sha256'],'actual':actual});continue
  else:
   current={'source':BASE+r['file'],'target':target,'sha256':r['sha256'],'hash_registry':REG,
    'selection_evidence':'actual reachable saved87 source, exact original final registry SHA/bytes/imports; SOURCE_ONLY'}
   prev['records'].append(current);selected[target]=current;added+=1
  queue.extend(r['imports'])
 prev['baseline']='f0a0cbbe181c58c61d8e13cb30d9ae358095993f'
 prev['scope']='partial source staging; source-only original saved87 registry selection, no proof elaboration or closure'
 ev={'scope':'source byte identity, provenance and literal imports only; not Lean proof verification',
  'registry':REG,'registry_sha256':sha(data(REG)),'checked_count':len(entries),'prior_provisional_bound':bound,
  'new_reachable_staged':added,'conflicts':conflicts,
  'sources':[{'module':r['module'],'source':BASE+r['file'],'sha256':r['sha256'],'imports':r['imports'],
   'reachable_in_this_registry_walk':r['module'] in seen,'staged':'ImbalancedChen/'+r['file'] in selected} for r in entries]}
 (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
 (DEST/'SAVED87_EVIDENCE.json').write_text(json.dumps(ev,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'checked':len(entries),'bound':bound,'added':added,'conflicts':len(conflicts)}))
if __name__=='__main__':main()
