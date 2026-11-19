#!/usr/bin/env python3
"""Stage selected T03 review inputs; preserve a documented Reader version split."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parent
REG='docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/FINAL_REGISTRY.json'
YELLOW='docs/source-only/20261110-yellow-closure-10t/'
REVIEW=YELLOW+'t09_review_density_history/REPORT.md'
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
 reg=js(REG);prev=js('docs/source-only/20261119-p4a5-hdensity-install-r6/INSTALL_MANIFEST.json'); audit=js('docs/source-only/20261119-p4a5-hdensity-install-r6/IMPORT_AUDIT.json')
 sources={};version_differences=[]
 for r in reg['external_inputs_at_review']:
  if not r['path'].endswith('.lean'):continue
  path=YELLOW+r['path'];b=data(path);name=Path(path).stem;module='ImbalancedChen.'+name
  if sha(b)!=r['sha256']:
   if name!='P4AOriginalNewFifthArchiveReader':raise ValueError('unexpected source version mismatch '+name)
   report=data(REVIEW).decode();old=r['sha256'];new=sha(b)
   if old not in report or new not in report:raise ValueError('Reader discrepancy lacks recorded review')
   version_differences.append({'module':module,'path':path,'at_review_sha256':old,'current_sha256':new,
     'review':REVIEW,'review_sha256':sha(data(REVIEW)),'policy':'not installed by this step; select final-reviewed version only with compatible consumer'})
   continue
  sources[module]={'path':path,'sha256':r['sha256'],'bytes':len(b),'imports':imports(b)}
 selected={x['target']:x for x in prev['records']};queue=list(audit['visited'])+list(audit['missing_project_modules']);seen=set();added=bound=0;conflicts=[]
 while queue:
  mod=queue.pop()
  if mod in seen:continue
  seen.add(mod)
  if mod not in sources:continue
  r=sources[mod];target='ImbalancedChen/'+mod.rsplit('.',1)[-1]+'.lean';current=selected.get(target)
  if current:
   actual=sha(data(current['source']))
   if actual!=r['sha256'] or current['sha256']!=r['sha256']:
    conflicts.append({'module':mod,'expected':r['sha256'],'actual':actual});continue
   if 'selection' in current:del current['selection'];bound+=1
   current['hash_registry']=REG;current['selection_evidence']='T03 final registry reviewed-input SHA matches actual reachable import; SOURCE_ONLY'
  elif (ROOT/target).is_file():
   actual=sha(data(target))
   if actual!=r['sha256']:conflicts.append({'module':mod,'expected':r['sha256'],'actual':actual});continue
  else:
   current={'source':r['path'],'target':target,'sha256':r['sha256'],'hash_registry':REG,
    'selection_evidence':'T03 final registry reviewed-input SHA matches actual reachable import; SOURCE_ONLY'}
   prev['records'].append(current);selected[target]=current;added+=1
  queue.extend(r['imports'])
 ev={'scope':'historical reviewed-input source identity and literal imports, not compilation or PNT/BV proof',
  'registry':REG,'registry_sha256':sha(data(REG)),'matching_lean_sources':len(sources),
  'new_reachable_staged':added,'prior_provisional_bound':bound,'conflicts':conflicts,
  'version_differences':version_differences,
  'sources':[{'module':m,**r,'reachable_in_registry_walk':m in seen,'staged':('ImbalancedChen/'+m.rsplit('.',1)[-1]+'.lean') in selected} for m,r in sources.items()]}
 (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
 (DEST/'REVIEWED_INPUT_EVIDENCE.json').write_text(json.dumps(ev,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'matching':len(sources),'version_differences':len(version_differences),'added':added,'bound':bound,'conflicts':len(conflicts)}))
if __name__=='__main__':main()
