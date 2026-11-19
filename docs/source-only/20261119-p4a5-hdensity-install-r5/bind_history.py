#!/usr/bin/env python3
"""Bind the exact remotely pinned HistoryCore; this is not elaboration."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parent
PREV='docs/source-only/20261119-p4a5-hdensity-install-r4/'
BANK='docs/source-only/20261110-yellow-closure-10t/t02_full87_volume_integral/successor_finite_fallback_cover/REGISTRY.json'
HIGH='docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor_finite_policy/HIGH_PP_REGISTRY.json'
FINE='docs/source-only/20261112-resume/t03/T01_FINE_COFINAL_ALLOWLIST.json'
HD='docs/source-only/20261112-resume/t01/FINAL_HDENSITY_REGISTRY.json'
FR='docs/source-only/20261112-resume/t01/FINAL_FINE_REGISTRY.json'
SRC='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/P4AOriginalFull87HistoryCore.lean'
def data(p):return (ROOT/p).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(p):return json.loads(data(p))
def main():
 hd=js(HD);fr=js(FR);fine=js(FINE);high=js(HIGH);bank=js(BANK)
 if sha(data(FR))!=hd['fine_predecessor_registry']['sha256'] or sha(data(FINE))!=fr['independent_allowlist']['sha256'] or sha(data(HIGH))!=fine['existing_high_author_record']['sha256'] or sha(data(BANK))!=high['T02BankRegisterSHA256']:
  raise ValueError('provenance chain hash mismatch')
 rec=bank['remote_reused_dependency'];b=data(SRC)
 history_blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 if sha(b)!=rec['sha256'] or history_blob!=rec['git_blob_sha1'] or len(b)!=rec['bytes'] or b.count(b'\n')!=rec['lines']:
  raise ValueError('pinned source identity mismatch')
 if rec['git_commit']!='be2efd01c561080672e6c0ad0ba21638837afe4c':raise ValueError('unexpected source pin')
 actual=[]
 for line in b.decode().splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m: actual.extend(m.group(1).split())
 prev=js(PREV+'INSTALL_MANIFEST.json');audit=js(PREV+'IMPORT_AUDIT.json')
 if rec['module'] not in audit['missing_project_modules']:raise ValueError('not in previous frontier')
 if any(x['target']==rec['install_path'] for x in prev['records']):raise ValueError('duplicate target')
 prev['records'].append({'source':SRC,'target':rec['install_path'],'sha256':rec['sha256'],
  'hash_registry':BANK,'selection_evidence':'exact Git SHA, path, blob, bytes and sha256 in bank remote_reused_dependency; SOURCE_ONLY'})
 # Dictionary is the first literal import of HistoryCore.  The same
 # pinned Git tree supplies it; the original source registry fixes its SHA.
 if actual[0]!='ImbalancedChen.P4AOriginalFull87SourceDictionary':
  raise ValueError('unexpected HistoryCore dictionary import')
 dict_reg='docs/source-only/20261102-resume-30r/full87_source_history/REGISTRY.json'
 drec=next(x for x in js(dict_reg)['files'] if x['module']==actual[0])
 dict_src='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/P4AOriginalFull87SourceDictionary.lean'
 db=data(dict_src); dblob=hashlib.sha1(b'blob '+str(len(db)).encode()+b'\0'+db).hexdigest()
 if sha(db)!=drec['sha256'] or len(db)!=drec['bytes'] or dblob!='b35c77fc9f3905d87ceb9a3297625cb3267e795d':
  raise ValueError('dictionary identity mismatch')
 dict_imports=[]
 for line in db.decode().splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:dict_imports.extend(m.group(1).split())
 if dict_imports!=[i['module'] for i in drec['direct_imports']]:
  raise ValueError('dictionary imports mismatch')
 dtarget='ImbalancedChen/P4AOriginalFull87SourceDictionary.lean'
 if any(x['target']==dtarget for x in prev['records']):raise ValueError('duplicate dictionary target')
 prev['records'].append({'source':dict_src,'target':dtarget,'sha256':drec['sha256'],
  'hash_registry':dict_reg,'selection_evidence':'literal HistoryCore import from same pinned Git tree; source registry SHA and imports; SOURCE_ONLY'})
 # Match all four dictionary inputs. Two already reside at the root;
 # two are recovered from the same be2efd pinned Git tree as HistoryCore.
 recovered={
  'ImbalancedChen.P4AOriginalRemainingEighthSources':'ca9c21e4f126a3adc189e210171b1ba7b137a953',
  'ImbalancedChen.P4AOriginalFirstFailureH3SourceSemantics':'04ae8467ff017d1d6346a554a5126f62bc99fc09'}
 dict_input_evidence=[]
 for dep in drec['direct_imports']:
  name=dep['module'].split('.')[-1];target='ImbalancedChen/'+name+'.lean'
  if dep['module'] in recovered:
   path='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/'+name+'.lean'
   raw=data(path); blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
   if sha(raw)!=dep['sha256'] or blob!=recovered[dep['module']]:
    raise ValueError('dictionary source identity mismatch '+name)
   if any(x['target']==target for x in prev['records']):raise ValueError('duplicate target '+name)
   prev['records'].append({'source':path,'target':target,'sha256':dep['sha256'],
    'hash_registry':dict_reg,'selection_evidence':'literal dictionary import from same pinned Git tree; source registry SHA; SOURCE_ONLY'})
   origin='same_pinned_git_tree'
  else:
   path=dep['path'];raw=data(path);blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
   if sha(raw)!=dep['sha256']:raise ValueError('dictionary root input mismatch '+name)
   origin='checkout_root'
  dict_input_evidence.append({'module':dep['module'],'source':path,'sha256':sha(raw),'blob':blob,'origin':origin})
 # Follow the dictionary's two newly recovered dependencies one layer.
 rrec=next(x for x in js(dict_reg)['files'] if x['module']=='ImbalancedChen.P4AOriginalRemainingEighthSources')
 remaining_src='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/P4AOriginalRemainingEighthSources.lean'
 remaining_imports=[]
 for line in data(remaining_src).decode().splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:remaining_imports.extend(m.group(1).split())
 if remaining_imports!=[x['module'] for x in rrec['direct_imports']]:raise ValueError('remaining source imports mismatch')
 second_layer=[]
 for dep in rrec['direct_imports']:
  if dep['path'] is None:continue
  name=dep['module'].split('.')[-1];target='ImbalancedChen/'+name+'.lean'
  if dep['path'].startswith('docs/'):
   path='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/'+name+'.lean';raw=data(path)
   if sha(raw)!=dep['sha256']:raise ValueError('remaining input mismatch '+name)
   prev['records'].append({'source':path,'target':target,'sha256':dep['sha256'],'hash_registry':dict_reg,
     'selection_evidence':'literal RemainingEighthSources input, source registry SHA, same pinned Git tree; SOURCE_ONLY'})
   origin='same_pinned_git_tree'
  else:
   path=dep['path'];raw=data(path)
   if sha(raw)!=dep['sha256']:raise ValueError('remaining root mismatch '+name)
   origin='checkout_root'
  second_layer.append({'module':dep['module'],'source':path,'sha256':sha(raw),'origin':origin})
 h3reg='docs/source-only/20261102-resume-30p/adopted87_policy/REGISTRY.json'
 h3=next(x for x in js(h3reg)['new_lean_files'] if x.get('intended_install_module')=='ImbalancedChen.P4AOriginalFirstFailureH3Literal')
 semantics='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/P4AOriginalFirstFailureH3SourceSemantics.lean'
 if ('import '+h3['intended_install_module']) not in data(semantics).decode().splitlines():raise ValueError('H3 semantics does not import H3 literal')
 h3src='docs/source-only/20261119-p4a5-hdensity-install-r5/pinned/P4AOriginalFirstFailureH3Literal.lean';hb=data(h3src)
 if sha(hb)!=h3['sha256']:raise ValueError('H3 literal hash mismatch')
 h3imports=[]
 for line in hb.decode().splitlines():
  m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if m:h3imports.extend(m.group(1).split())
 if h3imports!=h3['direct_imports']:raise ValueError('H3 literal imports mismatch')
 prev['records'].append({'source':h3src,'target':'ImbalancedChen/P4AOriginalFirstFailureH3Literal.lean',
  'sha256':sha(hb),'hash_registry':h3reg,'selection_evidence':'literal H3 semantics import, source registry SHA and imports, same pinned Git tree; SOURCE_ONLY'})
 prev['baseline']='3399e9f51bc54ab46ea9270052c12e7e58768470'
 prev['scope']='partial source staging with exact remote HistoryCore; not transitive closure or Lean elaboration'
 evidence={'scope':'exact source retrieval and literal import inventory; no Lean proof verification',
  'bank_registry':BANK,'bank_registry_sha256':sha(data(BANK)),
  'selection':rec,'retrieved_path':SRC,'verified_sha256':sha(b),'verified_git_blob':history_blob,'actual_imports':actual,
  'previous_direct_importers':[k for k,v in audit['visited'].items() if rec['module'] in v['imports']],
  'dictionary':{'registry':dict_reg,'registry_sha256':sha(data(dict_reg)),
   'origin_commit':rec['git_commit'],'origin_path':drec['path'],'source':dict_src,
   'sha256':sha(db),'git_blob':dblob,'imports':dict_imports,'direct_inputs':dict_input_evidence},
  'remaining_inputs':second_layer,'H3_literal':{'registry':h3reg,'source':h3src,'sha256':sha(hb),'imports':h3imports}}

 (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
 (DEST/'HISTORY_EVIDENCE.json').write_text(json.dumps(evidence,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'module':rec['module'],'sha256':sha(b),'blob':history_blob,'imports':actual,'dictionary_sha256':sha(db),'dictionary_blob':dblob,'dictionary_imports':dict_imports}))
if __name__=='__main__':main()
