#!/usr/bin/env python3
"""Bind nine missing paths to the pinned be2 tree and v3 manifest, source-only."""
import hashlib,json,re
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parent
PREV='docs/source-only/20261119-p4a5-hdensity-install-r6/'
SOURCE_REG='docs/source-only/20261110-yellow-closure-10t/t03_saved87_actual_gain/FINAL_REGISTRY.json'
V3='docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
PIN='be2efd01c561080672e6c0ad0ba21638837afe4c'
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
 sr=js(SOURCE_REG);v3=js(V3);prev=js(PREV+'INSTALL_MANIFEST.json');audit=js(PREV+'IMPORT_AUDIT_FINAL.json')
 if sr['p1_topic']!=PIN:raise ValueError('T03 saved87 source pin mismatch')
 if v3['compiled'] or v3['kernel_verified']:raise ValueError('unexpected v3 evidence state')
 index={r['module']:r for r in v3['files']}; existing={r['target'] for r in prev['records']};results=[]
 for path in sorted((DEST/'pinned').glob('*.lean')):
  module='ImbalancedChen.'+path.stem; rec=index.get(module)
  if not rec or module not in audit['missing_project_modules']:
   raise ValueError('not a previous frontier with v3 record: '+module)
  if rec['origin'].get('commit')!=PIN:raise ValueError('not from source pin: '+module)
  blob=path.read_bytes();gitsha=hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()
  if sha(blob)!=rec['sha256'] or len(blob)!=rec['bytes'] or gitsha!=rec['git_blob_sha1'] or imports(blob)!=rec['imports']:
   raise ValueError('source bytes/size/blob/imports mismatch: '+module)
  target='ImbalancedChen/'+path.name
  if target in existing:raise ValueError('duplicate target '+module)
  source=str(path.relative_to(ROOT));existing.add(target)
  prev['records'].append({'source':source,'target':target,'sha256':rec['sha256'],'hash_registry':V3,
   'selection':'conditional_be2_and_v3_exact_bytes_cross_scope_compatibility_unverified',
   'selection_evidence':'prior actual frontier; same original be2 Git tree and v3 exact manifest SHA/blob/imports; no accepted object'})
  results.append({'module':module,'source':source,'origin':rec['origin'],'sha256':rec['sha256'],
                  'git_blob_sha1':gitsha,'bytes':len(blob),'imports':rec['imports'],
                  'prior_direct_importers':[k for k,v in audit['visited'].items() if module in v['imports']]})
 if len(results)!=9:raise ValueError('unexpected number of pinned frontier sources')
 prev['baseline']='cd330752b7ee0d083c9ccbe87cd4146efdc0d8be'
 prev['scope']='partial source staging, nine be2/v3 candidates conditional pending P4A.5 compatibility; UNCOMPILED'
 ev={'scope':'same pinned Git-tree and separate source-only manifest byte agreement, not kernel acceptance or cross-packet semantic identity',
  'original_source_registry':SOURCE_REG,'source_registry_sha256':sha(data(SOURCE_REG)),
  'manifest':V3,'manifest_sha256':sha(data(V3)),'pinned_commit':PIN,'records':results}
 (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
 (DEST/'BE2_FRONTIER_EVIDENCE.json').write_text(json.dumps(ev,indent=2,ensure_ascii=False)+'\n')
 print(json.dumps({'checked':len(results),'cross_scope_status':'conditional','pinned_commit':PIN}))
if __name__=='__main__':main()
