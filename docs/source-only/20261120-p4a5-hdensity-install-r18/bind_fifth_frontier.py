#!/usr/bin/env python3
"""Bind prior missing imports only where exact parent, source hash, blob and imports match.

The separate T06 manifest is used as conditional source evidence only; no
cross-target compatibility, Lean checking, or proof-object reuse is asserted.
"""
import hashlib
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
PREV=HERE
REG=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
def load(path,expected):
 data=path.read_bytes();assert hashlib.sha256(data).hexdigest()==expected,str(path);return json.loads(data)
a=load(PREV/'PHASE4_IMPORT_AUDIT.json','1cab169fb8e29a8fb16661b36dd875e3982cc1d038a688db889f8499e6dbf039')
m=load(PREV/'PHASE4_INSTALL_MANIFEST.json','7295f06dbf1891568851ddee9a3993fe01e8504ea5def8fe0b920bb468ce65ba')
r=load(REG,'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9')
files={x['module']:x for x in r['files']};assert len(files)==len(r['files'])
paths=defaultdict(list)
found=subprocess.run(['rg','--files','-g','*.lean'],cwd=ROOT,text=True,check=True,capture_output=True).stdout.splitlines()
for p in sorted(found):paths[Path(p).name].append(p)
rows=[];summary=Counter()
for mod,target in sorted(a['missing_project_modules'].items()):
 rec=files.get(mod)
 if not rec:summary['missing_from_T06_manifest']+=1;continue
 actual_parents=[(n,x) for n,x in a['visited'].items() if mod in x['imports']]
 exact_parents=[(n,x) for n,x in actual_parents if n in files and files[n]['sha256']==x['sha256'] and mod in files[n]['imports']]
 if not exact_parents:summary['no_exact_parent_record']+=1;continue
 candidates=[]
 for path in paths[mod.split('.')[-1]+'.lean']:
  data=(ROOT/path).read_bytes()
  if hashlib.sha256(data).hexdigest()==rec['sha256']:candidates.append((path,data))
 if not candidates:summary['no_exact_local_source']+=1;continue
 assert rec['install_path']==target and len(candidates)==1,mod
 path,data=candidates[0];assert len(data)==rec['bytes']
 blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
 assert blob==rec['git_blob_sha1'],mod
 direct=[]
 for line in data.decode('utf-8-sig').splitlines():
  match=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
  if match:direct+=match.group(1).split()
 assert direct==rec['imports'],mod
 summary['conditional_exact_parent_and_local_source']+=1
 parents=[{'module':n,'origin':v['origin'],'sha256':v['sha256'],
           'T06_parent_sha_matches':n in files and files[n]['sha256']==v['sha256'] and mod in files[n]['imports']}
          for n,v in actual_parents]
 rows.append({'module':mod,'source':path,'target':target,'bytes':len(data),'sha256':rec['sha256'],
   'git_blob_sha1':blob,'T06_selection':rec.get('selection'),'T06_origin':rec.get('origin'),
   'direct_imports':direct,'actual_importers':parents})
 m['records'].append({'source':path,'target':target,'sha256':rec['sha256'],'hash_registry':str(REG.relative_to(ROOT)),
  'selection':'conditional_T06_exact_parent_source_pending_P4A5_elaboration',
  'selection_evidence':'r18 phase4 actual missing edge with at least one exact T06 parent; module SHA, blob, size and imports match; cross-target compatibility unverified'})
assert sum(summary.values())==len(a['missing_project_modules']) and len(rows)==28
m['baseline']='535e794bab690571a12a879c19f2933b42eabff1'
m['scope']='partial source-only install; T06 exact-parent evidence is conditional and does not certify the P4A5 closure'
(HERE/'PHASE5_INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'scope':'r18 phase4 literal missing edges and exact T06 source identities; cross-target compatibility and Lean unverified',
 'T06_manifest_sha256':'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9',
 'T06_status':r['status'],'T06_compiled':r['compiled'],'T06_kernel_verified':r['kernel_verified'],
 'summary':dict(sorted(summary.items())),'sources':rows},indent=2))
