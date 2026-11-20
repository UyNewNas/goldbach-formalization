#!/usr/bin/env python3
"""Replace exactly two stale matrix imports, retaining the proof bytes."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
p=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json';raw=p.read_bytes();assert sha(raw)=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9'
z=next(x for x in json.loads(raw)['files'] if x['module']=='ImbalancedChen.P2OriginalCertificateBudgetAssembly')
assert z['transform']==[{'old':'import Mathlib.Data.Matrix.Notation','new':'import Mathlib.LinearAlgebra.Matrix.Notation','count':1}]
old=b'import Mathlib.Data.Matrix.Notation';new=b'import Mathlib.LinearAlgebra.Matrix.Notation'
oldmanifest=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r19/INSTALL_MANIFEST.json';m=json.loads(oldmanifest.read_bytes());audit=json.loads((oldmanifest.parent/'IMPORT_AUDIT.json').read_bytes());out=[]
S=[('P2OriginalCertificateBudgetAssembly',z['pre_input']['sha256']),('P2OriginalThirdMinorantLogDictionary','6bcaeb8d4f3e24f3422ba52cec424d0cbae84a6801e5b5cb37992652dcf38230')]
for name,oldsha in S:
 module='ImbalancedChen.'+name;meta=audit['visited'][module];assert meta['origin']=='checkout' and meta['sha256']==oldsha and 'Mathlib.Data.Matrix.Notation' in meta['imports']
 source=ROOT/meta['path'];b=source.read_bytes();assert sha(b)==oldsha and b.count(old)==1
 changed=b.replace(old,new);assert changed.replace(new,old)==b and changed.count(new)==1
 target='ImbalancedChen/'+name+'.lean';assert not any(x['target']==target for x in m['records'])
 path=HERE/(name+'.lean');path.write_bytes(changed);newsha=sha(changed);blob=hashlib.sha1(b'blob '+str(len(changed)).encode()+b'\0'+changed).hexdigest()
 item={'source':str(path.relative_to(ROOT)),'target':target,'sha256':newsha,'selection':'minimal_one_import_overlay_uncompiled','selection_evidence':'exact r19 parent SHA; byte-only import replacement; mathlib pinned tree presence checked'}
 if name=='P2OriginalCertificateBudgetAssembly':
  assert len(changed)==z['bytes'] and newsha==z['sha256'] and blob==z['git_blob_sha1'];item['hash_registry']=str(p.relative_to(ROOT))
 m['records'].append(item);out.append({'module':module,'base_path':meta['path'],'base_sha256':oldsha,'overlay_path':str(path.relative_to(ROOT)),'overlay_sha256':newsha,'overlay_git_blob':blob,'old':old.decode(),'new':new.decode(),'count':1,'matches_T06_final_source':name=='P2OriginalCertificateBudgetAssembly','proof_body_bytes_changed':False})
m['baseline']='5c930604745ab58b08de1d0a08fa38cbf399c345';m['scope']='r19 conditional source installation plus two exact matrix import overlays; not elaborated'
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n');(HERE/'MATRIX_OVERLAY_EVIDENCE.json').write_text(json.dumps({'scope':'source-only bytewise overlays; no Lean evaluation','rows':out},indent=2,ensure_ascii=False)+'\n')
for x in out:print(x['module'],x['base_sha256'],x['overlay_sha256'])
