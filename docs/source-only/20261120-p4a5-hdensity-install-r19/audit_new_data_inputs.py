#!/usr/bin/env python3
"""Audit two newly reached literal-string loaders, without reading certificates."""
import hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
stage=Path(sys.argv[1]).resolve(strict=True);work=Path(sys.argv[2]).resolve(strict=True)
a=json.loads((HERE/'IMPORT_AUDIT.json').read_bytes());base=ROOT/'docs/source-only/20261110-yellow-closure-10t'
REGS={'P2OriginalLaterSixthArchive':(base/'t05_all22_actual_density/successor_sixth_history/LATER_PAYMENT_REGISTRY.json','original_fixture_inputs'),'P2OriginalSixthLogArchive':(base/'t01_remote_fifth_kernel/successor_G7/G7_INPUT_BINDINGS.json','compile_inputs')}
out=[]
for name,(reg,key) in REGS.items():
 mod='ImbalancedChen.'+name;src=stage/'ImbalancedChen'/(name+'.lean');raw=src.read_bytes();assert hashlib.sha256(raw).hexdigest()==a['visited'][mod]['sha256']
 text=raw.decode('utf-8-sig');names=list(dict.fromkeys(re.findall(r'"(sixth-[^"/]+\.json)"',text)));rr=reg.read_bytes();records=json.loads(rr)[key];records={Path(x['path'].replace('\\','/')).name:x for x in records}
 assert len(names)==(15 if 'Later' in name else 7) and all(x in records for x in names)
 assert '../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/' in text
 for file in names:
  x=records[file];target=work.parent/'tmp/publication-20261010/verification-renewal-v2/_runs/full-final'/file;actual=None
  if target.is_file():
   h=hashlib.sha256()
   with target.open('rb') as f:
    for b in iter(lambda:f.read(1048576),b''):h.update(b)
   actual=h.hexdigest()
  out.append({'consumer':mod,'source_sha256':a['visited'][mod]['sha256'],'name':file,'original_path':x['path'],'size':x['bytes'],'expected_sha256':x['sha256'],'expected_git_blob':x.get('git_blob_sha1'),'registry':str(reg.relative_to(ROOT)),'registry_sha256':hashlib.sha256(rr).hexdigest(),'checked_work_path':str(target),'actual_sha256':actual,'status':'absent' if actual is None else ('match' if actual==x['sha256'] and target.stat().st_size==x['bytes'] else 'mismatch')})
print(json.dumps({'scope':'22 newly reached raw data inputs, identity only; no numerical evaluation','rows':out},indent=2))
