#!/usr/bin/env python3
"""Select a byte-verified previously registered one-token adaptation; no Lean execution."""
import hashlib, json, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]; HERE=Path(__file__).resolve().parent
PREV=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r22'
def sha(b): return hashlib.sha256(b).hexdigest()
mb=(PREV/'INSTALL_MANIFEST.json').read_bytes(); ab=(PREV/'IMPORT_AUDIT.json').read_bytes()
assert sha(mb)=='59a2bd7681a669f17b222a8b5b999d2111855ee1e5cac8b1b07d41f1f6bfcb00'
assert sha(ab)=='ed6339d54792dcb46d5625cdf8879663a6e35d389a101c6540307c2929978aa6'
m=json.loads(mb); a=json.loads(ab)
module='ImbalancedChen.P1ActualUpperNearOneBound'; e=a['visited'][module]; assert e['origin']=='checkout'
original=(ROOT/e['path']).read_bytes(); assert sha(original)==e['sha256']=='3fac5d307e02e636df9e223f102613f6bc12f017bce5411e1121d0b8bef67600'
p=a['visited']['ImbalancedChen.ActualSmallEulerNormalization']; assert p['origin']=='checkout'
provider=(ROOT/p['path']).read_bytes(); assert sha(provider)==p['sha256']=='10733388e3a16ceddc1a58387c6fb60a8c261fc46f97666575670251bc523b63'
assert b'actualSmallEulerProduct N cap w \xe2\x89\xa4 B * singularSeries N / Real.log w' in provider
assert b'have hlogy : 0 < Real.log y' in original
assert b"have hEuler' := hEuler N cap hNpos hEven y hy4 hcap" in original
old="(div_le_iff₀ hlogy).mp hEuler'".encode(); new="(le_div_iff₀ hlogy).mp hEuler'".encode()
assert original.count(old)==1; result=original.replace(old,new); assert result.replace(new,old)==original
rev='cdc81d65ea82bd35ccc2ea19f916f65d84b7a3a1'; path='docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/v3repairs/P1ActualUpperNearOneBound.lean'
registered=subprocess.check_output(['git','show',rev+':'+path],cwd=ROOT)
blob=subprocess.check_output(['git','rev-parse',rev+':'+path],cwd=ROOT,text=True).strip()
assert result==registered and blob=='468c73df5765e8e761284bfec96fe3fca26dcf22'
assert sha(result)=='e2cd0184207d94fe509ba7b9e2295c07ba0aa505f12dffcefd5a5182806903e4'
out=HERE/'P1ActualUpperNearOneBound.lean'; out.write_bytes(result)
target='ImbalancedChen/P1ActualUpperNearOneBound.lean'; assert not any(x['target']==target for x in m['records'])
m['records'].append({'source':str(out.relative_to(ROOT)),'target':target,'sha256':sha(result),'selection':'previously_registered_exact_T06_inequality_direction_overlay_source_only_uncompiled','selection_evidence':'exact selected source, predecessor theorem, positive log and one-substitution equality to registered T06 blob'})
m['baseline']='8d37455527f8c5ddae189133b457fa9bb16099a8'; m['scope']='r22 overlays and one prior registered Euler inequality direction adaptation; uncompiled'
(HERE/'INSTALL_MANIFEST.json').write_text(json.dumps(m,indent=2,ensure_ascii=False)+'\n')
evidence={'status':'SOURCE_ONLY_NOT_ELABORATED','module':module,'original_sha256':sha(original),'overlay_sha256':sha(result),'registered_commit':rev,'registered_path':path,'registered_blob':blob,'provider_sha256':sha(provider),'provider_shape':'A ≤ B / log y','positive_denominator':'hlogy : 0 < Real.log y','old':old.decode(),'new':new.decode(),'pinned_mathlib_revision':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','pinned_mathlib_source':'Mathlib/Algebra/Order/GroupWithZero/Basic.lean','pinned_mathlib_blob':'1003ca665170b581f1d63bb09a6245aea0d445d1','pinned_mathlib_le_div_iff_statement':'a ≤ b / c ↔ a * c ≤ b, given 0 < c','other_bytes_unchanged':True,'mathematical_statements_changed':False,'compiled':False}
(HERE/'INEQUALITY_EVIDENCE.json').write_text(json.dumps(evidence,indent=2,ensure_ascii=False)+'\n')
print('original',sha(original),'overlay',sha(result),'blob',blob)
