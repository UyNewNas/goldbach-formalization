#!/usr/bin/env python3
"""Bind reachable source identities from the directly linked bank registry.

Only source bytes and literal imports are checked; no Lean proof is executed.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT=Path(__file__).resolve().parents[3]
DEST=Path(__file__).resolve().parent
PREV='docs/source-only/20261119-p4a5-hdensity-install-r3/'
HIGH='docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor_finite_policy/HIGH_PP_REGISTRY.json'
FINE='docs/source-only/20261112-resume/t03/T01_FINE_COFINAL_ALLOWLIST.json'
BANK='docs/source-only/20261110-yellow-closure-10t/t02_full87_volume_integral/successor_finite_fallback_cover/REGISTRY.json'
def data(path):return (ROOT/path).read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def js(path):return json.loads(data(path))
def imports(b):
    out=[]
    for line in b.decode().splitlines():
        m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
        if m:out.extend(m.group(1).split())
    return out

def main():
    hd=js('docs/source-only/20261112-resume/t01/FINAL_HDENSITY_REGISTRY.json')
    fr='docs/source-only/20261112-resume/t01/FINAL_FINE_REGISTRY.json'
    if sha(data(fr))!=hd['fine_predecessor_registry']['sha256']:raise ValueError('hdensity/fine mismatch')
    if sha(data(FINE))!=js(fr)['independent_allowlist']['sha256']:raise ValueError('fine/allowlist mismatch')
    if sha(data(HIGH))!=js(FINE)['existing_high_author_record']['sha256']:raise ValueError('allowlist/high mismatch')
    if sha(data(BANK))!=js(HIGH)['T02BankRegisterSHA256']:raise ValueError('high/bank mismatch')
    reg=js(BANK);records=reg['source_files']+reg['direct_and_material_reused_dependencies']
    if len(reg['source_files'])!=7 or len(reg['direct_and_material_reused_dependencies'])!=20:raise ValueError('unexpected registry')
    indexed={}; evidence=[]
    for r in records:
        module=r['module'];prefix='goldbach-proof-continuation/'
        if not r['source'].startswith(prefix):raise ValueError('unknown source root '+module)
        path=r['source'][len(prefix):]; b=data(path)
        if sha(b)!=r['sha256'] or len(b)!=r['bytes'] or imports(b)!=r['imports']:
            raise ValueError('identity or imports mismatch '+module)
        if module in indexed:raise ValueError('duplicate module '+module)
        indexed[module]=(r,path)
    prev=js(PREV+'INSTALL_MANIFEST.json');audit=js(PREV+'IMPORT_AUDIT.json')
    selected={r['target']:r for r in prev['records']}
    queue=list(audit['visited'])+list(audit['missing_project_modules'])
    seen=set(); bound=0;added=0;conflicts=[]
    while queue:
        module=queue.pop()
        if module in seen:continue
        seen.add(module)
        if module not in indexed:continue
        r,path=indexed[module]; target=r['install_path']; present=selected.get(target)
        if present:
            if present['sha256']!=r['sha256'] or sha(data(present['source']))!=r['sha256']:
                conflicts.append({'module':module,'expected':r['sha256'],'actual':present['sha256']});continue
            if 'selection' in present:del present['selection'];bound+=1
            present['hash_registry']=BANK
            present['selection_evidence']='Fine allowlist -> HIGH_PP_REGISTRY -> exact T02 bank registry; matching module, size, SHA-256 and imports; SOURCE_ONLY'
        elif (ROOT/target).is_file():
            actual=sha(data(target))
            if actual!=r['sha256']:
                conflicts.append({'module':module,'expected':r['sha256'],'actual':actual});continue
        else:
            present={'source':path,'target':target,'sha256':r['sha256'],'hash_registry':BANK,
                     'selection_evidence':'actual reachable T02 bank dependency; exact module, size, SHA-256 and imports; SOURCE_ONLY'}
            prev['records'].append(present);selected[target]=present;added+=1
        queue.extend(r['imports'])
    for module,(r,path) in indexed.items():
        evidence.append({'module':module,'source':path,'sha256':r['sha256'],
                         'imports':r['imports'],'reachable_in_registry_walk':module in seen,
                         'staged':r['install_path'] in selected})
    prev['baseline']='14fca1e25f9ffffd7b9c1ae47788e6b333726f6d'
    prev['scope']='partial source staging; bank registry chain is byte-checked; no transitive closure or Lean elaboration'
    output={'fine_allowlist':FINE,'fine_allowlist_sha256':sha(data(FINE)),
            'high_registry':HIGH,'high_registry_sha256':sha(data(HIGH)),
            'bank_registry':BANK,'bank_registry_sha256':sha(data(BANK)),
            'scope':'exact linked source identities and literal imports; no Lean proof verification',
            'registry_sources_checked':len(records),'previous_provisional_entries_bound':bound,
            'new_reachable_staged':added,'conflicts':conflicts,'records':evidence}
    (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
    (DEST/'BANK_EVIDENCE.json').write_text(json.dumps(output,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'checked':len(records),'previous_provisional_bound':bound,'new_staged':added,'conflicts':len(conflicts)}))
if __name__=='__main__':main()
