#!/usr/bin/env python3
"""Bind selected fallback bytes along Fine allowlist -> High -> coefficient registry.

The output is an installation candidate and source provenance check; no
Lean compilation or claim about untraversed dependencies is made.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
DEST = Path(__file__).resolve().parent
BASE = 'docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor_finite_policy/'
FINE = 'docs/source-only/20261112-resume/t03/T01_FINE_COFINAL_ALLOWLIST.json'
HIGH = BASE + 'HIGH_PP_REGISTRY.json'
COEFF = BASE + 'COEFFICIENT_REGISTRY.json'
PREV = 'docs/source-only/20261119-p4a5-hdensity-install-r2/'

def data(path):
    return (ROOT / path).read_bytes()
def sha(b):
    return hashlib.sha256(b).hexdigest()
def js(path):
    return json.loads(data(path))
def imports(b):
    ans=[]
    for line in b.decode().splitlines():
        m=re.match(r'^\s*import\s+([A-Za-z0-9_\. ]+)',line)
        if m: ans.extend(m.group(1).split())
    return ans

def main():
    hd_path='docs/source-only/20261112-resume/t01/FINAL_HDENSITY_REGISTRY.json'
    fine_path='docs/source-only/20261112-resume/t01/FINAL_FINE_REGISTRY.json'
    candidate='docs/source-only/20261112-resume/t01/P4AOriginalFiniteAll22FineDensity.lean'
    hd=js(hd_path); fine_registry=js(fine_path)
    if sha(data(candidate))!=hd['new_source']['sha256']:
        raise ValueError('hdensity candidate hash mismatch')
    if sha(data(fine_path))!=hd['fine_predecessor_registry']['sha256']:
        raise ValueError('hdensity -> fine registry hash mismatch')
    if sha(data(FINE))!=fine_registry['independent_allowlist']['sha256']:
        raise ValueError('fine registry -> fine allowlist hash mismatch')
    fine=js(FINE); high=js(HIGH); coeff=js(COEFF)
    if sha(data(HIGH))!=fine['existing_high_author_record']['sha256']:
        raise ValueError('Fine -> HIGH_PP_REGISTRY hash mismatch')
    if sha(data(COEFF))!=high['coefficientRegisterSHA256']:
        raise ValueError('HIGH_PP_REGISTRY -> COEFFICIENT_REGISTRY hash mismatch')
    if len(coeff['sources'])!=32:raise ValueError('unexpected coefficient registry size')
    high_by_name={x['source']:x for x in high['sources']}
    high_evidence=[]
    for rec in fine['existing_high_sources_reached_within_that_record']:
        name=Path(rec['installation_target']).name
        h=high_by_name[name]
        b=data(BASE+name)
        if sha(b)!=rec['sha256'] or sha(b)!=h['sha256'] or len(b)!=h['bytes']:
            raise ValueError('high source identity mismatch: '+name)
        actual=imports(b)
        if actual!=rec['imports'] or actual!=h['imports']:
            raise ValueError('high import mismatch: '+name)
        high_evidence.append({'module':'ImbalancedChen.'+name[:-5], 'path':BASE+name,
                              'sha256':sha(b),'imports':actual})
    prev=js(PREV+'INSTALL_MANIFEST.json'); audit=js(PREV+'IMPORT_AUDIT.json')
    by_target={r['target']:r for r in prev['records']}
    coeff_evidence=[];updated=added=0
    for rec in coeff['sources']:
        name=rec['source']; src=BASE+name; target='ImbalancedChen/'+name
        b=data(src)
        if sha(b)!=rec['sha256'] or len(b)!=rec['bytes']:
            raise ValueError('coefficient source mismatch: '+name)
        module='ImbalancedChen.'+name[:-5]
        current=by_target.get(target)
        was_missing=module in audit['missing_project_modules']
        if current:
            if current['sha256']!=rec['sha256'] or sha(data(current['source']))!=rec['sha256']:
                raise ValueError('existing staged source mismatch: '+name)
            if 'selection' in current:
                del current['selection']; updated+=1
            current['hash_registry']=COEFF
            current['selection_evidence']='Fine allowlist -> HIGH_PP_REGISTRY -> COEFFICIENT_REGISTRY; exact name, size, SHA-256; SOURCE_ONLY'
        elif was_missing:
            current={'source':src,'target':target,'sha256':rec['sha256'],'hash_registry':COEFF,
                     'selection_evidence':'Fine allowlist -> HIGH_PP_REGISTRY -> COEFFICIENT_REGISTRY; exact name, size, SHA-256; SOURCE_ONLY'}
            prev['records'].append(current);by_target[target]=current;added+=1
        coeff_evidence.append({'module':module,'path':src,'sha256':rec['sha256'],
              'bytes':len(b),'imports':imports(b),'previously_missing':was_missing,
              'staged_now':current is not None})
    # Close dependencies *within this exact coefficient registry*. This
    # does not pretend to close imports outside it or resolve other variants.
    coeff_by_module={e['module']:e for e in coeff_evidence}
    changed=True
    while changed:
        changed=False
        for entry in coeff_evidence:
            if not entry['staged_now']:
                continue
            for module in entry['imports']:
                sub=coeff_by_module.get(module)
                if sub is None or sub['staged_now']:
                    continue
                target='ImbalancedChen/'+module.rsplit('.',1)[-1]+'.lean'
                if (ROOT/target).is_file():
                    continue
                record={'source':sub['path'],'target':target,'sha256':sub['sha256'],
                        'hash_registry':COEFF,
                        'selection_evidence':'actual import within chained COEFFICIENT_REGISTRY; exact name, size, SHA-256; SOURCE_ONLY'}
                prev['records'].append(record);by_target[target]=record
                sub['staged_now']=True;added+=1;changed=True
    prev['baseline']='c98d1fe0797a32e3409de801d4413916be39ee65'
    prev['scope']='partial source staging; chained fallback registry evidence only; not transitive closure or compilation'
    evidence={'hdensity_registry':hd_path,'hdensity_registry_sha256':sha(data(hd_path)),
      'fine_registry':fine_path,'fine_registry_sha256':sha(data(fine_path)),
      'candidate':candidate,'candidate_sha256':sha(data(candidate)),
      'fine_allowlist':FINE,'fine_allowlist_sha256':sha(data(FINE)),
      'high_registry':HIGH,'high_registry_sha256':sha(data(HIGH)),
      'coefficient_registry':COEFF,'coefficient_registry_sha256':sha(data(COEFF)),
      'scope':'selected source bytes and literal imports only; no elaboration',
      'prior_provisional_entries_bound':updated,'newly_staged_reachable_coefficient_modules':added,
      'high_reached':high_evidence,'coefficient_entries':coeff_evidence}
    (DEST/'INSTALL_MANIFEST.json').write_text(json.dumps(prev,indent=2,ensure_ascii=False)+'\n')
    (DEST/'FALLBACK_EVIDENCE.json').write_text(json.dumps(evidence,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'high_checked':len(high_evidence),'coefficient_checked':len(coeff_evidence),
                      'previous_provisional_bound':updated,'new_reachable_staged':added}))
if __name__=='__main__':main()
