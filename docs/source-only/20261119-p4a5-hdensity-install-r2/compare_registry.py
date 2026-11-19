#!/usr/bin/env python3
"""Compare the previous partial packet with a separately scoped registry.

Same hashes corroborate bytes only; they do not prove common dependency
semantics, elaborate Lean, or authorize importing the other whole packet.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
P = 'docs/source-only/'
def read(path):
    return json.loads((ROOT / path).read_text())
def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    prev = read(P+'20261119-p4a5-hdensity-install/INSTALL_MANIFEST.json')
    selection_path = P+'20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
    other = read(selection_path)
    index = {entry['module']:entry for entry in other['files']}
    comparisons=[]
    for entry in prev['records']:
        if 'selection' not in entry: continue
        module=entry['target'][:-5].replace('/','.')
        candidate=index.get(module)
        state='not_in_other_manifest' if not candidate else ('equal' if candidate['sha256']==entry['sha256'] else 'different')
        comparisons.append({'module':module,'old_sha256':entry['sha256'],'comparison':state,
                            'other_sha256':candidate.get('sha256') if candidate else None,
                            'other_origin':candidate.get('origin') if candidate else None})
    comparison_path=P+'20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/CORE_SELECTION_BYTE_COMPARISON.json'
    byte_comparison=read(comparison_path)
    rec=next(x for x in byte_comparison['changed_bytes'] if x['module']=='ImbalancedChen.P4AOriginalFull87SavedGain')
    path=P+'20261110-yellow-closure-10t/t03_saved87_actual_gain/P4AOriginalFull87SavedGain.lean'
    data=(ROOT/path).read_bytes()
    if sha(data)!=rec['authority_sha256']: raise ValueError('authority hash mismatch')
    for op in rec['transform']:
        old,new=op['old'].encode(),op['new'].encode()
        if data.count(old)!=op['count']: raise ValueError('transform count mismatch')
        data=data.replace(old,new)
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    expected=index[rec['module']]
    if sha(data)!=rec['selected_sha256'] or blob!=expected['git_blob_sha1']:
        raise ValueError('transformed variant hash/blob mismatch')
    print(json.dumps({'comparison_scope':'other manifest is source-only and has a different target; no P4A.5 compatibility inferred',
       'other_manifest':selection_path,'other_manifest_sha256':sha((ROOT/selection_path).read_bytes()),
       'compared_old_provisional_count':len(comparisons),'counts':dict(Counter(x['comparison'] for x in comparisons)),
       'comparisons':comparisons,
       'recorded_transform':{'registry':comparison_path,'registry_sha256':sha((ROOT/comparison_path).read_bytes()),
        'source':path,'authority_sha256':rec['authority_sha256'],'operations':rec['transform'],
        'transformed_sha256':sha(data),'transformed_git_blob':blob,
        'status':'hash match only; no elaboration and no variant substituted'}},indent=2,sort_keys=True))
if __name__=='__main__':main()
