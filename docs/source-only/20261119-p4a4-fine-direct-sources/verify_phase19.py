"""Verify recorded source bytes and simple witness markers, not Lean proofs."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--registry',type=Path,required=True);p.add_argument('--source-root',type=Path,required=True);a=p.parse_args()
j=json.loads(a.registry.read_text());assert j['schema']=='p4a4-fine-witness-changed-phase19-v1'
for r in j['prior_source_identities']+[j['new_candidate']]:
 f=a.source_root.joinpath(*r['module'].split('.')).with_suffix('.lean');b=f.read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
 if r['module'].endswith('FineWitnessChangedSupport'):
  t=b.decode();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',t)
  for marker in ['theorem fine_witness_all_changed_seen','∀ (tags : ℕ → List Bool) (x : ℕ)','P4AOriginalFiniteFallbackActualChangedSupport.actual_changed_seen']:
   assert marker in t
print('verified_source_files',len(j['prior_source_identities'])+1)
print('Lean_elaboration_or_kernel',False)
