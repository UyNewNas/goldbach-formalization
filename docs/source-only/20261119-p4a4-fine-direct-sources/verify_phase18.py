"""Verify recorded source identities and candidate syntax markers only."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--registry',type=Path,required=True);p.add_argument('--source-root',type=Path,required=True);a=p.parse_args()
j=json.loads(a.registry.read_text());assert j['schema']=='p4a4-actual-changed-transport-phase18-v1'
rows=j['prior_packet_inputs']+j['registered_dependencies']+[j['new_candidate']]
for r in rows:
 path=a.source_root.joinpath(*r['module'].split('.')).with_suffix('.lean');b=path.read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
 if r['module'].endswith('ActualChangedSupport'):
  text=b.decode();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b',text)
  for s in ['theorem actual_changed_seen','changed (F T delta n D omega N) tags','P4AOriginalFiniteFallbackProjection.support_cut','P4AOriginalFiniteFallbackWallRate.changed_seen']:
   assert s in text
print('verified_source_files',len(rows));print('Lean_elaboration_or_kernel',False)
