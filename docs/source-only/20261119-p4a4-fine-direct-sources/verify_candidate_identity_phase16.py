"""Check candidate byte identities only; does not compile Lean."""
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--receipt',type=Path,required=True)
p.add_argument('--source-root',type=Path,required=True)
a=p.parse_args();j=json.loads(a.receipt.read_text())
assert j['schema']=='p4a4-conditional-source-identity-phase16-v1'
for r in j['candidate_rows']:
 f=a.source_root.joinpath(*r['module'].split('.')).with_suffix('.lean')
 b=f.read_bytes(); assert len(b)==r['bytes']
 assert hashlib.sha256(b).hexdigest()==r['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
print('verified_candidate_sources',len(j['candidate_rows']))
print('Lean_compile_or_kernel_replay',False)
