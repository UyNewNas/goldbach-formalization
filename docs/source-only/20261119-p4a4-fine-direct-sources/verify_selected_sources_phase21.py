"""Check the selected source bytes against the frozen manifest receipt."""
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser()
p.add_argument('--selection',type=Path,required=True)
p.add_argument('--lean-root',type=Path,required=True)
a=p.parse_args()
j=json.loads(a.selection.read_text())
assert len(j['rows']) == 4
for r in j['rows']:
    b=(a.lean_root/(r['module'].split('.')[-1]+'.lean')).read_bytes()
    assert len(b)==r['bytes']
    assert hashlib.sha256(b).hexdigest()==r['sha256']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
    assert len(r['same_origin_refs'])==3 and all(x['match'] and x['blob']==r['git_blob'] for x in r['same_origin_refs'])
print('manifest_selected_source_blobs_verified',len(j['rows']))
print('recorded_same_origin_ref_matches',sum(len(r['same_origin_refs']) for r in j['rows']))
print('lean_elaboration_or_kernel',False)
