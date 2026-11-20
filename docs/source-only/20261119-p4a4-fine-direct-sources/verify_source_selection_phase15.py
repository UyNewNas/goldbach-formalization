"""Verify bytes of the selected source packet; not a Lean compiler."""
import argparse, hashlib, json
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--selection',type=Path,required=True)
p.add_argument('--source-root',type=Path,required=True)
a=p.parse_args()
j=json.loads(a.selection.read_text())
assert j['schema']=='p4a4-source-closure-phase15-v1'
for r in j['source_rows']:
    file=a.source_root.joinpath(*r['module'].split('.')).with_suffix('.lean')
    data=file.read_bytes()
    assert len(data)==r['bytes'],r['module']
    assert hashlib.sha256(data).hexdigest()==r['sha256'],r['module']
    assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==r['git_blob'],r['module']
print('verified_selected_sources',len(j['source_rows']))
print('compiler_or_kernel_check',False)
