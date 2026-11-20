"""Check source bytes against recorded manifest selection; not Lean compilation."""
import argparse,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--selection',type=Path,required=True);p.add_argument('--source-root',type=Path,required=True);a=p.parse_args()
j=json.loads(a.selection.read_text());assert j['schema']=='p4a4-selected-dependency-identities-phase17-v1'
for r in j['source_rows']:
 f=a.source_root.joinpath(*r['module'].split('.')).with_suffix('.lean');b=f.read_bytes()
 assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'] and hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
 assert re.findall(r'^import\s+(\S+)',b.decode(),re.M)==r['direct_imports']
print('verified selected source files',len(j['source_rows']))
print('Lean compiler or kernel check',False)
