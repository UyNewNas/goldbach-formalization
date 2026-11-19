#!/usr/bin/env python3
"""Bind the reached Saving19 loader's exact 26 original files; no evaluation."""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
MANIFEST=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
assert sha(MANIFEST)=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9'
assert sha(HERE/'IMPORT_AUDIT.json')=='7114b4ab2c0284950265f98902afc1e213fd80c081f73fc59d4e1949bc5cfed3'
a=json.loads((HERE/'IMPORT_AUDIT.json').read_text());m=json.loads(MANIFEST.read_text())
ap=argparse.ArgumentParser();ap.add_argument('stage',type=Path);args=ap.parse_args();stage=args.stage.resolve(strict=True)
mod='ImbalancedChen.P2OriginalSaving19Archive';src=stage/'ImbalancedChen/P2OriginalSaving19Archive.lean'
assert sha(src)==a['visited'][mod]['sha256']=='b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6'
x=[v for v in m['files'] if v['module']==mod];assert len(x)==1 and x[0]['sha256']==sha(src)
s=src.read_text();assert '../goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-' in s
assert '../goldbach-research/eighth-third-moment-refinement-20261009-a23-low-' in s
for name in ('originalGeometryText','originalMomentText'):
 assert set(map(int,re.findall(name+r'%\s+(\d+)',s)))==set(range(13))
names=['../goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-'+f'{i:02}'+'-cell.witness.json' for i in range(13)]
names+=['../goldbach-research/eighth-third-moment-refinement-20261009-a23-low-'+f'{i:02}'+'.witness.json' for i in range(13)]
lookup={v['install_path']:v for v in m['data_inputs']};assert len(lookup)==len(m['data_inputs'])
rows=[]
for name in names:
 item=lookup[name];assert item.get('consuming_module')==mod or mod in item.get('consumed_by',[])
 path=(stage/name).resolve();ok=path.is_file();actual=sha(path) if ok else None
 rows.append({'consumer':mod,'install_path':name,'bytes':item['bytes'],'expected_sha256':item['sha256'],
              'origin':item['origin'],'status':'missing' if not ok else ('match' if actual==item['sha256'] and path.stat().st_size==item['bytes'] else 'mismatch'),'actual_sha256':actual})
assert len(rows)==26 and len({x['install_path'] for x in rows})==26
print(json.dumps({'scope':'exact reached loader and 26 T06 original witness records; no Lean proof execution',
 'cwd_assumption':'isolated stage root','source_sha256':sha(src),'manifest_sha256':'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9',
 'status_counts':dict(Counter(x['status'] for x in rows)),'total_registered_bytes':sum(x['bytes'] for x in rows),'witnesses':rows},indent=2))
