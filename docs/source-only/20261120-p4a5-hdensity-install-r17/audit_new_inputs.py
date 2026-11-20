#!/usr/bin/env python3
"""Bind three reached loaders to original recorded data; do not evaluate it."""
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
assert sha(HERE/'IMPORT_AUDIT.json')=='6563319f8c49429aabc820d4048c23a28f09834f9cf7077991a7a8fd832d6cdc'
a=json.loads((HERE/'IMPORT_AUDIT.json').read_text());m=json.loads(MANIFEST.read_text())
ap=argparse.ArgumentParser();ap.add_argument('stage',type=Path);args=ap.parse_args();stage=args.stage.resolve(strict=True)
ns=['P2OriginalSaving16OriginalArchive','P4AOriginalSavedSixthArchive','P5OriginalFourthFifthSourceInputs'];txt={}
for n in ns:
 mod='ImbalancedChen.'+n;p=stage/'ImbalancedChen'/(n+'.lean');assert sha(p)==a['visited'][mod]['sha256']
 choices=[x for x in m['files'] if x.get('module')==mod];assert len(choices)==1 and choices[0]['sha256']==sha(p)
 txt[n]=p.read_text()
s=txt[ns[0]];assert '../goldbach-research/eighth-prefix-family-20261009-cell-' in s
ids=set(range(15))-{7};assert set(map(int,re.findall(r'originalSaving16Text%\s+(\d+)',s)))==ids
wanted={ns[0]:['../goldbach-research/eighth-prefix-family-20261009-cell-'+f'{i:02}'+'.witness.json' for i in sorted(ids)],
 ns[1]:['ImbalancedChen/provenance/OriginalSixthCells.npy'],
 ns[2]:['ImbalancedChen/provenance/original-fourth/FourthRows17LE.bin']}
assert 'include_original_sixth_bytes% "provenance/OriginalSixthCells.npy"' in txt[ns[1]]
assert 'include_original_fourth_bytes% "provenance/original-fourth/FourthRows17LE.bin"' in txt[ns[2]]
lookup={v['install_path']:v for v in m['data_inputs']};assert len(lookup)==len(m['data_inputs'])
rows=[]
for n in ns:
 mod='ImbalancedChen.'+n
 for name in wanted[n]:
  x=lookup[name];assert x.get('consuming_module')==mod or mod in x.get('consumed_by',[])
  path=(stage/name).resolve();exists=path.is_file();actual=sha(path) if exists else None
  rows.append({'consumer':mod,'install_path':name,'bytes':x['bytes'],'expected_sha256':x['sha256'],
   'git_blob_sha1':x.get('git_blob_sha1'),'origin':x['origin'],
   'status':'missing' if not exists else ('match' if actual==x['sha256'] and path.stat().st_size==x['bytes'] else 'mismatch'),
   'actual_sha256':actual})
assert len(rows)==16 and len({x['install_path'] for x in rows})==16
print(json.dumps({'scope':'three hash-matched reached loaders and 16 T06 original data records; not exhaustive or evaluated',
 'cwd_assumption':'isolated stage root; binaries source-relative',
 'manifest_sha256':'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9',
 'consumer_counts':dict(Counter(x['consumer'] for x in rows)),
 'status_counts':dict(Counter(x['status'] for x in rows)),
 'total_registered_bytes':sum(x['bytes'] for x in rows),'witnesses':rows},indent=2))
