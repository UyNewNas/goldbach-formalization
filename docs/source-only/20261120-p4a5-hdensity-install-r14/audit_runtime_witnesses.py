#!/usr/bin/env python3
"""Match five actual loaders and their literal witness names to frozen metadata.

This is not an exhaustive Lean IO scan, certificate verification, or compilation.
"""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
PREV=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r13'
MANIFEST=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
G6=ROOT/'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G6_RELEASE_INPUT_REUSE.json'
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
assert sha(MANIFEST)=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9'
assert sha(G6)=='0bf1b3a39e43f73332c434b2fa4378cb0d1defa42dc3a437e6338948be87fe1d'
assert sha(PREV/'IMPORT_AUDIT.json')=='2bba8ecc78267049b022a57503a0557bfcc1d616c902ab4f6265ac6a9adc0b08'
a=json.loads((PREV/'IMPORT_AUDIT.json').read_text());m=json.loads(MANIFEST.read_text());g6=json.loads(G6.read_text())
ap=argparse.ArgumentParser();ap.add_argument('stage',type=Path);args=ap.parse_args();stage=args.stage.resolve(strict=True)
base='ImbalancedChen.'
names=['P2OriginalSaving15RadialArchive','P2OriginalSaving17DescendingArchive','P2OriginalSaving18UnequalArchive','P2OriginalSaving20FirstFailureIntegral','P4AOriginalThirdFallbackArchive']
texts={}
for n in names:
 mod=base+n; src=stage/'ImbalancedChen'/(n+'.lean');entry=a['visited'][mod]
 assert sha(src)==entry['sha256']
 selected=[x for x in m['files'] if x.get('module')==mod or x.get('install_path')=='ImbalancedChen/'+n+'.lean']
 assert len(selected)==1 and selected[0]['sha256']==entry['sha256']
 texts[n]=src.read_text()
assert '../goldbach-research/eighth-radial-reduction-20261009.witness.json' in texts[names[0]]
wanted={names[0]:['../goldbach-research/eighth-radial-reduction-20261009.witness.json']}
t=texts[names[1]];assert '../goldbach-research/eighth-prefix-family-20261009-descending-cell-' in t
assert set(map(int,re.findall(r'originalSaving17Text%\s+(\d+)',t)))==set(range(15))
wanted[names[1]]=[f'../goldbach-research/eighth-prefix-family-20261009-descending-cell-{i:02}.witness.json' for i in range(15)]
t=texts[names[2]];assert '"../goldbach-research/" ++ nm.getString' in t
s=re.findall(r'originalUnequalText%[ \t]+"([^"/\r\n]+)"',t);assert len(s)==30 and len(set(s))==30
wanted[names[2]]=['../goldbach-research/'+x for x in s]
t=texts[names[3]]
assert '../goldbach-research/eighth-history-first-failure-20261009-' in t and '../goldbach-research/eighth-history-moment-refinement-20261009-' in t
for macro in ('originalSaving20GeometryText','originalSaving20MomentText'):
 assert set(map(int,re.findall(macro+r'%\s+(\d+)',t)))==set(range(29))
labels=[f'h3-{i:02}' for i in range(12)]+[f'h5-{i:02}' for i in range(7)]+[f'h7-{i:02}' for i in range(10)]
wanted[names[3]]=['../goldbach-research/eighth-history-first-failure-20261009-'+s+'-cell.witness.json' for s in labels]+['../goldbach-research/eighth-history-moment-refinement-20261009-'+s+'.witness.json' for s in labels]
assert 'source.withFileName "G6_ORIGINAL_WITNESS.json"' in texts[names[4]]
wanted[names[4]]=['ImbalancedChen/G6_ORIGINAL_WITNESS.json']
by_path={x['install_path']:x for x in m['data_inputs']};assert len(by_path)==len(m['data_inputs'])
rows=[]
for n in names:
 mod=base+n
 for path in wanted[n]:
  item=by_path[path];consumers=item.get('consumed_by',[])
  assert item.get('consuming_module')==mod or mod in consumers
  if n==names[4]:assert (item['sha256'],item['bytes'])==(g6['sha256'],g6['bytes'])
  actual=(stage/path).resolve();exists=actual.is_file()
  actual_sha=sha(actual) if exists else None
  rows.append({'consumer':mod,'install_path':path,'bytes':item['bytes'],'expected_sha256':item['sha256'],
   'origin':item.get('origin'),'status':'missing' if not exists else ('match' if actual_sha==item['sha256'] and actual.stat().st_size==item['bytes'] else 'mismatch'),
   'actual_sha256':actual_sha})
assert len(rows)==105 and len({x['install_path'] for x in rows})==105
print(json.dumps({'scope':'five hash-matched source loaders and frozen T06 v3 data records; source-only, not exhaustive nor evaluated',
 'cwd_assumption':'isolated stage root; G6 uses actual source directory',
 'manifest_sha256':'21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9',
 'consumer_counts':dict(Counter(x['consumer'] for x in rows)),
 'status_counts':dict(Counter(x['status'] for x in rows)),
 'total_registered_bytes':sum(x['bytes'] for x in rows),'witnesses':rows},indent=2))
