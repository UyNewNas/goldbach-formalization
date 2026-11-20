#!/usr/bin/env python3
"""Inventory line-leading resource options in the literal reachable source set.

Textual audit only: no Lean parsing, evaluation, proof or runtime-limit changes.
"""
import argparse
import hashlib
import json
import re
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('stage',type=Path);args=ap.parse_args()
stage=args.stage.resolve(strict=True)
a=json.loads((HERE/'IMPORT_AUDIT.json').read_text())
pat=re.compile(r'^\s*set_option\s+(maxHeartbeats|maxRecDepth)\s+([0-9]+)(?:\s+(in))?\s*(?:--.*)?$')
files=[];totals=Counter()
for name,x in sorted(a['visited'].items()):
 src=(stage if x['origin']=='stage' else ROOT)/x['path']
 data=src.read_bytes();assert hashlib.sha256(data).hexdigest()==x['sha256'],str(src)
 hits=[]
 for i,line in enumerate(data.decode('utf-8').splitlines(),1):
  m=pat.match(line)
  if m:
   opt,num,scope=m.groups();num=int(num)
   hits.append({'line':i,'option':opt,'value':num,'local_in':scope=='in'})
   totals[opt+':'+str(num)]+=1
 if hits:files.append({'module':name,'origin':x['origin'],'path':x['path'],'sha256':x['sha256'],'hits':hits})
print(json.dumps({'scope':'line-leading textual options in literal reachable sources; comments not lexed, other forms may be missed; no options executed',
 'files_with_hits':len(files),'hit_count':sum(totals.values()),'option_counts':dict(sorted(totals.items())),
 'files':files},indent=2))
