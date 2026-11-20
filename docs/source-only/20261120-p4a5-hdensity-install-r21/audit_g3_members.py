#!/usr/bin/env python3
"""Independently rehash the 188 registered G3 members, without evaluation."""
import argparse,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];p=ROOT/'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/G3_FIXTURES.json';raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()=='f79c794c614af8b4aec78ca4601f9b6e6d58f3e47d72b72eac98f94003cca184'
ap=argparse.ArgumentParser();ap.add_argument('lean',type=Path);a=ap.parse_args();lean=a.lean.resolve(strict=True);loader=lean/'ImbalancedChen/P4AOriginalNewFifthArchiveData.lean';assert hashlib.sha256(loader.read_bytes()).hexdigest()=='5fc51f4622c04ff0d2ce69d87e19d7b0a1cb20ccd48295309e24aab6a4879df4';rows=[]
for block in json.loads(raw)['blocks']:
 for m in block['members']:
  rel=Path(m['staged']);assert len(rel.parts)==2 and rel.parts[0]=='g3-fixtures';file=lean/'ImbalancedChen'/rel;assert file.is_file() and not file.is_symlink();h=hashlib.sha256()
  with file.open('rb') as f:
   for b in iter(lambda:f.read(1048576),b''):h.update(b)
  got=h.hexdigest();assert got==m['sha256'] and file.stat().st_size==m['bytes'];rows.append({'target':str(rel),'sha256':got,'bytes':m['bytes'],'source_npz':block['input_original']})
assert len(rows)==188 and len({x['target'] for x in rows})==188
print(json.dumps({'scope':'independent input byte rehash only; not a finite certificate','count':len(rows),'total_bytes':sum(x['bytes'] for x in rows),'rows':rows},indent=2))
