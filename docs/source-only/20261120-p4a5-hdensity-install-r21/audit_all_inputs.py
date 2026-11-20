#!/usr/bin/env python3
"""Rehash all 357 registered physical files together, without parsing them."""
import argparse,hashlib,json,os
from pathlib import Path
HERE=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--lean',type=Path,required=True);args=ap.parse_args();lean=args.lean.resolve(strict=True);base=lean.parent;items=[]
for name in ['WITNESS_INSTALLED.json','SAVING19_INSTALLED.json','OLD16_INSTALLED.json']:
 doc=json.loads((HERE/name).read_bytes())
 for x in doc['witnesses']:items.append((name,lean/x['install_path'],x['bytes'],x['expected_sha256']))
for x in json.loads((HERE/'SIXTH_INSTALLED.json').read_bytes())['rows']:
 items.append(('SIXTH_INSTALLED.json',base/'tmp/publication-20261010/verification-renewal-v2/_runs/full-final'/x['name'],x['size'],x['expected_sha256']))
for x in json.loads((HERE/'G3_INSTALLED.json').read_bytes())['rows']:
 items.append(('G3_INSTALLED.json',lean/'ImbalancedChen'/x['target'],x['bytes'],x['sha256']))
assert len(items)==357;rows=[];seen=set()
for group,path,size,expected in items:
 assert not path.is_symlink();path=path.resolve(strict=True);assert path.is_relative_to(base) and path not in seen;seen.add(path);assert path.is_file() and path.stat().st_size==size
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 got=h.hexdigest();assert got==expected,(group,path)
 rows.append({'group':group,'path_from_work_root':str(path.relative_to(base)),'bytes':size,'sha256':got})
print(json.dumps({'scope':'357 distinct input byte identities, not data evaluation or complete IO proof','files':len(rows),'total_bytes':sum(x['bytes'] for x in rows),'rows':rows},indent=2))
