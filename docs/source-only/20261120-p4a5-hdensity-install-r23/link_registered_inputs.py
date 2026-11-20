#!/usr/bin/env python3
"""Link already audited inputs into a separate task tree without copying bytes.

Hard links share inodes: both trees must be treated as read-only input data.
"""
import argparse,hashlib,json,os
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];audit=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r21/ALL_INPUTS_REAUDIT.json';rows=json.loads(audit.read_bytes())['rows'];assert len(rows)==357
ap=argparse.ArgumentParser();ap.add_argument('--source-work',type=Path,required=True);ap.add_argument('--destination-work',type=Path,required=True);args=ap.parse_args();src=args.source_work.resolve(strict=True);dst=args.destination_work.resolve(strict=True);assert src!=dst and ROOT not in src.parents and ROOT not in dst.parents and src not in dst.parents and dst not in src.parents
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
items=[];seen=set()
for r in rows:
 rel=Path(r['path_from_work_root']);assert not rel.is_absolute() and '..' not in rel.parts and rel not in seen;seen.add(rel)
 a=src/rel;b=dst/rel;assert not a.is_symlink() and a.resolve(strict=True).is_relative_to(src) and a.is_file() and a.stat().st_size==r['bytes'] and sha(a)==r['sha256'];assert not b.exists() and not b.is_symlink();items.append((r,a,b))
assert len(items)==357 and src.stat().st_dev==dst.stat().st_dev
out=[]
for r,a,b in items:
 b.parent.mkdir(parents=True,exist_ok=True);assert b.parent.resolve().is_relative_to(dst);os.link(a,b);assert os.path.samefile(a,b) and b.stat().st_size==r['bytes'] and sha(b)==r['sha256'];out.append({'group':r['group'],'path_from_work_root':r['path_from_work_root'],'bytes':r['bytes'],'sha256':r['sha256'],'same_inode_as_previous':True})
print(json.dumps({'scope':'hard-linked read-only source inputs; no computation; source and destination share data inodes','source_work':str(src),'destination_work':str(dst),'count':len(out),'bytes':sum(x['bytes'] for x in out),'files':out},indent=2))
