#!/usr/bin/env python3
"""Reproduce a partial source tree by merging exact stage + checkout files.

No packages, .olean, other fixtures or proof execution are supplied.
"""
import argparse
import hashlib
import json
import shutil
from collections import Counter
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
PREV=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r23'
EXPECTED_AUDIT='6ea4691bc6820ec42e837792dd48e6ff9a8c1e86d7c5a98bc4748959d49362dd'
CONFIG={'lean-toolchain':'62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef',
 'lakefile.toml':'b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254',
 'lake-manifest.json':'35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849'}
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
 return h.hexdigest()
ap=argparse.ArgumentParser();ap.add_argument('--stage',type=Path,required=True);ap.add_argument('--destination',type=Path,required=True);args=ap.parse_args()
stage=args.stage.resolve(strict=True);dest=args.destination.resolve()
assert dest!=ROOT and ROOT not in dest.parents and dest!=stage and stage not in dest.parents and dest not in stage.parents
assert not dest.exists() or not any(dest.iterdir()),'destination must be empty'
audit=PREV/'IMPORT_AUDIT.json';assert sha(audit)==EXPECTED_AUDIT
j=json.loads(audit.read_text());assert len(j['visited'])==1806
items=[]
for module,entry in sorted(j['visited'].items()):
 target=Path(*module.split('.')).with_suffix('.lean')
 assert str(target)==entry['path'] and entry['origin'] in ('stage','checkout')
 origin=(stage if entry['origin']=='stage' else ROOT)/target
 assert origin.is_file() and sha(origin)==entry['sha256'],str(origin)
 items.append((origin,target,entry['sha256'],entry['origin']))
for name,h in CONFIG.items():
 path=ROOT/name;assert sha(path)==h;items.append((path,Path(name),h,'configuration'))
dest.mkdir(parents=True,exist_ok=True)
for origin,target,h,_ in items:
 out=dest/target;out.parent.mkdir(parents=True,exist_ok=True)
 assert not out.exists();shutil.copyfile(origin,out);assert sha(out)==h,str(out)
print(json.dumps({'scope':'exact reachable source bytes and declared configuration only; not import/data closure or Lean verification',
 'source_audit_sha256':EXPECTED_AUDIT,'source_count':len(j['visited']),
 'source_origins':dict(Counter(x[3] for x in items if x[3]!='configuration')),
 'config_sha256':CONFIG,'project_missing_count':len(j['missing_project_modules']),
 'external_import_count':len(j['external_modules']),'packages_installed':False,
 'olean_created':False,'certificates_evaluated':False},indent=2))
