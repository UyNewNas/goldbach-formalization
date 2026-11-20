#!/usr/bin/env python3
"""Stage two byte-identical local recorded inputs; no numerical evaluation."""
import argparse
import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path, PurePosixPath
ROOT=Path(__file__).resolve().parents[3]
HERE=Path(__file__).resolve().parent
BEFORE=HERE/'NEW_INPUTS_BEFORE.json'
MANIFEST=ROOT/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3/EXACT_INSTALL_MANIFEST.json'
def hashes(path):
 h=hashlib.sha256();g=hashlib.sha1();g.update(b'blob '+str(path.stat().st_size).encode()+b'\0')
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b);g.update(b)
 return h.hexdigest(),g.hexdigest()
assert hashes(BEFORE)[0]=='a70818a6d4dd6c86bc5e58b00d6e845b9c85669725bd513f162ba663a426ce01'
assert hashes(MANIFEST)[0]=='21ee9d56c5891d6929e4ce1be045a21e6adbda0c372af7bc9a84575b113ff3c9'
a=json.loads(BEFORE.read_text());m=json.loads(MANIFEST.read_text());lookup={x['install_path']:x for x in m['data_inputs']}
ap=argparse.ArgumentParser();ap.add_argument('stage',type=Path);args=ap.parse_args();stage=args.stage.resolve(strict=True)
assert stage!=ROOT and ROOT not in stage.parents
names=['ImbalancedChen/provenance/OriginalSixthCells.npy','ImbalancedChen/provenance/original-fourth/FourthRows17LE.bin']
items=[]
for name in names:
 row=next(x for x in a['witnesses'] if x['install_path']==name);v=lookup[name]
 assert row['origin']['kind']=='git' and row['origin']==v['origin']
 assert (row['bytes'],row['expected_sha256'],row['git_blob_sha1'])==(v['bytes'],v['sha256'],v['git_blob_sha1'])
 sourcepath=PurePosixPath(row['origin']['path']);destpath=PurePosixPath(name)
 assert not sourcepath.is_absolute() and '..' not in sourcepath.parts and not destpath.is_absolute() and '..' not in destpath.parts
 src=ROOT/str(sourcepath);target=stage/str(destpath)
 assert src.is_file() and src.stat().st_size==v['bytes'] and hashes(src)==(v['sha256'],v['git_blob_sha1'])
 assert not target.is_symlink() and not target.parent.is_symlink()
 if target.exists():assert target.is_file() and target.stat().st_size==v['bytes'] and hashes(target)==(v['sha256'],v['git_blob_sha1'])
 items.append((row,src,target))
for row,src,target in items:
 if target.exists():continue
 target.parent.mkdir(parents=True,exist_ok=True);assert not target.parent.is_symlink()
 fd,tmp=tempfile.mkstemp(prefix='.original-',dir=target.parent);os.close(fd)
 try:
  shutil.copyfile(src,tmp)
  assert Path(tmp).stat().st_size==row['bytes'] and hashes(Path(tmp))==(row['expected_sha256'],row['git_blob_sha1'])
  os.replace(tmp,target)
 finally:
  if os.path.exists(tmp):os.unlink(tmp)
print(json.dumps({'scope':'local source and staged binary byte identity only; recorded origin commit tree not verified; no Lean execution',
 'count':len(items),'bytes':sum(x[0]['bytes'] for x in items),
 'inputs':[{'path':row['install_path'],'source':str(src.relative_to(ROOT)),
 'sha256':row['expected_sha256'],'git_blob_sha1':row['git_blob_sha1'],'bytes':row['bytes'],
 'recorded_origin':row['origin']} for row,src,_ in items]},indent=2))
