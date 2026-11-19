#!/usr/bin/env python3
"""Stage the 188 original G3 NPY members only after exact SHA-256 checks.

No mathematical certificate is evaluated. This tool does not download data.
"""
import argparse,hashlib,json,os,shutil,stat,tempfile,zipfile
from pathlib import Path,PurePosixPath
ROOT=Path(__file__).resolve().parents[3]
EVIDENCE=Path(__file__).with_name('G3_EVIDENCE.json')
def digest_stream(f):
 h=hashlib.sha256(); size=0
 while True:
  b=f.read(1024*1024)
  if not b:break
  h.update(b);size+=len(b)
 return h.hexdigest(),size

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--archive',required=True,type=Path);ap.add_argument('--stage',required=True,type=Path);a=ap.parse_args()
 e=json.loads(EVIDENCE.read_text());stage=a.stage.resolve();module=stage/'ImbalancedChen'/'P4AOriginalNewFifthArchiveData.lean'
 if not module.is_file():raise ValueError('stage must contain the selected Data module')
 with module.open('rb') as f: h,_=digest_stream(f)
 if h!=e['data_source_sha256']:raise ValueError('staged Data source SHA-256 mismatch')
 manifest=ROOT/e['fixture_manifest']
 with manifest.open('rb') as f:h,_=digest_stream(f)
 if h!=e['fixture_manifest_sha256']:raise ValueError('fixture manifest SHA-256 mismatch')
 if not a.archive.is_file():raise ValueError('G3_INPUTS.zip not found')
 with a.archive.open('rb') as f: zsha,zsize=digest_stream(f)
 if zsha!=e['archive_sha256'] or zsize!=e['archive_bytes']:
  raise ValueError('archive SHA-256 or byte length mismatch')
 members=e['members'];names=[x['staged'] for x in members]
 if len(names)!=188 or len(set(names))!=188:raise ValueError('unexpected member inventory')
 for name in names:
  p=PurePosixPath(name)
  if len(p.parts)!=2 or p.parts[0]!='g3-fixtures' or p.suffix!='.npy':raise ValueError('invalid member path')
 destroot=stage/'ImbalancedChen'
 with zipfile.ZipFile(a.archive) as z:
  infos={}
  for info in z.infolist():
   if info.filename in infos:raise ValueError('duplicate ZIP member: '+info.filename)
   infos[info.filename]=info
  # Verify every member, and all preexisting destinations, before writing.
  for item in members:
   name=item['staged']; info=infos.get(name)
   if info is None:raise ValueError('missing ZIP member: '+name)
   if info.is_dir() or stat.S_ISLNK(info.external_attr >> 16) or info.file_size!=item['bytes']:
    raise ValueError('invalid ZIP member type/size: '+name)
   with z.open(info) as f: h,size=digest_stream(f)
   if h!=item['sha256'] or size!=item['bytes']:raise ValueError('member SHA-256 mismatch: '+name)
   dest=destroot/name
   if not dest.resolve().is_relative_to(stage):raise ValueError('destination escapes stage: '+name)
   if dest.exists():
    if not dest.is_file():raise ValueError('destination is not a file: '+name)
    with dest.open('rb') as f: existing,existing_size=digest_stream(f)
    if existing!=h or existing_size!=size:raise ValueError('refusing to overwrite changed fixture: '+name)
  (destroot/'g3-fixtures').mkdir(parents=True,exist_ok=True)
  written=0
  for item in members:
   name=item['staged'];dest=destroot/name
   if dest.exists():continue
   with tempfile.NamedTemporaryFile(dir=dest.parent,prefix='.g3-',delete=False) as tmp:
    temp=Path(tmp.name)
    try:
     with z.open(infos[name]) as f:shutil.copyfileobj(f,tmp,1024*1024)
    except BaseException:
     temp.unlink(missing_ok=True);raise
   os.replace(temp,dest);written+=1
 print(json.dumps({'archive_sha256':zsha,'members_verified':len(members),'members_written':written,
                   'total_member_bytes':sum(x['bytes'] for x in members),'numerical_certificates_evaluated':False}))
if __name__=='__main__':
 try:main()
 except (ValueError, OSError, zipfile.BadZipFile) as exc:raise SystemExit(str(exc))
