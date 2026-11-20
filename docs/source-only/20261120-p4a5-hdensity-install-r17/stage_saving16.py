#!/usr/bin/env python3
"""Verify original release ZIP members for the exact Saving16 Lean loader.

The input is a central-directory index plus limited original ZIP byte ranges;
this never claims that the whole release archive was downloaded or verified.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import struct
import tempfile
import zipfile
import zlib

ROOT=Path(__file__).resolve().parents[3]
PREV=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r17'
AUDIT=PREV/'NEW_INPUTS_BEFORE.json'
AUDIT_SHA='a70818a6d4dd6c86bc5e58b00d6e845b9c85669725bd513f162ba663a426ce01'
SRC_AUDIT=PREV/'IMPORT_AUDIT.json'
SRC_AUDIT_SHA='6563319f8c49429aabc820d4048c23a28f09834f9cf7077991a7a8fd832d6cdc'
CENTRAL_SHA='9e2c69c770f7760fc41a060829116c8abdffdd4e36a198e99baba24ef458f900'
PREFIX='chen-numerical-evidence-20261010-renewal-v2/goldbach-research/'
RANGES={'saving16':('P2OriginalSaving16OriginalArchive','r17-saving16.range',77742667,99803531)}
CHUNK=1048576

def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for chunk in iter(lambda:f.read(CHUNK),b''):h.update(chunk)
 return h.hexdigest()

def member(f,start,info,out=None):
 f.seek(info.header_offset-start);header=f.read(30)
 assert len(header)==30
 sig,version,flags,method,_,_,_,_,_,namelen,extralen=struct.unpack('<IHHHHHIIIHH',header)
 assert sig==0x04034b50 and flags & 1==0 and method==info.compress_type and method in (0,8)
 assert f.read(namelen).decode('utf-8')==info.filename
 assert len(f.read(extralen))==extralen
 left=info.compress_size;d=zlib.decompressobj(-15) if method==8 else None
 h=hashlib.sha256();size=0;crc=0
 def accept(buf):
  nonlocal size,crc
  h.update(buf);size+=len(buf);crc=zlib.crc32(buf,crc)
  if out is not None:out.write(buf)
 while left:
  data=f.read(min(CHUNK,left));assert data,'truncated ZIP member'
  left-=len(data);accept(d.decompress(data) if d else data)
 if d:
  accept(d.flush());assert d.eof and not d.unused_data and not d.unconsumed_tail
 assert size==info.file_size and crc & 0xffffffff==info.CRC,'ZIP member size or CRC mismatch'
 return h.hexdigest(),size

ap=argparse.ArgumentParser()
ap.add_argument('--stage',type=Path,required=True)
ap.add_argument('--range-dir',type=Path,required=True)
ap.add_argument('--index',type=Path,required=True)
ap.add_argument('--groups',nargs='+',choices=sorted(RANGES),required=True)
args=ap.parse_args()
assert len(args.groups)==len(set(args.groups))
stage=args.stage.resolve(strict=True);ranges=args.range_dir.resolve(strict=True)
assert stage!=ROOT and ROOT not in stage.parents
assert sha(AUDIT)==AUDIT_SHA and sha(SRC_AUDIT)==SRC_AUDIT_SHA
entries=json.loads(AUDIT.read_text())['witnesses'];sources=json.loads(SRC_AUDIT.read_text())['visited']
assert len(entries)==16 and args.index.stat().st_size==323605374
with args.index.open('rb') as f:
 f.seek(323421542);assert hashlib.sha256(f.read(183832)).hexdigest()==CENTRAL_SHA
selected=[];range_hashes={}
with zipfile.ZipFile(args.index) as index:
 allnames=[x.filename for x in index.infolist()]
 for group in args.groups:
  leaf,filename,start,end=RANGES[group];mod='ImbalancedChen.'+leaf
  source=stage/'ImbalancedChen'/(leaf+'.lean')
  assert sha(source)==sources[mod]['sha256']
  path=ranges/filename;assert path.is_file() and path.stat().st_size==end-start+1,filename
  range_hashes[group]=sha(path)
  group_entries=[x for x in entries if x['consumer']==mod]
  assert len(group_entries)=={'saving16':14}[group]
  for item in group_entries:
   name=item['origin']['member'];assert item['origin']['kind']=='release_member' and name.startswith(PREFIX)
   assert allnames.count(name)==1
   info=index.getinfo(name)
   assert start<=info.header_offset<=end and info.file_size==item['bytes']
   ip=PurePosixPath(item['install_path'])
   if group=='g6':
    assert str(ip)=='ImbalancedChen/G6_ORIGINAL_WITNESS.json';target=stage/str(ip)
   else:
    assert len(ip.parts)==3 and ip.parts[:2]==('..','goldbach-research') and ip.name==name.rsplit('/',1)[1]
    target=stage.parent/'goldbach-research'/ip.name
   assert not target.is_symlink() and not target.parent.is_symlink()
   if target.exists():assert target.is_file() and target.stat().st_size==item['bytes'] and sha(target)==item['expected_sha256'],'different existing data'
   selected.append((group,path,start,end,item,info,target))
 # Entire selected set is hashed and CRC-checked before any output is written.
 for group,path,start,end,item,info,target in selected:
  with path.open('rb') as f:found,size=member(f,start,info)
  assert found==item['expected_sha256'] and size==item['bytes'],item['install_path']
 for group,path,start,end,item,info,target in selected:
  if target.exists():continue
  target.parent.mkdir(parents=True,exist_ok=True)
  assert not target.parent.is_symlink()
  fd,tmp=tempfile.mkstemp(prefix='.witness-',dir=target.parent)
  try:
   with os.fdopen(fd,'wb') as out,path.open('rb') as f:found,size=member(f,start,info,out)
   assert found==item['expected_sha256'] and size==item['bytes']
   os.replace(tmp,target)
  finally:
   if os.path.exists(tmp):os.unlink(tmp)
print(json.dumps({'scope':'exact selected original member identities and staging; no numerical certificates or Lean evaluation',
 'release':'https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/tag/v2026.10.10',
 'runtime_audit_sha256':AUDIT_SHA,'full_release_archive_hash_verified':False,
 'groups':args.groups,'range_sha256':range_hashes,'member_count':len(selected),
 'member_bytes':sum(x[4]['bytes'] for x in selected),'certificates_evaluated':False,
 'members':[{'consumer':x[4]['consumer'],'install_path':x[4]['install_path'],
             'bytes':x[4]['bytes'],'sha256':x[4]['expected_sha256']} for x in selected]},indent=2))
