#!/usr/bin/env python3
"""Stage 22 original documents from verified ZIP members, without evaluation."""
import argparse,hashlib,json,struct,zipfile,zlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3];HERE=Path(__file__).resolve().parent
R=ROOT/'docs/source-only/20261120-p4a5-hdensity-install-r19/NEW_DATA_FRONTIER.json';audit=json.loads(R.read_bytes());rows=audit['rows'];assert len(rows)==22
ap=argparse.ArgumentParser();ap.add_argument('--lean',type=Path,required=True);ap.add_argument('--index',type=Path,required=True);ap.add_argument('--fragment',type=Path,required=True);args=ap.parse_args()
lean=args.lean.resolve(strict=True);idx=args.index.resolve(strict=True);frag=args.fragment.resolve(strict=True);assert lean!=ROOT and ROOT not in lean.parents
sha=lambda b:hashlib.sha256(b).hexdigest()
assert idx.stat().st_size==323605374
with idx.open('rb') as f:f.seek(323421542);assert sha(f.read(183832))=='9e2c69c770f7760fc41a060829116c8abdffdd4e36a198e99baba24ef458f900'
fb=frag.read_bytes();assert len(fb)==7833786 and sha(fb)=='36ed0c5d4c5a36f74167aa9b8de33ada32c154daa0159b12b270d3095a5203be'
start=313666215;prefix='chen-numerical-evidence-20261010-renewal-v2/goldbach-research/'
source_checked={}
for x in rows:
 source=lean/'ImbalancedChen'/(x['consumer'].split('.')[-1]+'.lean');assert sha(source.read_bytes())==x['source_sha256'];source_checked[x['consumer']]=x['source_sha256']
verified=[]
with zipfile.ZipFile(idx) as z:
 for x in rows:
  member=prefix+x['name'];matches=[i for i in z.infolist() if i.filename==member];assert len(matches)==1,member;i=matches[0]
  off=i.header_offset-start;assert 0<=off and off+30<len(fb)
  sig,version,flags,method,_,_,_,_,_,namelen,extralen=struct.unpack_from('<IHHHHHIIIHH',fb,off);assert sig==0x04034b50 and flags&1==0 and method==i.compress_type and method in (0,8)
  a=off+30;assert fb[a:a+namelen].decode('utf-8')==member;a+=namelen+extralen;assert a+i.compress_size<=len(fb)
  data=fb[a:a+i.compress_size];data=zlib.decompress(data,-15) if method==8 else data
  assert len(data)==i.file_size==x['size'] and zlib.crc32(data)&0xffffffff==i.CRC and sha(data)==x['expected_sha256'],x['name']
  blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest();assert not x.get('expected_git_blob') or blob==x['expected_git_blob']
  target=lean.parent/'tmp/publication-20261010/verification-renewal-v2/_runs/full-final'/x['name'];assert not target.exists() and not target.is_symlink()
  verified.append((x,i,data,blob,target))
# All 22 members are validated before any writes.
receipt=[]
for x,i,data,blob,target in verified:
 target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data);assert sha(target.read_bytes())==x['expected_sha256']
 receipt.append({'consumer':x['consumer'],'name':x['name'],'install_path':'../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/'+x['name'],'bytes':len(data),'sha256':sha(data),'git_blob_sha1':blob,'member':i.filename,'header_offset':i.header_offset,'compressed_size':i.compress_size,'crc32':f'{i.CRC:08x}','registry':x['registry'],'registry_sha256':x['registry_sha256']})
print(json.dumps({'scope':'original per-member data identity and placement only; no parsing, numerical calculation or Lean proof','release':'https://github.com/UyNewNas/chen-imbalanced-semiprimes/releases/tag/v2026.10.10','full_archive_sha256_verified':False,'central_sha256':'9e2c69c770f7760fc41a060829116c8abdffdd4e36a198e99baba24ef458f900','fragment_range':[313666215,321500000],'fragment_sha256':sha(fb),'source_sha256':source_checked,'count':len(receipt),'members':receipt},indent=2))
