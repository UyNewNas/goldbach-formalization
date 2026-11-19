#!/usr/bin/env python3
"""Recover the two pinned G1/G4 elaborator inputs; leave other data untouched."""
import argparse, hashlib, os, shutil, subprocess, tempfile
from pathlib import Path
BASE='https://raw.githubusercontent.com/UyNewNas/goldbach-formalization/d5f392f6717227ab94ad4004044a037ac83be877/'
ROWS=[
 ('proof-continuation-data/fourth-original/FourthRows17LE.bin','provenance/original-fourth/FourthRows17LE.bin',62885159,'561f5dc9ff2f6d64ba739de830511f6f68bf1f7be0c724655a8435c7edb914da','dbdbb0303f866afd17698c40b1c4d413beb7ca79'),
 ('docs/source-only/20261102-resume-30s/s09_actual_full_sixth/provenance/OriginalSixthCells.npy','provenance/OriginalSixthCells.npy',55625280,'406623527077e0cd424f2098713e70125795eafbee758d21f16d19d89dfb9be8','94caeaaa65463f79d354a7a90f78ddb2aa0977fa'),
]
def verify(p,size,sha,blob):
 if p.stat().st_size!=size: raise ValueError('unexpected size '+str(p))
 h=hashlib.sha256();g=hashlib.sha1(('blob '+str(size)+'\0').encode())
 with p.open('rb') as f:
  for chunk in iter(lambda:f.read(1<<20),b''): h.update(chunk);g.update(chunk)
 if h.hexdigest()!=sha or g.hexdigest()!=blob: raise ValueError('hash mismatch '+str(p))
def main():
 a=argparse.ArgumentParser();a.add_argument('--project-dir',type=Path,required=True);a=a.parse_args()
 if not a.project_dir.is_dir(): raise ValueError('project directory must already exist')
 root=a.project_dir/'ImbalancedChen'
 if not root.is_dir(): raise ValueError('existing ImbalancedChen directory required')
 for url_path,relative,size,sha,blob in ROWS:
  dst=root/relative;dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists(): verify(dst,size,sha,blob);print('verified-existing',relative);continue
  with tempfile.NamedTemporaryFile(dir=dst.parent,delete=False) as tmp: t=Path(tmp.name)
  try:
   cmd=['curl','-sS','-L','--fail','--max-time','50','--max-filesize',str(size),'--output',str(t),BASE+url_path+'?source=p4a4']
   subprocess.run(cmd,check=True);verify(t,size,sha,blob)
   with t.open('rb') as source,dst.open('xb') as target: shutil.copyfileobj(source,target,1<<20)
   verify(dst,size,sha,blob);print('recovered-verified',relative)
  finally: t.unlink(missing_ok=True)
if __name__=='__main__':main()
