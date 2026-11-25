#!/usr/bin/env bash
python3 -B - <<'PY'
from pathlib import Path
import base64,hashlib,io,json,lzma,tarfile
base=Path('/workspace/p1-complete-proof')
roots={
  "p14/bytes-frame-seed/540244f58dcfa10e035c12c7196597ee2198f327": "20261125-p14-continuation/bytes-frame-seed/540244f58dcfa10e035c12c7196597ee2198f327",
  "p15_shared_round03": "20261125-p15-actual-means-v1/57608d49e043b1d6857145679b958d3416aa3122",
  "p15_shared_round04": "20261125-p15-actual-means-v1/4294a84d24b24885eedfe101fe68a382879ab94d",
  "p15_shared_round05": "20261125-p15-actual-means-v1/915921f87cd7fa4f4ca6cc52af712adf02bb2fe8",
  "p15_shared_round06": "20261125-p15-actual-means-v1/a0c521ebe87459c1fb7d40732f4382cd850c4921",
  "p15_shared_round07": "20261125-p15-actual-means-v1/089a7f99646fe1921d0cd1450485561e6b52b5e4"
}
allowed={'.json','.log','.py','.lean','.txt','.trace','.md','.patch','.diff'}
files=[];omitted=[]
for label,rel in roots.items():
 root=base/rel
 if not root.is_dir():raise RuntimeError('missing evidence root '+str(root))
 for p in sorted(root.rglob('*')):
  if p.is_symlink():raise RuntimeError('unexpected symlink '+str(p))
  if p.is_file():
   row={'path':label+'/'+p.relative_to(root).as_posix(),'original_path':str(p),'bytes':p.stat().st_size}
   if p.suffix in allowed or p.name.endswith('.sha256'):
    data=p.read_bytes();row['sha256']=hashlib.sha256(data).hexdigest();files.append((row,data))
   else:omitted.append(row)
manifest={'schema':'p14_receipt_export_v1','checkpoint':'03','prior_checkpoint_sha256':'fb92a04371670d9f04b35420c0cfa7ac6afefd039eae1bca2f9ae0e584924ef5','roots':roots,'files':[r for r,_ in files],'omitted_nonreceipt_files':omitted,'whole_P1_4_complete':False}
raw=io.BytesIO()
with tarfile.open(fileobj=raw,mode='w') as tar:
 for row,data in files:
  info=tarfile.TarInfo(row['path']);info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
 data=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode();info=tarfile.TarInfo('EXPORT_MANIFEST.json');info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
archive=lzma.compress(raw.getvalue(),preset=9)
p=base/'20261125-p14-continuation-export/checkpoint-03.tar.xz'
with p.open('xb') as f:f.write(archive)
print(json.dumps({'schema':'p14_receipt_export_transport_v1','archive_path':str(p),'sha256':hashlib.sha256(archive).hexdigest(),'bytes':len(archive),'file_count':len(files),'omitted_count':len(omitted),'uncompressed_bytes':sum(len(d) for _,d in files)}),flush=True)
if len(archive)>4*1024*1024:raise RuntimeError('archive exceeds transport budget')
print(base64.b64encode(archive).decode(),flush=True)
PY

