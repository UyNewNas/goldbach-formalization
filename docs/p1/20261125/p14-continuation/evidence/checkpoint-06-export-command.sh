#!/usr/bin/env bash
python3 -B - <<'PY'
from pathlib import Path
import base64,hashlib,io,json,lzma,tarfile
base=Path('/workspace/p1-complete-proof')
roots={
  "p14/owner-license-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b": "20261125-p14-continuation/owner-license-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b",
  "p14/literal-positive-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b": "20261125-p14-continuation/literal-positive-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b",
  "p14/npy-positional-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b": "20261125-p14-continuation/npy-positional-retry/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b",
  "p14/owner-fibre-volume-retry/a700772dbddaa09df497590c7d1b54d6e488f812": "20261125-p14-continuation/owner-fibre-volume-retry/a700772dbddaa09df497590c7d1b54d6e488f812",
  "p14/exact64-tiling-retry/a700772dbddaa09df497590c7d1b54d6e488f812": "20261125-p14-continuation/exact64-tiling-retry/a700772dbddaa09df497590c7d1b54d6e488f812",
  "p14/owner-gamma-volume/a700772dbddaa09df497590c7d1b54d6e488f812": "20261125-p14-continuation/owner-gamma-volume/a700772dbddaa09df497590c7d1b54d6e488f812"
}
single_files={
  "p14_pipeline/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/c490c251cf83e1f0fd7d4a4a31fd53f99e7e972b/PIPELINE_RESULT.json",
  "p14_pipeline/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/a700772dbddaa09df497590c7d1b54d6e488f812/PIPELINE_RESULT.json"
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
for label,rel in single_files.items():
 p=base/rel
 if p.is_symlink() or not p.is_file():raise RuntimeError('missing/nonregular evidence file '+str(p))
 data=p.read_bytes()
 files.append(({'path':label,'original_path':str(p),'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()},data))
manifest={'schema':'p14_receipt_export_v1','checkpoint':'06','prior_checkpoint_sha256':'1e22c13ae22dffc8faa3db38958c30e62733fdbbbdd2b2d25b9f5f46e7fb1e5e','roots':roots,'single_files':single_files,'files':[r for r,_ in files],'omitted_nonreceipt_files':omitted,'whole_P1_4_complete':False}
raw=io.BytesIO()
with tarfile.open(fileobj=raw,mode='w') as tar:
 for row,data in files:
  info=tarfile.TarInfo(row['path']);info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
 data=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode();info=tarfile.TarInfo('EXPORT_MANIFEST.json');info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
archive=lzma.compress(raw.getvalue(),preset=9)
p=base/'20261125-p14-continuation-export/checkpoint-06.tar.xz'
with p.open('xb') as f:f.write(archive)
print(json.dumps({'schema':'p14_receipt_export_transport_v1','archive_path':str(p),'sha256':hashlib.sha256(archive).hexdigest(),'bytes':len(archive),'file_count':len(files),'omitted_count':len(omitted),'uncompressed_bytes':sum(len(d) for _,d in files)}),flush=True)
if len(archive)>4*1024*1024:raise RuntimeError('archive exceeds transport budget')
print(base64.b64encode(archive).decode(),flush=True)
PY

