#!/usr/bin/env bash
python3 -B - "$@" <<'PY'
from pathlib import Path
import base64,hashlib,io,json,lzma,re,sys,tarfile
if len(sys.argv)!=2 or re.fullmatch(r'[0-9a-f]{64}',sys.argv[1]) is None:
 raise RuntimeError('expected exactly one mandatory expected_prior_checkpoint_sha256 argument: 64 lowercase hexadecimal characters')
expected_prior_checkpoint_sha256=sys.argv[1]
base=Path('/workspace/p1-complete-proof')
prior=base/'20261125-p14-continuation-export/checkpoint-06.tar.xz'
if prior.is_symlink() or not prior.is_file():raise RuntimeError('missing/nonregular/symlink prior checkpoint '+str(prior))
prior_sha=hashlib.sha256(prior.read_bytes()).hexdigest()
if prior_sha!=expected_prior_checkpoint_sha256:raise RuntimeError('prior checkpoint SHA256 mismatch')
roots={
  "p14/typed-range-blocks-001-010/5ba405bc08aaef020868399aa62a429ca4281eda": "20261125-p14-continuation/typed-range-blocks-001-010/5ba405bc08aaef020868399aa62a429ca4281eda",
  "p14/frozen-upper-surrogate/8682bf05456060c0677bdddb210df38f33229817": "20261125-p14-continuation/frozen-upper-surrogate/8682bf05456060c0677bdddb210df38f33229817",
  "p14/frozen-gap-concavity/8682bf05456060c0677bdddb210df38f33229817": "20261125-p14-continuation/frozen-gap-concavity/8682bf05456060c0677bdddb210df38f33229817",
  "p14/typed-base-core/e4dfe229579714b69c302e667d88649a14b58a0c": "20261125-p14-continuation/typed-base-core/e4dfe229579714b69c302e667d88649a14b58a0c",
  "p14/typed-base-block000/e4dfe229579714b69c302e667d88649a14b58a0c": "20261125-p14-continuation/typed-base-block000/e4dfe229579714b69c302e667d88649a14b58a0c"
}
single_files={
  "p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-001-010/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-001-010/PIPELINE_RESULT.json",
  "p14_pipeline/8682bf05456060c0677bdddb210df38f33229817/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/8682bf05456060c0677bdddb210df38f33229817/PIPELINE_RESULT.json",
  "p14_pipeline/e4dfe229579714b69c302e667d88649a14b58a0c/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/e4dfe229579714b69c302e667d88649a14b58a0c/PIPELINE_RESULT.json"
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
manifest={'schema':'p14_receipt_export_v1','checkpoint':'07','prior_checkpoint_sha256':prior_sha,'roots':roots,'single_files':single_files,'files':[r for r,_ in files],'omitted_nonreceipt_files':omitted,'whole_P1_4_complete':False}
raw=io.BytesIO()
with tarfile.open(fileobj=raw,mode='w') as tar:
 for row,data in files:
  info=tarfile.TarInfo(row['path']);info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
 data=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode();info=tarfile.TarInfo('EXPORT_MANIFEST.json');info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
archive=lzma.compress(raw.getvalue(),preset=9)
p=base/'20261125-p14-continuation-export/checkpoint-07.tar.xz'
with p.open('xb') as f:f.write(archive)
print(json.dumps({'schema':'p14_receipt_export_transport_v1','archive_path':str(p),'sha256':hashlib.sha256(archive).hexdigest(),'bytes':len(archive),'file_count':len(files),'omitted_count':len(omitted),'uncompressed_bytes':sum(len(d) for _,d in files)}),flush=True)
if len(archive)>4*1024*1024:raise RuntimeError('archive exceeds transport budget')
print(base64.b64encode(archive).decode(),flush=True)
PY

