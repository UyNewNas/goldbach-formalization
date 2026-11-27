#!/usr/bin/env bash
python3 -B - "$@" <<'PY'
from pathlib import Path
import base64,hashlib,io,json,lzma,re,sys,tarfile
if len(sys.argv)!=2 or re.fullmatch(r'[0-9a-f]{64}',sys.argv[1]) is None:
 raise RuntimeError('expected exactly one mandatory expected_prior_checkpoint_sha256 argument: 64 lowercase hexadecimal characters')
expected_prior_checkpoint_sha256=sys.argv[1]
base=Path('/workspace/p1-complete-proof')
prior=base/'20261125-p14-continuation-export/checkpoint-12.tar.xz'
if prior.is_symlink() or not prior.is_file():raise RuntimeError('missing/nonregular/symlink prior checkpoint '+str(prior))
prior_sha=hashlib.sha256(prior.read_bytes()).hexdigest()
if prior_sha!=expected_prior_checkpoint_sha256:raise RuntimeError('prior checkpoint SHA256 mismatch')
roots={
  "p14/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda": "20261125-p14-continuation/typed-range-blocks-111-120/5ba405bc08aaef020868399aa62a429ca4281eda",
  "p14/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda": "20261125-p14-continuation/typed-range-blocks-121-130/5ba405bc08aaef020868399aa62a429ca4281eda",
  "p14/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda": "20261125-p14-continuation/typed-range-blocks-131-140/5ba405bc08aaef020868399aa62a429ca4281eda",
  "p14/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda": "20261125-p14-continuation/typed-range-blocks-141-142/5ba405bc08aaef020868399aa62a429ca4281eda",
  "p14/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5": "20261125-p14-continuation/owner-b13-typed-bound-retry/bb377de86aa1e92f461c3d01471010cb0791dad5",
  "p14/adopted-owner-bank-label5-retry/bb377de86aa1e92f461c3d01471010cb0791dad5": "20261125-p14-continuation/adopted-owner-bank-label5-retry/bb377de86aa1e92f461c3d01471010cb0791dad5",
  "p14/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27": "20261125-p14-continuation/adopted-owner-bank-typed-bound-retry/14845975a892974d2633c283f73f03cb87faae27",
  "p14/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4": "20261125-p14-continuation/barycentric-id-power-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4",
  "p14/child-gap-namespace-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4": "20261125-p14-continuation/child-gap-namespace-retry/28faf9d2b028997dfe7669b6750c0be5649c9ee4",
  "p14/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb": "20261125-p14-continuation/typed-range-aggregate/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb",
  "p14/child-gap-expression-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52": "20261125-p14-continuation/child-gap-expression-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52",
  "p14/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52": "20261125-p14-continuation/uniform-adopted-error-add-cast-retry/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52",
  "p14/typed-key-uniqueness-kernel-exception-diagnostic/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52": "20261125-p14-continuation/typed-key-uniqueness-kernel-exception-diagnostic/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52"
}
single_files={
  "p14_pipeline/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/5ba405bc08aaef020868399aa62a429ca4281eda/range-blocks-111-142/PIPELINE_RESULT.json",
  "p14_pipeline/bb377de86aa1e92f461c3d01471010cb0791dad5/owner-b13-typed-bound-and-consumers/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/bb377de86aa1e92f461c3d01471010cb0791dad5/owner-b13-typed-bound-and-consumers/PIPELINE_RESULT.json",
  "p14_pipeline/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/28faf9d2b028997dfe7669b6750c0be5649c9ee4/barycentric-id-power-and-consumers/PIPELINE_RESULT.json",
  "p14_pipeline/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/typed-range-aggregate-after-known-deployment/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/0c596ad7ce87f9f3a9a2ffbb5aec75af443444cb/typed-range-aggregate-after-known-deployment/PIPELINE_RESULT.json",
  "p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/PIPELINE_RESULT.json": "20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/PIPELINE_RESULT.json",
  "p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/CANDIDATE_BINDING.json": "20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/CANDIDATE_BINDING.json",
  "p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/child-gap-expression-retry.log": "20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/child-gap-expression-retry.log",
  "p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/uniform-adopted-error-add-cast-retry.log": "20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/uniform-adopted-error-add-cast-retry.log",
  "p14_pipeline/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/typed-key-uniqueness-kernel-exception-diagnostic.log": "20261125-p14-continuation-bootstrap/a6fdc93e06ad6d8cbfaf2bb60ff723c1efbfee52/restored-p1-three-singletons/checks/typed-key-uniqueness-kernel-exception-diagnostic.log"
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
manifest={'schema':'p14_receipt_export_v1','checkpoint':'13','prior_checkpoint_sha256':prior_sha,'roots':roots,'single_files':single_files,'files':[r for r,_ in files],'omitted_nonreceipt_files':omitted,'whole_P1_4_complete':False}
raw=io.BytesIO()
with tarfile.open(fileobj=raw,mode='w') as tar:
 for row,data in files:
  info=tarfile.TarInfo(row['path']);info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
 data=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode();info=tarfile.TarInfo('EXPORT_MANIFEST.json');info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
archive=lzma.compress(raw.getvalue(),preset=9)
p=base/'20261125-p14-continuation-export/checkpoint-13.tar.xz'
with p.open('xb') as f:f.write(archive)
print(json.dumps({'schema':'p14_receipt_export_transport_v1','archive_path':str(p),'sha256':hashlib.sha256(archive).hexdigest(),'bytes':len(archive),'file_count':len(files),'omitted_count':len(omitted),'uncompressed_bytes':sum(len(d) for _,d in files)}),flush=True)
if len(archive)>4*1024*1024:raise RuntimeError('archive exceeds transport budget')
print(base64.b64encode(archive).decode(),flush=True)
PY

