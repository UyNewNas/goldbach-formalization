set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
cd /workspace/p2-4-compact-proof-20261125
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python - <<'PY'
from pathlib import Path
import hashlib,json,base64,gzip,io,tarfile,subprocess,os
root=Path.cwd();src=Path('/workspace/p24-nine-source-promotion-20261126/attempt-001')
archive=src.parent/'evidence-1087.tar.gz'
descriptor=src.parent/'evidence-1087-descriptor.json'
assert not archive.exists() and not descriptor.exists(), 'Preserve prior derived artifacts'
reserve=32*1024*1024
def free_bytes():
 v=os.statvfs(src.parent);return v.f_bavail*v.f_frsize
assert free_bytes()>=reserve
input_paths=set()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()=='1087bc663a46352f99b2e9a1da238aaf4b855fdf'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True).strip()
reg=root/'.lake/p2-private/records.json'; regsha=sha(reg);assert regsha=='6ad38f2848bb1a1165460b41575837036e3555d8bc77c1fcebd2d9bd19187a88'
assert sha(src/'receipt.json')=='ce0f2d1c7477b27143dc2e1f6891a6b373e2484785925703bd5995fe9a268620'
files={}
for p in sorted(src.iterdir()):
 if p.is_file():
  files['promotion/'+p.name]=p.read_bytes();input_paths.add(p)
records=json.loads(reg.read_bytes())
for name in ['ImbalancedChen.P2OriginalCompactQ80Reachability','ImbalancedChen.P2OriginalCompactCachedRun','ImbalancedChen.P2OriginalCompactQ80FixedBindings']:
 rec=records[name];assert rec['exit_code']!=0
 p=Path(rec['log']);p=p if p.is_absolute() else root/p
 raw=p.read_bytes();input_paths.add(p)
 if rec.get('log_sha256'):assert hashlib.sha256(raw).hexdigest()==rec['log_sha256']
 files['failed/'+name+'/compile.log']=raw
 files['failed/'+name+'/compile-record.json']=(json.dumps(rec,sort_keys=True,indent=2)+'\n').encode()
 source_path=root/(name.replace('.','/')+'.lean')
 files['failed/'+name+'/source.lean']=source_path.read_bytes();input_paths.add(source_path)
input_before={str(p):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(input_paths)}
index={n:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in files.items()}
files['FILES.json']=(json.dumps(index,sort_keys=True,indent=2)+'\n').encode()
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.PAX_FORMAT) as t:
 for name,raw in sorted(files.items()):
  info=tarfile.TarInfo(name);info.size=len(raw);info.mtime=0;info.mode=0o644;t.addfile(info,io.BytesIO(raw))
tar=buf.getvalue();z=gzip.compress(tar,mtime=0)
assert sha(reg)==regsha and sha(src/'receipt.json')=='ce0f2d1c7477b27143dc2e1f6891a6b373e2484785925703bd5995fe9a268620'
# The exact original archive recipe is retained above; only its transport changes.
expected_members={n:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in files.items()}
meta={
 'retrieval_only':True,'original_gate_failed':True,'original_gate_task':'c8cd6d4256d4401da57be40cdb10ecb5',
 'source_pin':'1087bc663a46352f99b2e9a1da238aaf4b855fdf','file_count':len(files),
 'tar_bytes':len(tar),'tar_sha256':hashlib.sha256(tar).hexdigest(),
 'gzip_bytes':len(z),'gzip_sha256':hashlib.sha256(z).hexdigest(),
 'archive_path':str(archive),'descriptor_path':str(descriptor),
 'original_registry_sha256':regsha,'original_receipt_sha256':sha(src/'receipt.json'),
 'source_inputs':input_before,'members':expected_members,
 'prior_transport_failure':{'task':'ec2a8d049aa34280be107e7499857501','log_truncated':True,'retained_bytes':2097152,'discarded_bytes':6984297,'complete_archive_retrieved':False},
 'reserve_bytes':reserve,'original_files_deleted':False,'production_changed':False,
 'registry_writeback':False,'canonical_credit':False,'archive_retrieved_locally':False,
}
encoded=(json.dumps(meta,sort_keys=True,indent=2)+'\n').encode()
assert free_bytes()>=len(z)+len(encoded)+reserve+1024*1024, 'Retain the full 32 MiB reserve'
with archive.open('xb') as out:
 out.write(z);out.flush();os.fsync(out.fileno())
assert archive.stat().st_size==len(z) and sha(archive)==meta['gzip_sha256']
archived_tar=gzip.decompress(archive.read_bytes())
assert len(archived_tar)==len(tar) and hashlib.sha256(archived_tar).hexdigest()==meta['tar_sha256']
actual_members={}
with tarfile.open(fileobj=io.BytesIO(archived_tar),mode='r:') as t:
 for member in t:
  assert member.isfile() and member.name not in actual_members
  raw=t.extractfile(member).read()
  actual_members[member.name]={'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
  assert raw==files[member.name]
 assert actual_members==expected_members
 assert json.loads(t.extractfile('FILES.json').read())==index
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==meta['source_pin']
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True).strip()
assert sha(reg)==regsha and sha(src/'receipt.json')=='ce0f2d1c7477b27143dc2e1f6891a6b373e2484785925703bd5995fe9a268620'
assert {str(p):{'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(input_paths)}==input_before
meta['whole_tar_and_all_members_verified']=True
meta['all_original_inputs_unchanged']=True
meta['free_bytes_after_archive']=free_bytes()
encoded=(json.dumps(meta,sort_keys=True,indent=2)+'\n').encode()
assert free_bytes()>=len(encoded)+reserve
with descriptor.open('xb') as out:
 out.write(encoded);out.flush();os.fsync(out.fileno())
assert descriptor.read_bytes()==encoded and free_bytes()>=reserve
print('P24_1087_GATE_EVIDENCE_ARCHIVE '+json.dumps({
 'retrieval_only':True,'original_gate_failed':True,'source_pin':meta['source_pin'],
 'archive':{'path':str(archive),'bytes':len(z),'sha256':meta['gzip_sha256']},
 'descriptor':{'path':str(descriptor),'bytes':len(encoded),'sha256':sha(descriptor)},
 'file_count':len(files),'tar_bytes':len(tar),'tar_sha256':meta['tar_sha256'],
 'whole_tar_and_all_members_verified':True,'all_original_inputs_unchanged':True,
 'reserve_bytes':reserve,'free_bytes_after':free_bytes(),
 'prior_stdout_truncated':True,'canonical_credit':False,
},sort_keys=True),flush=True)
PY
