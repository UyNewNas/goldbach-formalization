set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
cd /workspace/p2-4-compact-proof-20261125
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python - <<'PY'
from pathlib import Path
import hashlib,json,base64,gzip,io,tarfile,subprocess
root=Path.cwd();src=Path('/workspace/p24-nine-source-promotion-20261126/attempt-001')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()=='1087bc663a46352f99b2e9a1da238aaf4b855fdf'
assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],text=True).strip()
reg=root/'.lake/p2-private/records.json'; regsha=sha(reg);assert regsha=='6ad38f2848bb1a1165460b41575837036e3555d8bc77c1fcebd2d9bd19187a88'
assert sha(src/'receipt.json')=='ce0f2d1c7477b27143dc2e1f6891a6b373e2484785925703bd5995fe9a268620'
files={}
for p in sorted(src.iterdir()):
 if p.is_file():files['promotion/'+p.name]=p.read_bytes()
records=json.loads(reg.read_bytes())
for name in ['ImbalancedChen.P2OriginalCompactQ80Reachability','ImbalancedChen.P2OriginalCompactCachedRun','ImbalancedChen.P2OriginalCompactQ80FixedBindings']:
 rec=records[name];assert rec['exit_code']!=0
 p=Path(rec['log']);p=p if p.is_absolute() else root/p
 raw=p.read_bytes()
 if rec.get('log_sha256'):assert hashlib.sha256(raw).hexdigest()==rec['log_sha256']
 files['failed/'+name+'/compile.log']=raw
 files['failed/'+name+'/compile-record.json']=(json.dumps(rec,sort_keys=True,indent=2)+'\n').encode()
 files['failed/'+name+'/source.lean']=(root/(name.replace('.','/')+'.lean')).read_bytes()
index={n:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in files.items()}
files['FILES.json']=(json.dumps(index,sort_keys=True,indent=2)+'\n').encode()
buf=io.BytesIO()
with tarfile.open(fileobj=buf,mode='w',format=tarfile.PAX_FORMAT) as t:
 for name,raw in sorted(files.items()):
  info=tarfile.TarInfo(name);info.size=len(raw);info.mtime=0;info.mode=0o644;t.addfile(info,io.BytesIO(raw))
tar=buf.getvalue();z=gzip.compress(tar,mtime=0)
assert sha(reg)==regsha and sha(src/'receipt.json')=='ce0f2d1c7477b27143dc2e1f6891a6b373e2484785925703bd5995fe9a268620'
print('P24_1087_GATE_EVIDENCE '+json.dumps({'retrieval_only':True,'original_gate_failed':True,'source_pin':'1087bc663a46352f99b2e9a1da238aaf4b855fdf','file_count':len(files),'tar_bytes':len(tar),'tar_sha256':hashlib.sha256(tar).hexdigest(),'gzip_bytes':len(z),'gzip_sha256':hashlib.sha256(z).hexdigest(),'data':base64.b64encode(z).decode()},sort_keys=True),flush=True)
PY
