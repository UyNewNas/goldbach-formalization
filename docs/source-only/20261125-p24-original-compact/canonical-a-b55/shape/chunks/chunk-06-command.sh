set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'P24_A_SHAPE_CHUNK_6'
from pathlib import Path
import base64,hashlib,json,stat
path=Path('/workspace/p2-4-compact-proof-20261125/.lake/p24-canonical-A-block-shape/b55-attempt-001/blocks.stdout.log.gz')
assert path.resolve(strict=True)==path and stat.S_ISREG(path.stat().st_mode)
before=path.stat();raw=path.read_bytes();after=path.stat()
assert (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns)
assert len(raw)==7577341 and hashlib.sha256(raw).hexdigest()=='709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0'
part=raw[6000000:7000000]
assert len(part)==1000000 and len(part)<=1000000
assert path.read_bytes()==raw
result={'chunk_index':6,'chunk_count':8,'offset':6000000,'end':7000000,'raw_bytes':len(part),'chunk_sha256':hashlib.sha256(part).hexdigest(),'file_bytes':len(raw),'file_sha256':'709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0','data':base64.b64encode(part).decode(),'all_original_bytes_unchanged':True,'remote_writes':False,'proof_or_audit_executed':False,'canonical_credit':False}
out='P24_A_SHAPE_CHUNK '+json.dumps(result,sort_keys=True)+'\n'
assert len(out.encode())<2000000
print(out,end='',flush=True)
P24_A_SHAPE_CHUNK_6
