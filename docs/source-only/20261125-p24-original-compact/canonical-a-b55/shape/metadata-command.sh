set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'P24_A_SHAPE_METADATA'
from pathlib import Path
import base64,hashlib,json,os,stat
root=Path('/workspace/p2-4-compact-proof-20261125/.lake/p24-canonical-A-block-shape/b55-attempt-001')
names=['blocks.stdout.log.gz','shape-diagnostic.json','complete-block-summary.json.gz','complete-block-owned-link.json.gz','InspectBlocks.lean']
rows={}
raws={}
for name in names:
 p=root/name
 assert p.resolve(strict=True)==p and stat.S_ISREG(p.stat().st_mode)
 before=p.stat()
 raw=p.read_bytes()
 after=p.stat()
 assert (before.st_dev,before.st_ino,before.st_size,before.st_mtime_ns,before.st_ctime_ns)==(after.st_dev,after.st_ino,after.st_size,after.st_mtime_ns,after.st_ctime_ns)
 assert len(raw)==before.st_size
 rows[name]={'path':str(p),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest()}
 raws[name]=raw
assert rows['blocks.stdout.log.gz']['bytes']==7577341 and rows['blocks.stdout.log.gz']['sha256']=='709c2f0d26d4481f2845edd7d2726e677842eda447f455297178dab7259a25d0'
assert rows['shape-diagnostic.json']['bytes']==47362 and rows['shape-diagnostic.json']['sha256']=='b9b08afbc251a664cbb01d4b45cdc1be4bb8fc6fbb02f1c3fba049b39d549182'
payloads={};total=0
for name in names[1:]:
 if total+len(raws[name])<=1000000:
  payloads[name]=base64.b64encode(raws[name]).decode()
  total+=len(raws[name])
for name in names:
 assert (root/name).read_bytes()==raws[name]
result={'source_pin_of_evidence':'b55fa93d39e6a4ddf2abd37b9b8481078e329f70','original_shape_task_id':'af141e9e53ef4fd591f2e320debedb5e','files':rows,'payloads':payloads,'total_raw_payload_bytes':total,'all_original_bytes_unchanged':True,'remote_writes':False,'proof_or_audit_executed':False,'canonical_credit':False}
out='P24_A_SHAPE_METADATA '+json.dumps(result,sort_keys=True)+'\n'
assert len(out.encode())<2000000
print(out,end='',flush=True)
P24_A_SHAPE_METADATA
