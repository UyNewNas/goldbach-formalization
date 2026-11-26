set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_A_EVIDENCE'
from pathlib import Path
import base64,gzip,hashlib,io,json,os,re,subprocess,tarfile
root=Path.cwd()
pin='b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
assert subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()==pin
def digest_bytes(raw): return hashlib.sha256(raw).hexdigest()
def digest(path):
 with Path(path).open('rb') as stream: return hashlib.file_digest(stream,'sha256').hexdigest()
assert digest(root/'verification/part2/run_winner9_private_audit.py')=='571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5'
out=Path('/workspace/p24-current-a-acceptance-evidence-20261126/attempt-001')
assert not out.exists()
items={}
origins={}
def add(name,path):
 path=Path(path);raw=path.read_bytes();items[name]=raw
 origins[name]={'path':str(path),'bytes':len(raw),'sha256':digest_bytes(raw)}
 return raw
cap=root/'.lake/p24-owned-capacity/b55-A-attempt-001'
add('capacity/capacity-diagnostic.json',cap/'capacity-diagnostic.json')
assert digest_bytes(items['capacity/capacity-diagnostic.json'])=='47734ae76baf0a59f4f381e491ff4fc2ed62669a2fd81131af24635bb94d20a9'
add('capacity/capacity-sizes.json',cap/'capacity-sizes.json')
owned=Path('/workspace/p24-eleven-source-canonical-owned-20261126/attempt-001')
for name in ['receipt.json','original-artifact-index.json','registry-before-audit.json.gz.index.json','registry-after-audit.json.gz.index.json','prerequisite-result.json']:
 add('owned-eleven/'+name,owned/name)
assert digest_bytes(items['owned-eleven/receipt.json'])=='ae098dd1a27bfc4a0b5965db2e4c554d486a948c36f2f462fe2101678e14d13a'
assert digest_bytes(items['owned-eleven/original-artifact-index.json'])=='bdde78a78d855ed691b522bf2f19d6589f586e80e2485aacbcce3f4a602ec5ba'
registry=root/'.lake/p2-private/records.json'
raw_registry=registry.read_bytes()
A='ImbalancedChen.P2OriginalCompactArchivedTotalCandidate'
row=json.loads(raw_registry)[A]
assert row['source_sha256']=='03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd'
assert row['object_sha256']=='d02eb743f6e8dfbe27182b46f9b2f8dd0c1a8482a6f0236207557b997bb629b6'
assert row['exit_code']==0 and row['new_strict_compile'] is True
items['canonical-A/selected-record.json']=(json.dumps(row,indent=2,sort_keys=True)+'\n').encode()
alog=root/row['log'];assert alog==root/'.lake/p2-private/logs/ImbalancedChen.P2OriginalCompactArchivedTotalCandidate.attempt5.log'
log=add('canonical-A/original-module.log',alog)
blocks=[(int(s),int(n)) for s,n in re.findall(rb'^P24_Q80_CHECKED_BLOCK name=\S+ start=(\d+) count=(\d+)$',log,re.M)]
assert blocks==[(32769+64*i,64) for i in range(2048)]
assert b'P24_Q80_ARCHIVED_DONE checked_blocks=2048 computed_nodes=131072 query_index=163840' in log
source=root/'ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean'
add('canonical-A/source.lean',source)
assert digest_bytes(items['canonical-A/source.lean'])==row['source_sha256']
obj=root/'.lake/p2-private/lib/ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.olean'
assert digest(obj)==row['object_sha256']
metadata={'source_pin':pin,'current_registry_sha256':digest_bytes(raw_registry),'A_object_sha256':digest(obj),'A_object_bytes':obj.stat().st_size,'block_log_exact_2048_sequence_verified':True,'origins':origins,'new_proof_credit':False}
items['READONLY_BINDINGS.json']=(json.dumps(metadata,indent=2,sort_keys=True)+'\n').encode()
index={name:{'bytes':len(raw),'sha256':digest_bytes(raw)} for name,raw in items.items()}
items['FILES.json']=(json.dumps(index,indent=2,sort_keys=True)+'\n').encode()
memory=io.BytesIO()
with tarfile.open(fileobj=memory,mode='w') as tar:
 for name in sorted(items):
  raw=items[name];info=tarfile.TarInfo(name);info.size=len(raw);info.mode=0o644;info.mtime=0
  tar.addfile(info,io.BytesIO(raw))
tar_raw=memory.getvalue();compressed=gzip.compress(tar_raw,compresslevel=9,mtime=0)
assert gzip.decompress(compressed)==tar_raw and len(compressed)<1400000
assert registry.read_bytes()==raw_registry
assert digest(obj)==row['object_sha256']
for name,binding in origins.items(): assert digest(binding['path'])==binding['sha256']
out.mkdir(parents=True)
path=out/'a-capacity-owned-eleven.tar.gz'
with path.open('xb') as stream:stream.write(compressed)
assert path.read_bytes()==compressed
descriptor={'path':str(path),'bytes':len(compressed),'sha256':digest_bytes(compressed),'tar_bytes':len(tar_raw),'tar_sha256':digest_bytes(tar_raw),'members':{name:{'bytes':len(raw),'sha256':digest_bytes(raw)} for name,raw in items.items()},'source_pin':pin,'current_registry_sha256':digest_bytes(raw_registry),'new_proof_credit':False}
with (out/'descriptor.json').open('x') as stream:stream.write(json.dumps(descriptor,indent=2,sort_keys=True)+'\n')
disk=os.statvfs(out);descriptor['free_bytes_after']=disk.f_bavail*disk.f_frsize
print('P24_A_EVIDENCE_DESCRIPTOR '+json.dumps(descriptor,sort_keys=True))
print('P24_A_EVIDENCE_BASE64 '+base64.b64encode(compressed).decode())
P24_A_EVIDENCE
