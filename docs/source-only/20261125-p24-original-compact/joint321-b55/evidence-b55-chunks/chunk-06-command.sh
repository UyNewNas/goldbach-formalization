set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'P24_B55_CHUNK_6'
from pathlib import Path
import base64,hashlib,json
archive=Path('/workspace/p24-integration-proof-repairs-20261126/evidence-b55.tar.gz')
descriptor=Path('/workspace/p24-integration-proof-repairs-20261126/evidence-b55-descriptor.json')
raw=archive.read_bytes();desc=descriptor.read_bytes()
assert len(raw)==6838405 and hashlib.sha256(raw).hexdigest()=='23d612dc0fb8266cb8928e1d11f69e4ebb9a4ed0e1429ddad91751071dc39c2c'
assert len(desc)==9053 and hashlib.sha256(desc).hexdigest()=='282f62e67dbe7e280afdcb413aaf086952b314368b57334c050d2d0b6a548799'
meta=json.loads(desc)
assert meta['source_pin']=='b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
assert meta['original_gate_failed'] is False and meta['canonical_credit'] is False
assert meta['whole_tar_and_all_members_verified'] and meta['all_original_inputs_unchanged']
part=raw[6000000:6838405]
assert len(part)==838405
assert len(part)+(6==0)*len(desc)<=1048576
assert archive.read_bytes()==raw and descriptor.read_bytes()==desc
result={'chunk_index':6,'chunk_count':7,'offset':6000000,'end':6838405,'raw_bytes':len(part),'chunk_sha256':hashlib.sha256(part).hexdigest(),'archive_bytes':len(raw),'archive_sha256':'23d612dc0fb8266cb8928e1d11f69e4ebb9a4ed0e1429ddad91751071dc39c2c','data':base64.b64encode(part).decode(),'original_gate_failed':False,'canonical_credit':False}
if 6==0:
 result['descriptor']={'bytes':len(desc),'sha256':'282f62e67dbe7e280afdcb413aaf086952b314368b57334c050d2d0b6a548799','data':base64.b64encode(desc).decode()}
encoded='P24_B55_EVIDENCE_CHUNK '+json.dumps(result,sort_keys=True)+'\n'
assert len(encoded.encode())<2*1024*1024
print(encoded,end='',flush=True)
P24_B55_CHUNK_6
