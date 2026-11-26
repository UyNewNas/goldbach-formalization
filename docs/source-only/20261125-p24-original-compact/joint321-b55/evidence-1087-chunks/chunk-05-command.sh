set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 -B - <<'P24_1087_CHUNK_5'
from pathlib import Path
import base64,hashlib,json
archive=Path('/workspace/p24-nine-source-promotion-20261126/evidence-1087.tar.gz')
descriptor=Path('/workspace/p24-nine-source-promotion-20261126/evidence-1087-descriptor.json')
raw=archive.read_bytes();desc=descriptor.read_bytes()
assert len(raw)==6810804 and hashlib.sha256(raw).hexdigest()=='28344d7aa71ce2a13ae73cfa695af4fc9b849f444a6142687dc19817be1b3439'
assert len(desc)==8156 and hashlib.sha256(desc).hexdigest()=='6c021f2c9b827e62b36caea5eab5f4a47c0fe203530dce93faadb1bf7a09fb4a'
meta=json.loads(desc)
assert meta['source_pin']=='1087bc663a46352f99b2e9a1da238aaf4b855fdf'
assert meta['original_gate_failed'] is True and meta['canonical_credit'] is False
assert meta['whole_tar_and_all_members_verified'] and meta['all_original_inputs_unchanged']
part=raw[5000000:6000000]
assert len(part)==1000000
assert len(part)+(5==0)*len(desc)<=1048576
assert archive.read_bytes()==raw and descriptor.read_bytes()==desc
result={'chunk_index':5,'chunk_count':7,'offset':5000000,'end':6000000,'raw_bytes':len(part),'chunk_sha256':hashlib.sha256(part).hexdigest(),'archive_bytes':len(raw),'archive_sha256':'28344d7aa71ce2a13ae73cfa695af4fc9b849f444a6142687dc19817be1b3439','data':base64.b64encode(part).decode(),'original_gate_failed':True,'canonical_credit':False}
if 5==0:
 result['descriptor']={'bytes':len(desc),'sha256':'6c021f2c9b827e62b36caea5eab5f4a47c0fe203530dce93faadb1bf7a09fb4a','data':base64.b64encode(desc).decode()}
encoded='P24_1087_EVIDENCE_CHUNK '+json.dumps(result,sort_keys=True)+'\n'
assert len(encoded.encode())<2*1024*1024
print(encoded,end='',flush=True)
P24_1087_CHUNK_5
