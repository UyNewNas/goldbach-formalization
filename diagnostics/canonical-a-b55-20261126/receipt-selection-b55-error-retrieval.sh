set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
python3 -B - <<'PY'
from pathlib import Path
import gzip,hashlib,json,os
root=Path('/workspace/p24-current-audit-receipt-selection-b55-20261126/attempt-001')
for name in ['receipt.json','errors.json.gz','zero321-result.json']:
 p=root/name;b=p.read_bytes();data=gzip.decompress(b) if name.endswith('.gz') else b
 print(json.dumps({'file':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'data':json.loads(data)},ensure_ascii=False))
v=os.statvfs('/workspace');print(json.dumps({'free_bytes':v.f_bavail*v.f_frsize}))
PY
