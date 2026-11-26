set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 - <<'PY'
import base64,gzip,hashlib,json,pathlib,subprocess
root=pathlib.Path('/workspace/p2-4-compact-proof-20261125')
pin=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert pin=='6e616f4e0372555f7a78bcdba3e198d0e277eec8', pin
reg=root/'.lake/p2-private/records.json'
reg_before=hashlib.sha256(reg.read_bytes()).hexdigest()
p=pathlib.Path('/workspace/p24-owned-flags-preflight-repro-20261126/attempt-003/owned-flags.log')
raw=p.read_bytes()
assert len(raw)==2933052
assert hashlib.sha256(raw).hexdigest()=='96a2cd3617b89ade3f607da66645d3d2421c9dbf4cd968ef8b99f2268ec307a4'
packed=gzip.compress(raw,mtime=0)
assert reg_before==hashlib.sha256(reg.read_bytes()).hexdigest()
print(json.dumps({'scope':'read-only exact existing log; no Lean execution','canonical_source_pin':pin,'registry_before_after':reg_before,'path':str(p),'raw_bytes':len(raw),'raw_sha256':hashlib.sha256(raw).hexdigest(),'gzip_bytes':len(packed),'gzip_sha256':hashlib.sha256(packed).hexdigest(),'gzip_base64':base64.b64encode(packed).decode(),'all_credit':False},separators=(',',':')))
PY
