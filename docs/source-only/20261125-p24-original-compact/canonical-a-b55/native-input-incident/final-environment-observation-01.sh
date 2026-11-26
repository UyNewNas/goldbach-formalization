set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
python -B - <<'PY'
import pathlib,json,hashlib,subprocess,datetime
root=pathlib.Path('/workspace/p2-4-compact-proof-20261125')
snapshot=pathlib.Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
registry=root/'.lake/p2-private/records.json'
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
v={'observed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_pin':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),'tracked_status':subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True),'registry_sha256':digest(registry),'snapshot_sha256':digest(snapshot),'mathlib_build_lib_exists':pathlib.Path('/workspace/compile-deps/mathlib/.lake/build/lib/lean').exists(),'Mathlib_ir_exists':pathlib.Path('/workspace/compile-deps/mathlib/.lake/build/lib/lean/Mathlib.ir').exists(),'qualification_repeated':False,'files_written':0,'proof_credit':False}
assert v['source_pin']=='b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
assert not v['tracked_status']
assert v['registry_sha256']=='3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445'
assert v['snapshot_sha256']=='ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
print('P24_FINAL_ENVIRONMENT_OBSERVATION '+json.dumps(v,sort_keys=True),flush=True)
PY
