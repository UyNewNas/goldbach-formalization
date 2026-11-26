set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
python -B - <<'PY'
import pathlib,hashlib,json,os,subprocess
root=pathlib.Path('/workspace/p2-4-compact-proof-20261125')
s=pathlib.Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
v=json.loads(s.read_text())
target='/workspace/compile-deps/mathlib/.lake/build/lib/lean/Mathlib.ir'
def walk(x,loc='$'):
 if isinstance(x,dict):
  if any(isinstance(y,str) and ('Mathlib.ir' in y) for y in x.values()): print('EXPECTED_ROW '+json.dumps({'location':loc,'row':x},sort_keys=True))
  for k,y in x.items():walk(y,loc+'.'+str(k))
 elif isinstance(x,list):
  for i,y in enumerate(x):walk(y,loc+'['+str(i)+']')
walk(v)
print('SNAPSHOT '+json.dumps({'bytes':s.stat().st_size,'sha256':hashlib.sha256(s.read_bytes()).hexdigest(),'top_keys':list(v)},sort_keys=True))
candidates=[
target,
'/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib/Mathlib.ir',
'/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/lib/Mathlib.ir',
'/workspace/p2-4-compact-proof-20261125/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.ir',
'/workspace/goldbach-p2/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.ir']
for name in candidates:
 p=pathlib.Path(name);row={'path':name,'exists':p.exists(),'is_symlink':p.is_symlink()}
 try:
  st=p.lstat();row['lstat']={'mode':st.st_mode,'bytes':st.st_size,'inode':st.st_ino,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns}
  row['realpath']=str(p.resolve())
  if p.is_file():row.update(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 except FileNotFoundError: pass
 print('CURRENT '+json.dumps(row,sort_keys=True))
for name in ['/workspace','/workspace/compile-deps/mathlib/.lake/build/lib/lean','/tmp']:
 p=pathlib.Path(name);st=os.statvfs(p);print('FS '+json.dumps({'path':name,'free':st.f_bavail*st.f_frsize,'device':p.stat().st_dev,'realpath':str(p.resolve())}))
print('HEAD '+subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip())
r=root/'.lake/p2-private/records.json';print('REGISTRY '+json.dumps({'bytes':r.stat().st_size,'sha256':hashlib.sha256(r.read_bytes()).hexdigest()}))
PY
