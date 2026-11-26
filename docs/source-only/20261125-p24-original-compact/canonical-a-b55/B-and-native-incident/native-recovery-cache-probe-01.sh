set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python -B - <<'PY'
import pathlib,json,os,zipfile,hashlib
paths=['/root/.cache/mathlib','/workspace/.compile-home/.cache','/workspace/compile-deps','/workspace/compile-deps/mathlib/Cache','/workspace/p2-private-20261124/.lake/p2-private/native-cache/repack-45362510169','/workspace/p2-private-20261124/.lake/p2-private/native-cache/kernel-metadata.zip']
for name in paths:
 p=pathlib.Path(name);r={'path':name,'exists':p.exists(),'is_symlink':p.is_symlink()}
 if p.exists():
  r.update(bytes=p.stat().st_size,is_dir=p.is_dir())
  if p.is_dir():
   items=sorted(p.iterdir());r['children']=[x.name for x in items[:80]];r['children_count']=len(items)
   if '.cache' in name:
    a=list(p.rglob('*.ltar'));r['ltar_count']=len(a);r['ltar_bytes']=sum(x.stat().st_size for x in a);r['ltar_first5']=[str(x) for x in a[:5]]
  elif p.suffix=='.zip':
   with zipfile.ZipFile(p) as z:
    n=z.infolist();r['zip_members']=len(n);r['zip_raw_bytes']=sum(x.file_size for x in n);r['mathlib_native_members']=[{'name':x.filename,'bytes':x.file_size} for x in n if ('Mathlib/' in x.filename or 'Mathlib.' in x.filename) and any(s in pathlib.PurePosixPath(x.filename).suffixes for s in ('.olean','.ir'))][:20]
 print('CACHE_PATH '+json.dumps(r,sort_keys=True))
cache=pathlib.Path('/workspace/compile-deps/mathlib/Cache')
if cache.is_dir():
 for name in ['IO.lean','Requests.lean','Main.lean','Hashing.lean','Lean.lean']:
  p=cache/name
  if p.is_file():
   b=p.read_bytes();print('CACHE_SOURCE '+json.dumps({'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}))
PY
