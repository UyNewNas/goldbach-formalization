set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
python -B - <<'PY'
import hashlib,json,pathlib,urllib.request,urllib.error,subprocess
pin='e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
root=pathlib.Path('/workspace/compile-deps/mathlib')
actual=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()
assert actual==pin,(actual,pin)
out=pathlib.Path('/workspace/p24-native-input-incident-20261126/official-index-probe-001');out.mkdir(parents=True,exist_ok=False)
rows=[]
for container in ['mathlib4-master','mathlib4']:
 url='https://lakecache.blob.core.windows.net/'+container+'/c/'+pin
 row={'url':url,'method':'GET','timeout_seconds':20}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'p24-exact-native-recovery-readonly-index/1'})
  with urllib.request.urlopen(req,timeout=20) as r:
   b=r.read(5000001);assert len(b)<=5000000,'index over cap'
   row.update(http_status=r.status,final_url=r.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),content_type=r.headers.get('Content-Type'))
  p=out/(container+'-commit-index.bin')
  with p.open('xb') as f:f.write(b)
  row['path']=str(p);row['first_300_utf8']=b[:300].decode('utf8',errors='replace')
 except urllib.error.HTTPError as e:row.update(http_status=e.code,error=str(e))
 except Exception as e:row.update(error=type(e).__name__+': '+str(e))
 rows.append(row);print('OFFICIAL_INDEX_PROBE '+json.dumps(row,sort_keys=True),flush=True)
result={'mathlib_pin':pin,'rows':rows,'native_files_written':0,'qualification_run':False,'proof_credit':False}
(out/'receipt.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
leantar=pathlib.Path('/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leantar')
print('LEANTAR '+json.dumps({'path':str(leantar),'exists':leantar.is_file(),'bytes':leantar.stat().st_size if leantar.is_file() else None,'sha256':hashlib.sha256(leantar.read_bytes()).hexdigest() if leantar.is_file() else None}))
PY
