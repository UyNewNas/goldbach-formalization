set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python -B - <<'PY'
import collections,gzip,hashlib,json,os,pathlib,subprocess,time
root=pathlib.Path('/workspace/p2-4-compact-proof-20261125')
snap=pathlib.Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json')
pin='b55fa93d39e6a4ddf2abd37b9b8481078e329f70'
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==pin
sb=snap.read_bytes();assert hashlib.sha256(sb).hexdigest()=='ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27'
v=json.loads(sb);files=v['files'];assert isinstance(files,dict)
reg=root/'.lake/p2-private/records.json';rb=reg.read_bytes();rh=hashlib.sha256(rb).hexdigest();assert rh=='3e71aab7f7b54dea5bddf99a09cc87310105979237a639e07f8988403dc74445'
counts=collections.Counter();groups=collections.defaultdict(lambda:collections.Counter());mismatch=[];present_expected_bytes=0
for name,row in files.items():
 p=pathlib.Path(name);expected_size=row['bytes']
 try:
  st=p.stat()
  if not p.is_file():state='not_file'
  elif st.st_size!=expected_size:state='size_changed'
  else:state='present_same_size';present_expected_bytes+=expected_size
 except FileNotFoundError:state='missing'
 counts[state]+=1
 group='/workspace/compile-deps/mathlib' if name.startswith('/workspace/compile-deps/mathlib/') else '/workspace/toolchains' if name.startswith('/workspace/toolchains/') else '/workspace/p2-private-20261124' if name.startswith('/workspace/p2-private-20261124/') else '/workspace/goldbach-p2' if name.startswith('/workspace/goldbach-p2/') else 'other'
 groups[group][state]+=1
 if state!='present_same_size':mismatch.append({'path':name,'expected':row,'state':state})
cacheinfo=[]
candidates=[pathlib.Path.home()/'.cache/mathlib',pathlib.Path('/workspace/.cache/mathlib'),pathlib.Path('/workspace/compile-deps/mathlib/.cache'),pathlib.Path('/workspace/compile-deps/mathlib/.lake/build'),pathlib.Path('/workspace/compile-deps/mathlib/.lake/build/lib'),pathlib.Path('/workspace/compile-deps/mathlib/.lake/build/lib/lean'),pathlib.Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169'),pathlib.Path('/workspace/p2-private-20261124/.lake/p2-private/native-cache')]
for p in candidates:
 r={'path':str(p),'exists':p.exists(),'is_symlink':p.is_symlink()}
 if p.exists():
  st=p.stat();r.update(bytes=st.st_size,mtime_ns=st.st_mtime_ns,ctime_ns=st.st_ctime_ns,realpath=str(p.resolve()),is_dir=p.is_dir())
  if p.is_dir():
   children=sorted(p.iterdir());r['direct_child_count']=len(children);r['first_30_children']=[q.name for q in children[:30]]
   if 'mathlib' in str(p) and '.cache' in str(p):
    ltars=list(p.rglob('*.ltar'));r['ltar_count']=len(ltars);r['ltar_total_bytes']=sum(q.stat().st_size for q in ltars if q.is_file());r['first_10_ltar_paths']=[str(q) for q in ltars[:10]]
 cacheinfo.append(r)
out=pathlib.Path('/workspace/p24-native-input-incident-20261126/attempt-001');out.mkdir(parents=True,exist_ok=False)
full={'source_pin':pin,'snapshot_sha256':hashlib.sha256(sb).hexdigest(),'registry_sha256':rh,'files_count':len(files),'counts':dict(counts),'groups':{k:dict(x) for k,x in groups.items()},'mismatches':mismatch,'cache_paths':cacheinfo,'present_same_size_sha256_not_checked':True,'native_files_written':0,'qualification_run':False,'proof_credit':False}
payload=(json.dumps(full,sort_keys=True,indent=2)+'\n').encode();gz=gzip.compress(payload,mtime=0)
q=out/'complete-missing-input-inventory.json.gz'
with q.open('xb') as f:f.write(gz);f.flush();os.fsync(f.fileno())
assert hashlib.sha256(snap.read_bytes()).hexdigest()==hashlib.sha256(sb).hexdigest()
assert hashlib.sha256(reg.read_bytes()).hexdigest()==rh
summary={k:x for k,x in full.items() if k!='mismatches'}
summary['mismatch_expected_bytes']=sum(x['expected']['bytes'] for x in mismatch)
summary['mismatches_first_12']=mismatch[:12]
summary['inventory']={'path':str(q),'bytes':len(gz),'sha256':hashlib.sha256(gz).hexdigest(),'raw_bytes':len(payload),'raw_sha256':hashlib.sha256(payload).hexdigest()}
summary['workspace_free_after']=os.statvfs('/workspace').f_bavail*os.statvfs('/workspace').f_frsize
sp=out/'summary.json'
with sp.open('x') as f:json.dump(summary,f,sort_keys=True,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
print('P24_NATIVE_INPUT_INCIDENT '+json.dumps(summary,sort_keys=True),flush=True)
PY
