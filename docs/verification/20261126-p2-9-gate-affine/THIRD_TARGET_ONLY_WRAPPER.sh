python3 - <<'PY_GATE_AFFINE'
import urllib.request,json,base64,hashlib,pathlib,traceback,datetime
blob='141762c848a161fac6e1352e779a5c1b6a0d33e3'
d=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=60))
assert d['encoding']=='base64'
b=base64.b64decode(d['content']);assert len(b)==30639
assert hashlib.sha256(b).hexdigest()=='896fa317074b2ab2ed4a64f487837ef98b9fde2c0223c13e5c7c78c8404ebd33'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode('utf-8');out=pathlib.Path('/workspace/p29-gate-affine-20261126-ba9b1989/verification')
assert out.is_dir() and not (out/'driver-constructor-if-repair-v2.py').exists(),'Existing or missing continuation: read receipt; do not resubmit.'
try:
 exec(compile(text,'p29-gate-affine-constructor-if-repair-v2','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
except BaseException as e:
 if out.is_dir() and (out/'driver-constructor-if-repair-v2.py').is_file() and (out/'driver-constructor-if-repair-v2.py').read_bytes()==b:
  with (out/'OUTER_FAILURE-constructor-if-repair-v2.json').open('x') as f:
   json.dump({'schema':'p29_gate_outer_initialization_or_stage_failure_v1','error':str(e),'traceback':traceback.format_exc(),'controller_git_blob':blob,'controller_sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_raw_stage_logs_preserved':True},f,indent=2);f.write('\n')
 raise
PY_GATE_AFFINE
