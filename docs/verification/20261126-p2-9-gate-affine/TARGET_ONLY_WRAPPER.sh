python3 - <<'PY_GATE_AFFINE'
import urllib.request,json,base64,hashlib,pathlib,traceback,datetime
blob='a99275730903c7a9a3aaaf75426cd435bd321112'
d=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=60))
assert d['encoding']=='base64'
b=base64.b64decode(d['content']);assert len(b)==29351
assert hashlib.sha256(b).hexdigest()=='cdc7420eb1052cca1575d388286053002ca3fbf0c6dd5ff02c0c775f40d6d295'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode('utf-8');out=pathlib.Path('/workspace/p29-gate-affine-20261126-ba9b1989/verification')
assert out.is_dir() and not (out/'driver-proof-repair-v1.py').exists(),'Existing or missing continuation: read receipt; do not resubmit.'
try:
 exec(compile(text,'p29-gate-affine-proof-repair-v1','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
except BaseException as e:
 if out.is_dir() and (out/'driver-proof-repair-v1.py').is_file() and (out/'driver-proof-repair-v1.py').read_bytes()==b:
  with (out/'OUTER_FAILURE-proof-repair-v1.json').open('x') as f:
   json.dump({'schema':'p29_gate_outer_initialization_or_stage_failure_v1','error':str(e),'traceback':traceback.format_exc(),'controller_git_blob':blob,'controller_sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_raw_stage_logs_preserved':True},f,indent=2);f.write('\n')
 raise
PY_GATE_AFFINE
