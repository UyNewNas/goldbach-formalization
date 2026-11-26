python3 - <<'PY_GATE_AFFINE'
import urllib.request,json,base64,hashlib,pathlib,traceback,datetime
blob='2aa3356118504551d93b2000d9968d6b547d3fad'
d=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=60))
assert d['encoding']=='base64'
b=base64.b64decode(d['content']);assert len(b)==29856
assert hashlib.sha256(b).hexdigest()=='a9b7b6685df439c8007cfdf1ee4b43b6dde854aa9bee0e1c2d4996b3805bf86b'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode('utf-8');out=pathlib.Path('/workspace/p29-gate-affine-20261126-ba9b1989/verification')
assert not out.parent.exists(),'Existing Gate receiver: read receipt; do not resubmit.'
try:
 exec(compile(text,'p29-gate-affine-controller-v1','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
except BaseException as e:
 if out.is_dir() and (out/'driver.py').is_file() and (out/'driver.py').read_bytes()==b:
  with (out/'OUTER_FAILURE.json').open('x') as f:
   json.dump({'schema':'p29_gate_outer_initialization_or_stage_failure_v1','error':str(e),'traceback':traceback.format_exc(),'controller_git_blob':blob,'controller_sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'original_raw_stage_logs_preserved':True},f,indent=2);f.write('\n')
 raise
PY_GATE_AFFINE
