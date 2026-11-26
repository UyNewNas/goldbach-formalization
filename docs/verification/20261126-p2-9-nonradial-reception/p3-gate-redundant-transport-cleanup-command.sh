python3 - <<'PY'
import sys
sys.dont_write_bytecode=True
import urllib.request,json,base64,hashlib
blob='b5d9f924ccd9cd47d2cb39cecfcf18c1c4d71572'
r=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=45))
assert r['encoding']=='base64'
b=base64.b64decode(r['content'])
assert len(b)==7402 and hashlib.sha256(b).hexdigest()=='28b735ef13a3c58a89e262a7d25419a62725bef51807c450c8ae5e0d8d9677a3'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode()
exec(compile(text,'p29-single-redundant-gate-transport-cleanup','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
PY
