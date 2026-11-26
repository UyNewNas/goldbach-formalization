python3 - <<'PY'
import urllib.request,json,base64,hashlib
blob='b6cfa01ec8b2d62deae66f8116be57c0fe23bf40'
r=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=45))
assert r['encoding']=='base64'
b=base64.b64decode(r['content'])
assert len(b)==12879 and hashlib.sha256(b).hexdigest()=='be6573d90259a24a41452b3047b60c6f8fcb56511c451e2776695490f8c9e05c'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode()
exec(compile(text,'p29-nonradial-P3-byte-receiver','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
PY
