python3 - <<'PY'
import urllib.request,json,base64,hashlib
blob='5daf4a3183e6581099bb7fad6812d037decaa34b'
r=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=45))
assert r['encoding']=='base64'
b=base64.b64decode(r['content'])
assert len(b)==8005 and hashlib.sha256(b).hexdigest()=='bcff80ededb5478ba85bcec98ffdebc59780cd03b28b6e4d7c96b33aa7011c70'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode()
exec(compile(text,'p29-nonradial-existing-object-export-v2','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
PY
