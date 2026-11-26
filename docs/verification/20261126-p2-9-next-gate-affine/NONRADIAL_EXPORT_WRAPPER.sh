python3 - <<'PY'
import urllib.request,json,base64,hashlib
blob='5ad1322132859326ac4a1279b4cd2bc3c9317304'
r=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/'+blob,timeout=45))
assert r['encoding']=='base64'
b=base64.b64decode(r['content'])
assert len(b)==7859 and hashlib.sha256(b).hexdigest()=='531e9a671367592153c2bab487d6af36cd3c892db0fa475525bc4e54937aa75f'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob
text=b.decode()
exec(compile(text,'p29-nonradial-existing-object-export','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
PY
