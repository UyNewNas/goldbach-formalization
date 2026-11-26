python3 - <<'PY'
import urllib.request,base64,json,hashlib
r=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/0cca5ade7ba76d5308c5db921ec7c8b1103dbee6'))
b=base64.b64decode(r['content']);assert len(b)==41009 and hashlib.sha256(b).hexdigest()=='c970948d0848815c2d8dd4462c506e6842efc60415df5b2a9bfc3e14c881ebba'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()=='0cca5ade7ba76d5308c5db921ec7c8b1103dbee6'
text=b.decode();exec(compile(text,'nonunit-quotient-p1-controller-v1.py','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
PY