python3 - <<'PY'
import urllib.request,base64,json,hashlib
r=json.load(urllib.request.urlopen('https://api.github.com/repos/UyNewNas/goldbach-formalization/git/blobs/d99a7bf077d05c7c7b6b5205c1fa717edfd98642'))
b=base64.b64decode(r['content']);assert len(b)==48398 and hashlib.sha256(b).hexdigest()=='239b105f1da467518d3bd2c6de86e0b8934aa2196a4b976afa9566d6ee9a0536'
assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()=='d99a7bf077d05c7c7b6b5205c1fa717edfd98642'
text=b.decode();exec(compile(text,'nonunit-quotient-p1-norm-fqn-002-resume.py','exec'),{'SOURCE_TEXT':text,'__name__':'__main__'})
PY
