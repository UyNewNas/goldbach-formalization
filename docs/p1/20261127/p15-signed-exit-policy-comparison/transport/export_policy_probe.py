from pathlib import Path
import base64,hashlib,json,zlib

roots={
 'policy':Path('/workspace/p1-complete-proof/20261127-p15-signed-exit-policy-probe-v1'),
}
files=[]
for label,root in roots.items():
    assert root.is_dir() and root.resolve()==root
    for p in sorted(root.rglob('*')):
        if p.is_dir():continue
        assert p.is_file() and not p.is_symlink()
        b=p.read_bytes()
        files.append({'path':label+'/'+str(p.relative_to(root)),'remote':str(p),
                      'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),
                      'base64':base64.b64encode(b).decode()})
raw=json.dumps({'schema':'p15_next_exact_probe_export_v1','files':files},sort_keys=True,separators=(',',':')).encode()
print(json.dumps({'schema':'zlib-base64-exact-files-v1','file_count':len(files),'raw_json_bytes':len(raw),
                  'raw_json_sha256':hashlib.sha256(raw).hexdigest(),
                  'payload':base64.b64encode(zlib.compress(raw,9)).decode()},separators=(',',':')))
