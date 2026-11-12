"""Exact-byte source-only installer. No Lean or Lake invocation."""
import argparse,json,pathlib,hashlib
p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True);p.add_argument('--manifest',type=pathlib.Path,required=True);p.add_argument('--dest',type=pathlib.Path,required=True);a=p.parse_args()
m=json.loads(a.manifest.read_text())
assert not m['missing'], 'Unresolved imports; do not publish partial closure as complete'
assert not a.dest.exists(),'Require new isolated destination'
a.dest.mkdir(parents=True)
for r in m['modules']:
 b=(a.source/r['source']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'],r
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob'],r
 q=a.dest/r['install_path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b)
for name,h in [('lean-toolchain','fd85b262bf1c734663aa8292b0101f672168788f'),('lake-manifest.json','86cb11a7a4b1c8ee3cd1d583985b4c7877933a4f'),('lakefile.toml','c7b839a2240d9960fb1f01f0e8808a9459935e0e')]:
 b=(a.source/name).read_bytes();assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==h;(a.dest/name).write_bytes(b)
(a.dest/'P4_STAGE_RECEIPT.json').write_text(json.dumps(m,indent=2))
print('MATERIALIZED_UNCOMPILED',len(m['modules']))
