#!/usr/bin/env python3
"""Assemble exact primary-uploaded data, then run the frozen joint probe."""
from pathlib import Path
import hashlib,json,subprocess,sys
ROOT=Path('/workspace/p2-1-original96-20261126')
assert Path.cwd().resolve()==ROOT
PINS={'verification/part2/original96/joint/Joint.lean': '9c942ceef4d5ca9b4f87bdf1e3637e73f3de34a155396e8808c7423738edd772', 'verification/part2/original96/joint/freeze_joint_reference.py': '5af69fa31010ebf08f0189eae29b278ce588e074673c9cc1fed7c1d6cf33a901', 'verification/part2/original96/joint/run_joint_increment.py': 'd4be3348f0d1d12dc4721409fd7b89b9563203b8a99bbb0aaeaf7ecfc610f664', 'verification/part2/original96/P160RemainingContract.lean': '0d0a3b05ff96de4e03010c0399b4b2b0c27eed75749f232886f911be40a33e55'}
PARTS=[{'path': 'verification/part2/original96/joint/transport-parts/reference-00.part', 'bytes': 32000, 'sha256': '77ed1572c62f0deb6710bf88fc2c5484d4d259f2fcbe4969393d236aa234142f'}, {'path': 'verification/part2/original96/joint/transport-parts/reference-01.part', 'bytes': 32000, 'sha256': '9cc3000161a898cd629c5afc42972689c4e9b76bb59cec3f9087cf527e2f1f13'}, {'path': 'verification/part2/original96/joint/transport-parts/reference-02.part', 'bytes': 32000, 'sha256': '3e5365a5fd6110bb6cc6e982c5e047f4be15f30690120f77b3e7928907d9fd72'}, {'path': 'verification/part2/original96/joint/transport-parts/reference-03.part', 'bytes': 32000, 'sha256': '0d355b6e78748adaf5f48c2cc9e5cd23a9f81266b4c0495602e101e9106653ec'}, {'path': 'verification/part2/original96/joint/transport-parts/reference-04.part', 'bytes': 27012, 'sha256': 'eb9839e391d67169c759c6f077b72596e0497e55f69cdfa75387a752678ede44'}]
EXPECTED='09f62777eb9996fb7c7d41e27238afec282b904a8072cc9555d055c6ec43cfc5'
REFERENCE=ROOT/'verification/part2/original96/joint/joint-reference.json.xz'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def check():
 for rel,wanted in PINS.items():
  assert sha(ROOT/rel)==wanted,rel
check()
self_before=sha(__file__)
if not REFERENCE.exists():
 chunks=[]
 for item in PARTS:
  b=(ROOT/item['path']).read_bytes()
  assert len(b)==item['bytes'] and hashlib.sha256(b).hexdigest()==item['sha256']
  chunks.append(b)
 data=b''.join(chunks)
 assert hashlib.sha256(data).hexdigest()==EXPECTED
 REFERENCE.write_bytes(data)
assert sha(REFERENCE)==EXPECTED
cmd=[sys.executable,'-B','verification/part2/original96/joint/run_joint_increment.py',
 '--reference-sha256',EXPECTED,'--emit-base64']
r=subprocess.run(cmd,cwd=ROOT)
check()
assert sha(__file__)==self_before and sha(REFERENCE)==EXPECTED
print('P21_JOINT_LAUNCH '+json.dumps({'argv':cmd,'exit_code':r.returncode,'primary_inputs':PINS,'launcher_sha256':self_before,'reference_sha256':EXPECTED}),flush=True)
if r.returncode:
 attempts=sorted((ROOT/'evidence/original96-joint-compatibility').glob('attempt-*'),key=lambda p:p.stat().st_mtime)
 if attempts:
  for name in ['failure.json','joint.log']:
   p=attempts[-1]/name
   if p.is_file():print(str(p)+'\n'+p.read_text(errors='replace')[-14000:],flush=True)
raise SystemExit(r.returncode)
