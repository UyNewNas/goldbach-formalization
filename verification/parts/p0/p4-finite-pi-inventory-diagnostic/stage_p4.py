"""Exact-byte source-only installer. No Lean or Lake invocation."""
import argparse,json,pathlib,hashlib
p=argparse.ArgumentParser();p.add_argument('--source',type=pathlib.Path,required=True);p.add_argument('--manifest',type=pathlib.Path,required=True);p.add_argument('--dest',type=pathlib.Path,required=True);a=p.parse_args()
import os
raw=a.manifest.read_bytes()
assert hashlib.sha256(raw).hexdigest()==os.environ['EXPECTED_MANIFEST'], 'Historical candidate manifest changed'
m=json.loads(raw)
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
# Install the identical accepted repair from same-rho run 44584300242.
# Keep every original source binding and strict inventory gate.
overlay_path = 'ImbalancedChen/FinitePiIntegral.lean'
preimage = '22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c'
postimage = '2e4fe57169a1a1e71b354008c0ad2639b52e7170a5e0e5129992437cc0931938'
overlay_blob = 'c548ea28e787ea24a3fce871f87be799d93682e9'
matches = [r for r in m['modules'] if r['install_path'] == overlay_path]
assert len(matches) == 1 and matches[0]['sha256'] == preimage
dest = a.dest / overlay_path
original = dest.read_bytes()
donor = pathlib.Path(__file__).resolve().parent.parent / 'p4-same-rho-api' / 'FinitePiIntegral.lean'
fixed = donor.read_bytes()
assert hashlib.sha256(original).hexdigest() == preimage
assert hashlib.sha256(fixed).hexdigest() == postimage
assert hashlib.sha1(b'blob ' + str(len(fixed)).encode() + b'\0' + fixed).hexdigest() == overlay_blob
import_line = b'import Mathlib.MeasureTheory.Integral.Pi\n'
assert import_line not in original and fixed.count(import_line) == 1
assert fixed.replace(import_line, b'', 1) == original
dest.write_bytes(fixed)
assert hashlib.sha256(dest.read_bytes()).hexdigest() == postimage
receipt = {'status': 'MATERIALIZED_UNCOMPILED', 'module': matches[0]['module'],
           'historical_failed_run': 45709491446, 'donor_strict_run': 44584300242,
           'donor_source_commit': '32a6363f93a1c3be2770fd0d773f4b08ced8fded',
           'donor_blob': overlay_blob, 'original_sha256': preimage,
           'effective_sha256': postimage, 'owner_gate_relaxed': False}
(a.dest/'FINITE_PI_OVERLAY.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('FINITE_PI_OVERLAY', json.dumps(receipt, sort_keys=True))

# Reuse the exact strict FirstExitTree donor; the other overlay stays in place.
overlay_path = 'ImbalancedChen/FirstExitTree.lean'
preimage = '6ab5eeb136969f76afc8fcc83dfa211985e0b7ffe85e89dab0702f381ad42a6b'
postimage = 'e12ba076eb7c79170b8f1dc18171dbb9fa94af14232018d7896a817a0f12fa72'
overlay_blob = '1163ab648424e3b30aff8699f03fb35e5790c2a7'
matches = [r for r in m['modules'] if r['install_path'] == overlay_path]
assert len(matches) == 1 and matches[0]['sha256'] == preimage
dest = a.dest / overlay_path
original = dest.read_bytes()
donor = pathlib.Path(__file__).resolve().parent.parent / 'p1-cap-api' / 'FirstExitTree.lean'
fixed = donor.read_bytes()
assert hashlib.sha256(original).hexdigest() == preimage
assert hashlib.sha256(fixed).hexdigest() == postimage
assert hashlib.sha1(b'blob ' + str(len(fixed)).encode() + b'\0' + fixed).hexdigest() == overlay_blob
assert [s for s in original.splitlines() if s.startswith(b'import ')] == [s for s in fixed.splitlines() if s.startswith(b'import ')]
dest.write_bytes(fixed)
assert hashlib.sha256(dest.read_bytes()).hexdigest() == postimage
receipt = {'status': 'MATERIALIZED_UNCOMPILED', 'module': matches[0]['module'],
           'historical_failed_run': 45717803056, 'donor_strict_run': 44043564382,
           'donor_source_commit': '1ea9409fd109db5f183178acdac47ef0cfb76d91',
           'donor_blob': overlay_blob, 'original_sha256': preimage,
           'effective_sha256': postimage, 'owner_gate_relaxed': False}
(a.dest/'FIRST_EXIT_TREE_OVERLAY.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('FIRST_EXIT_TREE_OVERLAY', json.dumps(receipt, sort_keys=True))
