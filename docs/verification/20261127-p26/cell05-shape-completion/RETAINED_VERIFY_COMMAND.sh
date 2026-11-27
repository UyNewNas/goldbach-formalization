python3 - <<'P26_RETAINED_SHAPE_EXPORT'
from pathlib import Path
import hashlib,json,subprocess,sys
stage=Path('/workspace/p26-cell05-shape-completion-20261127-v1')
driver=stage/'tools/p26/cell05-shape-completion-20261127/complete_shape.py'
b=driver.read_bytes();assert len(b)==45345 and hashlib.sha256(b).hexdigest()=='dc75e4c6d56df8673a6551420f74015b0b75d1fec3fe62b544ef63bcc596a133'
argv=[sys.executable,'-I','-B',str(driver),'verify','--recovery-binding-sha256','7425ce0a4d3c5907e55a74041f6f12456559f9d854a774fa648a16c2cd6f0f34']
r=subprocess.run(argv,capture_output=True,check=False,timeout=3300)
if r.returncode:
 sys.stdout.buffer.write(r.stdout);sys.stdout.buffer.write(r.stderr);sys.stdout.flush();sys.exit(r.returncode)
v=json.loads(r.stdout);assert v['status']=='RETAINED_EVIDENCE_VERIFIED'
p=stage/'exports/shape-evidence.tar.xz';b=p.read_bytes();assert len(b)==1057200 and hashlib.sha256(b).hexdigest()=='3a7f08f9f47c68a25bbc300ea2124cbfecd5332a74e425e3dba494d0540630d4'
header={'schema':'p26_retained_shape_binary_readback_v1','argv':argv,'exit_code':r.returncode,'verify':v,'verify_stdout_sha256':hashlib.sha256(r.stdout).hexdigest(),'verify_stderr_bytes':len(r.stderr),'verify_stderr_sha256':hashlib.sha256(r.stderr).hexdigest(),'archive':{'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()},'Lean_commands':0}
print(json.dumps(header,separators=(',',':')),flush=True)
sys.stdout.buffer.write(b);sys.stdout.buffer.flush()
P26_RETAINED_SHAPE_EXPORT
