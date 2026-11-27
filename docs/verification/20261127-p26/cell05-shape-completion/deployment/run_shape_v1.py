from pathlib import Path
import hashlib,json,subprocess,sys,time
STAGE=Path('/workspace/p26-cell05-shape-completion-20261127-v1')
TOOL=STAGE/'tools/p26/cell05-shape-completion-20261127'
EXPECTED=[{'member': 'tools/p26/cell05-shape-completion-20261127/complete_shape.py', 'bytes': 45345, 'sha256': 'dc75e4c6d56df8673a6551420f74015b0b75d1fec3fe62b544ef63bcc596a133'}, {'member': 'tools/p26/cell05-shape-completion-20261127/PINS.json', 'bytes': 25524, 'sha256': 'be4fc8f2064e9ba988a8eaed42b54831635eca9a297abf57bd08c08446b5be86'}, {'member': 'tools/p26/cell05-shape-completion-20261127/owned-audits/P2OriginalSaving19Geometry05ScalableShape.lean', 'bytes': 2720, 'sha256': 'e5106b4fcb2f8c166a26e9888e23e54b5435deb4dee50f89e27a7877bda43fd1'}, {'member': 'tools/p26/cell05-shape-completion-20261127/RECOVERY_BINDING.json', 'bytes': 967, 'sha256': '7425ce0a4d3c5907e55a74041f6f12456559f9d854a774fa648a16c2cd6f0f34'}, {'member': 'project/ImbalancedChen/P2OriginalSaving19Geometry05ScalableShape.lean', 'bytes': 7508, 'sha256': 'fd381d234ea1c9100d9248542273663df8b3042282326410a9fe8aaf961d90bb'}]
BINDING_SHA='7425ce0a4d3c5907e55a74041f6f12456559f9d854a774fa648a16c2cd6f0f34'
def need(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
for r in EXPECTED:
 p=STAGE/r['member'];need(p.resolve()==p and not p.is_symlink(),'Noncanonical fixed file');v=pin(p);need(v['bytes']==r['bytes'] and v['sha256']==r['sha256'],'Reviewed deployment changed')
p=STAGE/'PREFLIGHT.stdout';need(pin(p)['sha256']=='86db2c46fe3362b4c2d58d645756704be41a23dfd791f46adf3c6602db16212b','Preflight stdout differs')
v=json.loads(p.read_bytes());need(v['status']=='PASS_PREFLIGHT' and v['proof_commands_executed']==0 and v['accepted_existing_steps']==0,'Unexpected preflight')
argv=[sys.executable,'-I','-B',str(TOOL/'complete_shape.py'),'run','--recovery-binding-sha256',BINDING_SHA]
out=STAGE/'COMPLETE.stdout';err=STAGE/'COMPLETE.stderr';result_path=STAGE/'COMPLETE_PROCESS.json'
need(not any(p.exists() or p.is_symlink() for p in (out,err,result_path)),'Prior complete attempt exists; preserve it')
print(json.dumps({'kind':'shape_strict_run_started','argv':argv,'new_modes':['normal','kernel','owned'],'old_Lean_commands':0}),flush=True)
start=time.monotonic()
with out.open('xb') as o,err.open('xb') as e:proc=subprocess.run(argv,stdout=o,stderr=e,check=False,timeout=3500)
record={'schema':'p26_shape_complete_process_v1','argv':argv,'exit_code':proc.returncode,'elapsed_seconds':time.monotonic()-start,'stdout':pin(out),'stderr':pin(err)}
with result_path.open('x') as f:f.write(json.dumps(record,indent=2)+'\n')
print(json.dumps({'kind':'shape_strict_run_finished',**record}),flush=True)
print(out.read_text(errors='replace')[-24000:],flush=True)
if proc.returncode:
 print(err.read_text(errors='replace')[-24000:],flush=True);sys.exit(proc.returncode)
for n in ('verification/SUCCESS.json','COMBINED_INDEX.json','exports/shape-evidence.tar.xz'):
 print(json.dumps({'kind':'shape_evidence_ready','artifact':pin(STAGE/n)}),flush=True)
