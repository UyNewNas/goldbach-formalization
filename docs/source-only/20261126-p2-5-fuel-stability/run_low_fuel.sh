python3 - <<'P25_LOW_FUEL_001'
from pathlib import Path
import json,hashlib,os,subprocess,time,shutil
root=Path('/workspace/p25-q96-20261125')
base=root/'.lake/diagnostic/p25-cell00-canonical-attempt001'
out=root/'.lake/diagnostic/p25-low-fuel-attempt001'
assert not out.exists(),'preserve prior attempt'
out.mkdir()
old=json.loads((base/'charparse/RESULT.json').read_text())
assert json.loads((base/'canonical/RESULT.json').read_text())['accepted'] is True
module='ImbalancedChen.P2Saving16Cell00LowFuel'
src=out/'src';lib=out/'lib';audit=out/'audit'
for p in [src/'ImbalancedChen',lib/'ImbalancedChen',audit]:p.mkdir(parents=True)
source=json.loads("\"import ImbalancedChen.P2Saving16StringCharBinding00\\nimport ImbalancedChen.P2OriginalSaving16Decoder\\nimport ImbalancedChen.P2OriginalSaving19SourceJsonCharInput\\n\\n/-!\\nOriginal cell00 reader and typed decoder at a candidate sufficient fuel.\\nThis is a closed kernel check, not a host-parsed certificate. The eventual\\nconsumer must transport this same successful result to original length+1 fuel\\nand the already accepted canonical originalText 0 binding.\\n-/\\nnamespace ImbalancedChen.P2Saving16Cell00LowFuel\\n\\nopen P2OriginalSaving19Archive (SourceJson)\\nopen P2OriginalSaving16OriginalArchive (decodeCell)\\nopen P2Saving16StringCharBinding00 (chars00)\\n\\nnoncomputable def parsedAtFuel (fuel : Nat) := do\\n  let (v, tail) ← SourceJson.value fuel chars00\\n  if (SourceJson.white tail).isEmpty then decodeCell v\\n  else throw \\\"unconsumed original JSON input\\\"\\n\\ntheorem cell00_low_fuel_success :\\n    (match parsedAtFuel 371 with\\n     | .ok _ => true\\n     | .error _ => false) = true := by\\n  decide +kernel\\n\\n#print axioms cell00_low_fuel_success\\n\\nend ImbalancedChen.P2Saving16Cell00LowFuel\\n\"")
f=src/'ImbalancedChen/P2Saving16Cell00LowFuel.lean';f.write_text(source)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
deps={m:r for m,r in old['dependency_objects'].items() if m not in ['ImbalancedChen.P2OriginalSaving16OriginalInput','ImbalancedChen.P2Saving16CanonicalCell00Binding']}
for m,r in deps.items():
 p=Path(r['path']);assert h(p)==r['sha256'];q=lib/(m.replace('.','/')+'.olean');shutil.copyfile(p,q);assert h(q)==r['sha256']
a=(base/'charparse/audit/Audit.lean').read_text().replace('ImbalancedChen.P2Saving16CanonicalCell00ParseDiagnostic',module)
(audit/'Audit.lean').write_text(a)
lean='/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean';checker=lean.replace('/lean','/leanchecker') if False else str(Path(lean).with_name('leanchecker'))
env=dict(os.environ);env.pop('LEAN_SRC_PATH',None);env['LEAN_SYSROOT']=str(Path(lean).parent.parent);env['LEAN_PATH']=':'.join([str(lib),*old['approved_LEAN_PATH'].split(':')[1:]])
flags=['-t0','-j1','-M11264','-DwarningAsError=true','-DmaxRecDepth=1000000','-DmaxHeartbeats=80000000']
state={'status':'STARTED','accepted':False,'module':module,'source_sha256':h(f),'source':source,'dependencies':deps,'lean_sha256':h(Path(lean)),'checker_sha256':h(Path(checker)),'approved_LEAN_PATH':env['LEAN_PATH'],'original_cell00_sha256':h(Path('/workspace/goldbach-research/eighth-prefix-family-20261009-cell-00.witness.json')),'Q96_proved':False,'P2_5_proved':False}
write=lambda:(out/'RESULT.json').write_text(json.dumps(state,indent=2)+'\n')
write()
commands=[('normal',[lean,*flags,'--root='+str(src),'-o',str(lib/(module.replace('.','/')+'.olean')),str(f)]),('replay',[checker,'--verbose',module]),('audit',[lean,*flags,'--root='+str(audit),str(audit/'Audit.lean')])]
for label,cmd in commands:
 start=time.monotonic();print('P25_LOW_FUEL_START',label,flush=True)
 log=out/(label.upper()+'.log')
 with log.open('w') as stream:
  try:r=subprocess.run(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=600);code=r.returncode;timed=False
  except subprocess.TimeoutExpired:code=124;timed=True
 state[label]={'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'timed_out':timed,'log_sha256':h(log)}
 write();print('P25_LOW_FUEL_RESULT',label,json.dumps(state[label]),log.read_text()[-2500:],flush=True)
 if code:state['status']=label.upper()+'_FAILED';write();raise SystemExit(code)
rows=[json.loads(line.split('P0_QUEUE_DECL ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_DECL ')]
inv=[json.loads(line.split('P0_QUEUE_INVENTORY ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_INVENTORY ')]
assert len(inv)==1 and sorted(inv[0]['environment'])==sorted(inv[0]['serialized'])==sorted(r['name'] for r in rows)
assert all(not any(r.get(k) for k in ['axiom','unsafe','partial']) and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)
assert any(r['name']==module+'.cell00_low_fuel_success' for r in rows)
for m,r in deps.items():assert h(lib/(m.replace('.','/')+'.olean'))==r['sha256'] and h(Path(r['path']))==r['sha256']
state.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',accepted=True,owned_declarations=rows,owned_count=len(rows),object_sha256=h(lib/(module.replace('.','/')+'.olean')))
write();print('P25_LOW_FUEL_ACCEPTED',len(rows),flush=True)
P25_LOW_FUEL_001
