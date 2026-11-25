python3 - <<'P25_FINITE_CORE_001'
from pathlib import Path
import json,hashlib,os,subprocess,time,shutil
root=Path('/workspace/p25-q96-20261125')
base=root/'.lake/diagnostic/p25-cell00-canonical-attempt001'
out=root/'.lake/diagnostic/p25-finite-core-attempt001'
assert not out.exists(),'preserve prior attempt'
out.mkdir()
old=json.loads((base/'charparse/RESULT.json').read_text())
assert json.loads((base/'canonical/RESULT.json').read_text())['accepted'] is True
module='ImbalancedChen.P2OriginalSaving16FiniteCore'
src=out/'src';lib=out/'lib';audit=out/'audit'
for p in [src/'ImbalancedChen',lib/'ImbalancedChen',audit]:p.mkdir(parents=True)
source=json.loads("\"import Lean\\nimport ImbalancedChen.P2OriginalSaving16OriginalInput\\nimport ImbalancedChen.P2OriginalSaving16Decoder\\nimport ImbalancedChen.P2OriginalSaving16Q96FloorCore\\nimport ImbalancedChen.P2OriginalSaving19SourceJson\\nimport Mathlib.Data.Fin.VecNotation\\nimport Mathlib.LinearAlgebra.Matrix.Determinant.Basic\\nimport Mathlib.Tactic\\n\\n/-!\\nSOURCE ONLY / NOT COMPILED / ZERO FINITE OR Q96 CREDIT.\\n\\nMechanical extraction of twenty-one existing finite source commands from\\nP2OriginalSaving16FiniteArchive at SHA256\\n9db41aa0553a3c5020acceffa3f1bc91529f1382f7dc6c6d57ba96c073e6d627.\\nThe nineteen definitions, QPoint abbreviation and anonymous Decidable\\ninstance retain their original namespace, complete text and context.\\n\\nThis module exposes the same archive and original simplex computations.\\nThe four closed guards and their parse-success elimination theorem stay\\nin P2OriginalSaving16FiniteArchive. No file reader, parser, decoder,\\nalgorithm, numerical result or theorem is added here. OriginalInput and\\nits fourteen-input binding remain required when this module is compiled.\\n-/\\nnamespace ImbalancedChen.P2OriginalSaving16OriginalArchive\\n\\nopen Lean Elab Term\\nopen P2OriginalSaving19Archive (SourceJson)\\nopen P2OriginalSaving16JensenFloor (q96Floor)\\nopen scoped BigOperators\\n\\n\\nnoncomputable section\\n\\n\\ndef originalId : Fin 14 → Nat := ![0,1,2,3,4,5,6,8,9,10,11,12,13,14]\\n\\ndef parsedCell (i : Fin 14) : Except String CellRecord := do\\n  decodeCell (← SourceJson.parse (originalText i))\\n\\n/-- The default is not evidence. The next closed statement rules it out\\nfor every actual source text, including absent fields and parse errors. -/\\ndef archive (i : Fin 14) : CellRecord := (parsedCell i).toOption.getD default\\n\\n/-- Inspect only the Except constructor. Deciding this Bool does not\\nrequire decidable equality of CellRecord or the retained raw SourceJson\\ntrees. It still executes the full pure parser and decoder at reduction. -/\\ndef parsedCellSuccess (i : Fin 14) : Bool :=\\n  match parsedCell i with\\n  | .ok _ => true\\n  | .error _ => false\\n\\nabbrev QPoint := Fin 8 → ℚ\\n\\ndef point (c : CellRecord) (v : Nat) : QPoint := fun j => (c.vertices.getD v #[]).getD j.val 0\\n\\ndef simplexVertices (c : CellRecord) (r : SimplexRecord) : Fin 9 → QPoint :=\\n  fun i => point c (r.vertexIds.getD i.val 0)\\n\\ndef comparisonQ (t : QPoint) : ℚ := 57 / 64 - (3 / 2) * (t 1 + t 2)\\n\\ndef capQ (t : QPoint) : ℚ := (1 + (t 0 + t 7)) / 2 - 1 / 1000000\\n\\ndef gapQ (t : QPoint) : ℚ := capQ t - comparisonQ t\\n\\ndef factorsQ (t : QPoint) : Fin 10 → ℚ :=\\n  ![comparisonQ t - ∑ i, t i, capQ t - ∑ i, t i,\\n    t 0, t 1, t 2, t 3, t 4, t 5, t 6, t 7]\\n\\ndef gapTotalQ (v : Fin 9 → QPoint) : ℚ := ∑ i : Fin 9, gapQ (v i)\\n\\ndef meansQ (v : Fin 9 → QPoint) (j : Fin 10) : ℚ :=\\n  ((∑ i : Fin 9, factorsQ (v i) j) +\\n    (∑ i : Fin 9, gapQ (v i) * factorsQ (v i) j) / gapTotalQ v) / 10\\n\\ndef edgeMatrix (v : Fin 9 → QPoint) : Matrix (Fin 8) (Fin 8) ℚ :=\\n  fun i j => v i.succ j - v 0 j\\n\\ndef physicalVolumeQ (v : Fin 9 → QPoint) : ℚ := |(edgeMatrix v).det| / ((8 : ℕ).factorial : ℚ)\\n\\ndef jensenQ (v : Fin 9 → QPoint) : ℚ :=\\n  4 * physicalVolumeQ v * (gapTotalQ v / 9) / ∏ j : Fin 10, meansQ v j\\n\\ndef simplexValid (c : CellRecord) (s : Fin c.simplices.size) : Prop :=\\n  let r := c.simplices[s]\\n  let v := simplexVertices c r\\n  r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧\\n  (∀ k : Fin 9, r.vertexIds.getD k.val 0 < c.vertices.size) ∧\\n  0 < physicalVolumeQ v ∧ 0 < gapTotalQ v ∧\\n  r.physicalVolume = physicalVolumeQ v ∧ r.meanGap = gapTotalQ v / 9 ∧\\n  r.gapWeightedMeans.size = 10 ∧\\n  (∀ j : Fin 10, r.gapWeightedMeans.getD j.val 0 = meansQ v j) ∧\\n  r.jensenBound = jensenQ v ∧ r.jensenFloor = q96Floor (jensenQ v)\\n\\ninstance (c : CellRecord) (s : Fin c.simplices.size) : Decidable (simplexValid c s) :=\\n  inferInstanceAs (Decidable (let r := c.simplices[s]; let v := simplexVertices c r;\\n    r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧\\n    (∀ k : Fin 9, r.vertexIds.getD k.val 0 < c.vertices.size) ∧\\n    0 < physicalVolumeQ v ∧ 0 < gapTotalQ v ∧\\n    r.physicalVolume = physicalVolumeQ v ∧ r.meanGap = gapTotalQ v / 9 ∧\\n    r.gapWeightedMeans.size = 10 ∧\\n    (∀ j : Fin 10, r.gapWeightedMeans.getD j.val 0 = meansQ v j) ∧\\n    r.jensenBound = jensenQ v ∧ r.jensenFloor = q96Floor (jensenQ v)))\\n\\ndef cellFloorNumerator (i : Fin 14) : ℤ :=\\n  ∑ s : Fin (archive i).simplices.size,\\n    q96Floor (jensenQ (simplexVertices (archive i) (archive i).simplices[s]))\\n\\ndef aggregateNumerator : ℤ := ∑ i : Fin 14, cellFloorNumerator i\\n\\ndef historicalNumerator : ℤ := 1222997719565324892497827\\n\\nend\\nend ImbalancedChen.P2OriginalSaving16OriginalArchive\\n\"")
f=src/'ImbalancedChen/P2OriginalSaving16FiniteCore.lean';f.write_text(source)
h=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
deps={m:r for m,r in old['dependency_objects'].items() if m not in ['ImbalancedChen.P2Saving16CanonicalCell00Binding','ImbalancedChen.P2Saving16StringCharBinding00','ImbalancedChen.P2OriginalSaving19CharInputBridge','ImbalancedChen.P2OriginalSaving19SourceJsonCharInput']}
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
 start=time.monotonic();print('P25_FINITE_CORE_START',label,flush=True)
 log=out/(label.upper()+'.log')
 with log.open('w') as stream:
  try:r=subprocess.run(cmd,cwd=root,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=600);code=r.returncode;timed=False
  except subprocess.TimeoutExpired:code=124;timed=True
 state[label]={'command':cmd,'exit_code':code,'seconds':round(time.monotonic()-start,3),'timed_out':timed,'log_sha256':h(log)}
 write();print('P25_FINITE_CORE_RESULT',label,json.dumps(state[label]),log.read_text()[-2500:],flush=True)
 if code:state['status']=label.upper()+'_FAILED';write();raise SystemExit(code)
rows=[json.loads(line.split('P0_QUEUE_DECL ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_DECL ')]
inv=[json.loads(line.split('P0_QUEUE_INVENTORY ',1)[1]) for line in (out/'AUDIT.log').read_text().splitlines() if line.startswith('P0_QUEUE_INVENTORY ')]
assert len(inv)==1 and sorted(inv[0]['environment'])==sorted(inv[0]['serialized'])==sorted(r['name'] for r in rows)
assert all(not any(r.get(k) for k in ['axiom','unsafe','partial']) and set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} for r in rows)
assert any(r['name']=='ImbalancedChen.P2OriginalSaving16OriginalArchive.parsedCellSuccess' for r in rows)
for m,r in deps.items():assert h(lib/(m.replace('.','/')+'.olean'))==r['sha256'] and h(Path(r['path']))==r['sha256']
state.update(status='NORMAL_REPLAY_COMPLETE_OWNED_ACCEPTED',accepted=True,owned_declarations=rows,owned_count=len(rows),object_sha256=h(lib/(module.replace('.','/')+'.olean')))
write();print('P25_FINITE_CORE_ACCEPTED',len(rows),flush=True)
P25_FINITE_CORE_001
