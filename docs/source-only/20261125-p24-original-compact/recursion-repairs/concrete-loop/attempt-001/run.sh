set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_CONCRETE_LOOP_REC_01'
import hashlib, json, os, pathlib, signal, subprocess, sys, time
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-concrete-loop-rec-20261126/attempt-001")
payload=json.loads(r'''{"candidate":"import ImbalancedChen.P2OriginalCompactConcreteRun\n\n/-!\nSOURCEONLY / UNCOMPILED. The original stop test uses a source-computed\nfixedUpper supplied by the concrete Q80 module. This file defines the actual\nbounded computation, not an existence assertion for K.Run or an event file.\nThe two-million-step term is NEVER evaluated during source authoring.\n-/\nnamespace ImbalancedChen.P2OriginalCompactConcreteLoopSourceOnly\n\nopen MeasureTheory\nopen P4AOriginalInitialSeedInventorySourceOnly\nopen P2OriginalPrioritySerialQueueSourceOnly\nopen P2OriginalPriorityForestLedgerSourceOnly\nopen P2OriginalEfficientPriorityHeapSourceOnly\nopen P2OriginalCompactConcreteRunSourceOnly\n\n/-- Original full-run arguments, distinct from the manuscript\u0027s selected K. -/\ndef maxSplits : ℕ := 2000000\ndef target : ℚ := 6809 / 1000\nabbrev fixedUpper := P2OriginalCompactQ80EncloserSourceOnly.fixedUpper\n\ndef keepRunning (st : DriverState) : Prop :=\n  st.splits < maxSplits ∧ target ≤ fixedUpper + (st.totalUpper : ℚ) / 2^80\n\ninstance (st : DriverState) : Decidable (keepRunning st) := inferInstanceAs\n  (Decidable (st.splits < maxSplits ∧ target ≤ fixedUpper + (st.totalUpper : ℚ) / 2^80))\n\ninductive StopReason where\n  | budget\n  | belowTarget\n  deriving DecidableEq, Repr\n\ninductive Result where\n  | stopped (reason : StopReason) (state : DriverState)\n  | failed (reason : DriverFailure) (state : DriverState)\n\ndef Result.state : Result → DriverState\n  | .stopped _ st => st\n  | .failed _ st => st\n\n/-- The strict crossing is tested only after negating the original >= gate.\nAt the budget boundary the source\u0027s first while-condition already stops. -/\ndef stopResult (st : DriverState) : Result :=\n  .stopped (if st.splits < maxSplits then .belowTarget else .budget) st\n\n/-- Every successful iteration performs exactly one original split. Fuel is\nan implementation termination bound, not a changed early-stop criterion. -/\ndef runFuel : ℕ → DriverState → Result :=\n  Nat.rec (motive := fun _ => DriverState → Result)\n    (fun st =>\n      if keepRunning st then .failed .exhaustedFuel st else stopResult st)\n    (fun _ previous st =>\n      if keepRunning st then\n        match driverStep st with\n        | .error reason => .failed reason st\n        | .ok next => previous next\n      else stopResult st)\n\n/-- Concrete original computation. No run witness or per-leaf data argument. -/\ndef originalRun : Result := runFuel maxSplits initialDriverState\n\ntheorem runFuel_ledger (fuel : ℕ) (st : DriverState) (hi : LedgerInvariant st) :\n    LedgerInvariant (runFuel fuel st).state := by\n  induction fuel generalizing st with\n  | zero =>\n      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi\n  | succ fuel ih =>\n      by_cases hg : keepRunning st\n      · cases hs : driverStep st with\n        | error reason => simpa [runFuel,hg,hs,Result.state] using hi\n        | ok next =>\n            simpa [runFuel,hg,hs] using ih next (driverStep_ledger st next hs hi)\n      · simpa [runFuel,hg,stopResult,Result.state] using hi\n\ntheorem runFuel_heap (fuel : ℕ) (st : DriverState) (hi : AddressHeapInvariant st) :\n    AddressHeapInvariant (runFuel fuel st).state := by\n  induction fuel generalizing st with\n  | zero =>\n      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi\n  | succ fuel ih =>\n      by_cases hg : keepRunning st\n      · cases hs : driverStep st with\n        | error reason => simpa [runFuel,hg,hs,Result.state] using hi\n        | ok next =>\n            simpa [runFuel,hg,hs] using ih next (driverStep_heap st next hs hi)\n      · simpa [runFuel,hg,stopResult,Result.state] using hi\n\ntheorem runFuel_serial (fuel : ℕ) (st : DriverState)\n    (hi : SerialDiscipline (contents st.queue) st.serial) :\n    SerialDiscipline (contents (runFuel fuel st).state.queue) (runFuel fuel st).state.serial := by\n  induction fuel generalizing st with\n  | zero =>\n      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi\n  | succ fuel ih =>\n      by_cases hg : keepRunning st\n      · cases hs : driverStep st with\n        | error reason => simpa [runFuel,hg,hs,Result.state] using hi\n        | ok next =>\n            simpa [runFuel,hg,hs] using ih next (driverStep_serial st next hs hi)\n      · simpa [runFuel,hg,stopResult,Result.state] using hi\n\ntheorem originalRun_serial : SerialDiscipline (contents originalRun.state.queue) originalRun.state.serial :=\n  runFuel_serial _ _ initial_serial\ntheorem runFuel_leaf_count (fuel : ℕ) (st : DriverState)\n    (hi : (entries st.forest).length = 21 + st.splits) :\n    (entries (runFuel fuel st).state.forest).length = 21 + (runFuel fuel st).state.splits := by\n  induction fuel generalizing st with\n  | zero =>\n      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi\n  | succ fuel ih =>\n      by_cases hg : keepRunning st\n      · cases hs : driverStep st with\n        | error reason => simpa [runFuel,hg,hs,Result.state] using hi\n        | ok next =>\n            obtain ⟨p,href,hcount,_⟩ := driverStep_source st next hs\n            have hn := driverStep_leaf_count st next hs\n            have hi\u0027 : (entries next.forest).length = 21 + next.splits := by omega\n            simpa [runFuel,hg,hs] using ih next hi\u0027\n      · simpa [runFuel,hg,stopResult,Result.state] using hi\n\ntheorem originalRun_ledger : LedgerInvariant originalRun.state :=\n  runFuel_ledger _ _ initial_ledger\n\ntheorem originalRun_heap : AddressHeapInvariant originalRun.state :=\n  runFuel_heap _ _ initial_heap\n\ntheorem originalRun_leaf_count :\n    (entries originalRun.state.forest).length = 21 + originalRun.state.splits := by\n  apply runFuel_leaf_count\n  change (entries (seedForest originalEnclose initialSeeds 0).1).length = 21 + 0\n  rw [seedForest_entries_length,initialSeeds_eq_records,records_length]\n\n/-- Exact ordered charges include EVERY leaf. No positive-error filter. -/\ndef orderedUpperCharges : List ℤ :=\n  (entries originalRun.state.forest).map fun p => p.bounds.upper\n\ndef orderedLowerCharges : List ℤ :=\n  (entries originalRun.state.forest).map fun p => p.bounds.lower\n\ntheorem orderedUpperCharges_sum : orderedUpperCharges.sum = originalRun.state.totalUpper :=\n  originalRun_ledger.2.symm\n\ntheorem orderedLowerCharges_sum : orderedLowerCharges.sum = originalRun.state.totalLower :=\n  originalRun_ledger.1.symm\n\ntheorem orderedCharges_length :\n    orderedUpperCharges.length = 21 + originalRun.state.splits ∧\n      orderedLowerCharges.length = 21 + originalRun.state.splits := by\n  simp only [orderedUpperCharges,orderedLowerCharges,List.length_map,originalRun_leaf_count,and_self]\n\n/-- The original source integral, not a later independent partition or kernel. -/\ntheorem originalRun_source_integral :\n    OriginalThirdCompactPartitionSourceOnly.originalCompactThirdCorrection =\n      ((entries originalRun.state.forest).map (fun p =>\n        ∫ t in rootCell p.cell, OriginalThirdCompactPartitionSourceOnly.compactKernel t)).sum :=\n  complete_integral_identity originalRun.state.forest\n\ndef historicalUpper : ℤ := 144590669409566793572719\n\n/-- The original endpoint predicate, shared before inserting a closed run. -/\ndef historicalEndpointCheckFor (result : Result) : Bool :=\n  match result with\n  | .stopped .budget st =>\n      decide (st.splits = maxSplits ∧ st.totalUpper = historicalUpper ∧\n        Batteries.PairingHeap.size st.queue = 1852040 ∧ st.assertionsPassed = true)\n  | _ => false\n\n/-- The entire decisive finite claim. `true` requires the actual original\nstop/budget computation to finish without failure at 2M, with the historical\nupper sum and heap occupancy. No cached result is imported from JSON. -/\nabbrev historicalEndpointCheck : Bool :=\n  historicalEndpointCheckFor originalRun\n\nprivate theorem historical_check_fields_result (result : Result)\n    (hc : historicalEndpointCheckFor result = true) :\n    result.state.splits = maxSplits ∧\n    result.state.totalUpper = historicalUpper ∧\n    Batteries.PairingHeap.size result.state.queue = 1852040 ∧\n    result.state.assertionsPassed = true := by\n  unfold historicalEndpointCheckFor at hc\n  cases result with\n  | failed reason st => simp at hc\n  | stopped reason st =>\n      cases reason with\n      | belowTarget => simp at hc\n      | budget => exact of_decide_eq_true hc\n\n/-- Logical extraction only; the separate candidate file supplies the closed\nfinite proof term, left UNEVALUATED for user-owned compilation. -/\ntheorem historical_check_fields (hc : historicalEndpointCheck = true) :\n    originalRun.state.splits = maxSplits ∧\n    originalRun.state.totalUpper = historicalUpper ∧\n    Batteries.PairingHeap.size originalRun.state.queue = 1852040 ∧\n    originalRun.state.assertionsPassed = true := by\n  exact historical_check_fields_result originalRun hc\n\ntheorem historical_ordered_charge_fields (hc : historicalEndpointCheck = true) :\n    orderedUpperCharges.sum = historicalUpper ∧\n    orderedUpperCharges.length = 2000021 := by\n  have hf := historical_check_fields hc\n  refine ⟨orderedUpperCharges_sum.trans hf.2.1,?_⟩\n  rw [orderedCharges_length.1,hf.1]\n  rfl\n\n\nopen P4AOriginalClosedTreeStructuralAggregationSourceOnly in\nprivate theorem forest_upper_charges_length (forest : OriginalForest initialSeeds) :\n    ((entries forest).map (fun p => p.bounds.upper)).length =\n      splitCount (completeTree forest) + 1 := by\n  have hlen := closedLeaves_length (completeTree forest)\n    OriginalThirdCompactPartitionSourceOnly.compactRegion\n  rw [completeTree_closedLeaves,List.length_map] at hlen\n  simpa only [List.length_map] using hlen\n\n/-- Shape-preserving attachment at the concrete complete original forest.\nThis includes zero-error leaves that never enter the active heap. -/\nnoncomputable abbrev originalChargeTree : P4AOriginalClosedTreeStructuralAggregationSourceOnly.ChargedCutTree :=\n  (P4AClosedCutTreePositionalChargeBindingSourceOnly.attachCharges\n    (completeTree originalRun.state.forest) orderedUpperCharges\n      (forest_upper_charges_length originalRun.state.forest)).val\n\nopen P4AOriginalClosedTreeStructuralAggregationSourceOnly\n  P4AClosedCutTreePositionalChargeBindingSourceOnly in\nprivate noncomputable abbrev attachedChargeValue\n    (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree) (charges : List ℤ)\n    (hsize : charges.length = splitCount tree + 1) : ChargedCutTree :=\n  (attachCharges tree charges hsize).val\n\nopen P4AOriginalClosedTreeStructuralAggregationSourceOnly\n  P4AClosedCutTreePositionalChargeBindingSourceOnly in\n/-- Establish both projections before inserting the closed run or charge list. -/\nprivate theorem attached_charge_fields :\n    (fun (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree) (charges : List ℤ)\n      (hsize : charges.length = splitCount tree + 1) =>\n      (totalCharge (attachedChargeValue tree charges hsize),\n        eraseCharges (attachedChargeValue tree charges hsize))) =\n    (fun (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree) (charges : List ℤ)\n      (_ : charges.length = splitCount tree + 1) =>\n      (charges.sum,tree)) := by\n  funext tree charges hsize\n  apply Prod.ext\n  · exact (totalCharge_eq_leafCharges_sum\n      (attachCharges tree charges hsize).val).trans\n        (congrArg (fun qs : List ℤ => qs.sum)\n          (attachCharges_list tree charges hsize))\n  · exact attachCharges_erase tree charges hsize\n\ntheorem originalChargeTree_total :\n    P4AOriginalClosedTreeStructuralAggregationSourceOnly.totalCharge originalChargeTree =\n      originalRun.state.totalUpper := by\n  have h := congrFun (congrFun (congrFun attached_charge_fields\n    (completeTree originalRun.state.forest)) orderedUpperCharges)\n      (forest_upper_charges_length originalRun.state.forest)\n  exact (congrArg Prod.fst h).trans orderedUpperCharges_sum\n\ntheorem originalChargeTree_erase :\n    P4AOriginalClosedTreeStructuralAggregationSourceOnly.eraseCharges originalChargeTree =\n      completeTree originalRun.state.forest := by\n  have h := congrFun (congrFun (congrFun attached_charge_fields\n    (completeTree originalRun.state.forest)) orderedUpperCharges)\n      (forest_upper_charges_length originalRun.state.forest)\n  exact congrArg Prod.snd h\n\n/-- The complete computation proves active-serial uniqueness, including\nmultiplicity. Python\u0027s later cell/lo/hi tuple fields can never break a tie. -/\ntheorem runFuel_serial_nodup (fuel : ℕ) (st : DriverState)\n    (hb : SerialDiscipline (contents st.queue) st.serial)\n    (hi : SerialNodup (contents st.queue)) :\n    SerialNodup (contents (runFuel fuel st).state.queue) := by\n  induction fuel generalizing st with\n  | zero =>\n      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi\n  | succ fuel ih =>\n      by_cases hg : keepRunning st\n      · cases hs : driverStep st with\n        | error reason => simpa [runFuel,hg,hs,Result.state] using hi\n        | ok next =>\n            simpa [runFuel,hg,hs] using ih next\n              (driverStep_serial st next hs hb) (driverStep_serial_nodup st next hs hb hi)\n      · simpa [runFuel,hg,stopResult,Result.state] using hi\n\ntheorem originalRun_serial_nodup : SerialNodup (contents originalRun.state.queue) :=\n  runFuel_serial_nodup _ _ initial_serial initial_serial_nodup\nend ImbalancedChen.P2OriginalCompactConcreteLoopSourceOnly\r\n\r\n\r\n\r\n","oldBlock":"def runFuel : ℕ → DriverState → Result\n  | 0, st =>\n      if keepRunning st then .failed .exhaustedFuel st else stopResult st\n  | fuel + 1, st =>\n      if keepRunning st then\n        match driverStep st with\n        | .error reason => .failed reason st\n        | .ok next => runFuel fuel next\n      else stopResult st\n\n","newBlock":"def runFuel : ℕ → DriverState → Result :=\n  Nat.rec (motive := fun _ => DriverState → Result)\n    (fun st =>\n      if keepRunning st then .failed .exhaustedFuel st else stopResult st)\n    (fun _ previous st =>\n      if keepRunning st then\n        match driverStep st with\n        | .error reason => .failed reason st\n        | .ok next => previous next\n      else stopResult st)\n\n","proofPatches":[],"original_sha256":"a5465ae8b2455cce75965e7e2ff0de17df8d20f1fa12db8a299ee2b447eefd53","original_git_blob":"201f52aac15d15c4b9819a8a51ac206c50748c9b","candidate_sha256":"04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0"}''')
target="ImbalancedChen.P2OriginalCompactConcreteLoop"
pin="6e616f4e0372555f7a78bcdba3e198d0e277eec8"
snapshot_path=pathlib.Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json")
snapshot_expected="ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
native_context_expected="71451bbb4a755fb5ec8744663121d0630ba5afd3d5774f7d0ec7931d9d387e90"
expected={
 "verification/part2/run_winner9_private_checks.py":"164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
 "verification/part2/run_winner9_private_audit.py":"571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
 "verification/part2/winner9_private_audit_template.lean":"2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
 "verification/part2/winner9_external_snapshot.py":"a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
 "verification/part2/inspect_winner9_owner_native.py":"9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
}
def digest(path):
 with pathlib.Path(path).open("rb") as f: return hashlib.file_digest(f,"sha256").hexdigest()
def jd(value):
 return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(",",":")).encode()).hexdigest()
def info(path):
 return {"path":str(path),"bytes":pathlib.Path(path).stat().st_size,"sha256":digest(path)}
def write(name,value):
 (out/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+"\n")
def check_source():
 assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=root,text=True).strip()==pin
 assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],cwd=root,text=True).strip()
 assert {n:digest(root/n) for n in expected}==expected

check_source()
sys.path.insert(0,str(root/"verification/part2"))
from run_winner9_private_audit import LEAN, LEANCHECKER, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes
assert PIN=="e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"
runtime_expected={LEAN:"e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",LEANCHECKER:"ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a"}
assert {n:digest(n) for n in runtime_expected}==runtime_expected
assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=MATHLIB,text=True).strip()==PIN
assert digest(snapshot_path)==snapshot_expected
nodes=project_nodes(root,target)
lib=root/".lake/p2-private/lib"
registry=root/".lake/p2-private/records.json"
external=ExternalSnapshot(snapshot_path,lean=LEAN,mathlib_pin=PIN,project_lib=lib)
native_before=external.binding()
assert native_before["snapshot_sha256"]==snapshot_expected
assert native_before["context_signature"]==native_context_expected
assert native_before["verification_helper_sha256"]==expected["verification/part2/winner9_external_snapshot.py"]
mark_project_nodes(nodes,set(external.modules))
toolchain={"lean_version":subprocess.check_output([LEAN,"--version"],text=True).strip(),"lean_binary_sha256":runtime_expected[LEAN],"mathlib_commit":PIN}
records=json.loads(registry.read_text())
registry_before=digest(registry)
before=snapshot(root,lib,nodes,toolchain,external)
verify_compilation(records,nodes,before)
source=pathlib.Path(nodes[target]["source"]).read_bytes()
assert hashlib.sha1(b"blob "+str(len(source)).encode()+b"\0"+source).hexdigest()=="201f52aac15d15c4b9819a8a51ac206c50748c9b"
import base64,gzip
assert len(source)>0 and hashlib.sha256(source).hexdigest()=="a5465ae8b2455cce75965e7e2ff0de17df8d20f1fa12db8a299ee2b447eefd53"
candidate=payload["candidate"].encode("utf-8")
old_block=payload["oldBlock"].encode("utf-8")
new_block=payload["newBlock"].encode("utf-8")
assert source.count(old_block)==1
expected_candidate=source.replace(old_block,new_block,1)
for patch in payload["proofPatches"]:
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert expected_candidate.count(old)==1
 expected_candidate=expected_candidate.replace(old,new,1)
assert candidate==expected_candidate
restored=candidate
for patch in reversed(payload["proofPatches"]):
 restored=restored.replace(patch["new"].encode("utf-8"),patch["old"].encode("utf-8"),1)
assert restored.replace(new_block,old_block,1)==source
assert hashlib.sha256(candidate).hexdigest()=="04d6475a718cb7fd237ca52e7ee0d6555f23783cd39e6f9d92ac63ceca24c2d0"
out.mkdir(parents=True,exist_ok=False)
candidate_module="ConcreteLoopCandidate"
relative=pathlib.Path(candidate_module+".lean")
candidate_path=out/relative
candidate_path.parent.mkdir(parents=True,exist_ok=True)
candidate_path.write_bytes(candidate)
(out/"ConcreteLoop-original.lean").write_bytes(source)
candidate_lib=out/"lib"
candidate_object=candidate_lib/relative.with_suffix(".olean")
candidate_object.parent.mkdir(parents=True)
template=(root/"verification/part2/winner9_private_audit_template.lean").read_bytes()
original_target=b"ImbalancedChen.P2Winner9FiniteMomentKernel"
assert template.count(original_target)==2
audit=template.replace(original_target,candidate_module.encode())
assert audit.replace(candidate_module.encode(),original_target)==template
(out/"OriginalAuditTemplate.lean").write_bytes(template)
(out/"Audit.lean").write_bytes(audit)
write("before-snapshot.json",before)
original_env=external.environment(os.environ)
env=dict(original_env)
env["LEAN_PATH"]=str(candidate_lib)+os.pathsep+original_env["LEAN_PATH"]
flags=["-t0","-j1","-M11264","-DwarningAsError=true","-DmaxRecDepth=50000","-DmaxHeartbeats=40000000"]
receipt={
 "purpose":"isolated ConcreteLoop runFuel Nat.rec candidate compile replay original full-owned audit",
 "source_pin":pin,"module":target,"candidate_module":candidate_module,"canonical_closure_size":len(nodes),
 "original_source":info(out/"ConcreteLoop-original.lean"),"candidate_source":info(candidate_path),
 "source_changes":"runFuel named recursion to direct Nat.rec; identical zero keepRunning/driverStep/error/ok/stop behavior",
 "inverse_source_bytes_equal":True,"all_other_definitions_and_all_theorem_statements_unchanged":True,
 "proof_only_adaptations":{},
 "all_original_theorem_complete_blocks_unchanged":True,
 "template":info(out/"OriginalAuditTemplate.lean"),"audit_source":info(out/"Audit.lean"),
 "template_target_replacements":2,"template_other_bytes_equal":True,
 "canonical_source_and_object":before["project"][target],
 "registry_sha256_before":registry_before,"native_before":native_before,
 "runtime_sha256":runtime_expected,"verifier_sha256":expected,
 "before_snapshot_sha256":jd(before),"lean_path":env["LEAN_PATH"],"lean_sysroot":env["LEAN_SYSROOT"],
 "environment_only_delta":"isolated candidate lib prepended; original ExternalSnapshot environment retained after it",
 "production_changed":False,"registry_writeback":False,"native_qualification_run":False,
 "canonical_credit":False,"full_P2_credit":False,"stages":[],
}
write("receipt.json",receipt)
print("P24_RECURSOR_CANDIDATE_BEGIN "+json.dumps({k:receipt[k] for k in ["source_pin","module","candidate_module","canonical_closure_size","candidate_source","original_source","template","audit_source","registry_sha256_before"]},ensure_ascii=False),flush=True)
deadline=time.monotonic()+760
def run_stage(name,command):
 log_path=out/(name+".log")
 started=time.monotonic()
 left=deadline-started
 if left<=0:raise RuntimeError("Isolated diagnostic soft deadline exceeded")
 timed_out=False
 with log_path.open("wb") as log:
  proc=subprocess.Popen(command,cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  try:rc=proc.wait(timeout=left)
  except subprocess.TimeoutExpired:
   timed_out=True
   os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=124
 stage={"stage":name,"command":command,"exit_code":rc,"timed_out":timed_out,"seconds":time.monotonic()-started,"log":info(log_path)}
 receipt["stages"].append(stage)
 write("receipt.json",receipt)
 print("P24_RECURSOR_CANDIDATE_STAGE "+json.dumps(stage,ensure_ascii=False),flush=True)
 return rc
compile_rc=run_stage("compile",[LEAN]+flags+["-o",str(candidate_object),str(relative)])
rc=compile_rc
if compile_rc==0:
 receipt["candidate_object_before"]=info(candidate_object)
 write("receipt.json",receipt)
 replay_rc=run_stage("replay",[LEANCHECKER,"--verbose",candidate_module])
 audit_rc=run_stage("audit",[LEAN]+flags+["Audit.lean"])
 rc=replay_rc if replay_rc!=0 else audit_rc
 receipt["candidate_object_after"]=info(candidate_object)
 receipt["candidate_object_unchanged"]=receipt["candidate_object_before"]==receipt["candidate_object_after"]
 receipt["all_three_stages_passed"]=replay_rc==0 and audit_rc==0
postchecks={}
errors=[]
def perform(name,action):
 try:action();postchecks[name]=True
 except Exception as e:postchecks[name]=False;errors.append({"check":name,"error":type(e).__name__+": "+str(e)})
perform("source_pin_tracked_clean_original_verifiers",check_source)
def check_runtime():
 assert {n:digest(n) for n in runtime_expected}==runtime_expected
 assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=MATHLIB,text=True).strip()==PIN
perform("runtime_bytes_and_pin_unchanged",check_runtime)
def check_native():assert external.verify()==native_before
perform("native_binding_unchanged",check_native)
def check_bindings():
 after=snapshot(root,lib,nodes,toolchain,external)
 write("after-snapshot.json",after)
 assert after==before
 assert digest(registry)==registry_before
 verify_compilation(json.loads(registry.read_text()),nodes,after)
perform("canonical_closure_source_objects_and_registry_unchanged",check_bindings)
def check_isolated_inputs():
 assert candidate_path.read_bytes()==candidate
 assert (out/"OriginalAuditTemplate.lean").read_bytes()==template
 assert (out/"Audit.lean").read_bytes()==audit
 if compile_rc==0:assert receipt["candidate_object_unchanged"]
perform("isolated_inputs_and_object_unchanged",check_isolated_inputs)
if compile_rc==0 and receipt.get("all_three_stages_passed"):
 def check_audit():
  lines=(out/"audit.log").read_text().splitlines()
  inventory=[json.loads(x[len("P0_QUEUE_INVENTORY "):]) for x in lines if x.startswith("P0_QUEUE_INVENTORY ")]
  declarations=[json.loads(x[len("P0_QUEUE_DECL "):]) for x in lines if x.startswith("P0_QUEUE_DECL ")]
  assert len(inventory)==1
  names=[d["name"] for d in declarations]
  assert names and len(names)==len(set(names))
  assert sorted(names)==sorted(inventory[0]["serialized"])==sorted(inventory[0]["environment"])
  assert all(not d["unsafe"] and not d["partial"] and not d["axiom"] and set(d["axioms"])<={"propext","Classical.choice","Quot.sound"} and "⋯" not in d["type"] for d in declarations)
  receipt["audit_summary"]={"owned_count":len(names),"exact_inventory":True,"all_safe_nonpartial_nonaxiom":True,"allowed_axioms_only":True,"axiom_union":sorted({a for d in declarations for a in d["axioms"]}),"runFuel_declarations":[d for d in declarations if ".runFuel" in d["name"]]}
 perform("original_full_owned_audit_exact_inventory_and_rules",check_audit)
receipt["postchecks"]=postchecks
receipt["postcheck_errors"]=errors
receipt["registry_sha256_after"]=digest(registry)
receipt["wrapper_exit_code"]=rc if rc!=0 else (125 if errors else 0)
write("receipt.json",receipt)
print("P24_RECURSOR_CANDIDATE_DONE "+json.dumps({"receipt":info(out/"receipt.json"),"stages":receipt["stages"],"postchecks":postchecks,"postcheck_errors":errors,"wrapper_exit_code":receipt["wrapper_exit_code"],"audit_summary":receipt.get("audit_summary")},ensure_ascii=False),flush=True)
for name in ["receipt.json"]+[s["stage"]+".log" for s in receipt["stages"]]:
 raw=(out/name).read_bytes()
 compressed=gzip.compress(raw,mtime=0)
 packet={"file":info(out/name),"encoding":"base64(gzip(raw))","gzip_bytes":len(compressed),"gzip_sha256":hashlib.sha256(compressed).hexdigest(),"data":base64.b64encode(compressed).decode()}
 print("P24_RECURSOR_EVIDENCE "+json.dumps(packet),flush=True)
raise SystemExit(receipt["wrapper_exit_code"])

P24_CONCRETE_LOOP_REC_01

