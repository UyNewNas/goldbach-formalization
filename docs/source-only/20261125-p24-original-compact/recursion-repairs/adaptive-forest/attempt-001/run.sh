set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_ADAPTIVE_FOREST_REC_01'
import hashlib, json, os, pathlib, signal, subprocess, sys, time
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-adaptive-forest-rec-20261126/attempt-001")
payload=json.loads(r'''{"candidate":"import ImbalancedChen.P2OriginalInitialClosedTree\nimport ImbalancedChen.P4AClosedCutTreePositionalChargeBinding\n\n/-!\nSOURCEONLY / UNCOMPILED / BROAD P2.4 OPEN.\n\nThe original producer starts its 21 adaptive subtrees at `initialSeeds`,\nwhose x/y lower endpoints are z0. The skeleton\u0027s unnormalised integer boxes\nare not those raw producer boxes. This file proves that grafting those\nsubtrees into the original skeleton gives exactly the raw producer forest\u0027s\nordered leaf domains, with no per-leaf set-equality premise. In particular,\nnormalisation occurs BEFORE the producer chooses later relative-width cuts.\n\nNo historical adaptive subtree, enclosure charge, analytic leaf payment, or\n2M-step endpoint is invented or assumed here. The original output did not\nserialize its adaptive tree or its leaf charges.\n-/\n\nnamespace ImbalancedChen.P2OriginalAdaptiveForestSourceIdentitySourceOnly\n\nnoncomputable section\nopen Set MeasureTheory\nopen OriginalThirdCompactPartitionSourceOnly\nopen P4AOriginalClosedTreeStructuralAggregationSourceOnly\nopen P4AClosedCutTreePositionalChargeBindingSourceOnly\nopen P4AClosedTreeCoordinatePropagationSourceOnly\nopen P4AOriginalInitialSeedInventorySourceOnly\nopen P2OriginalInitialClosedTreeSourceOnly\n\n/-- Traverse each supplied subtree on its corresponding domain, keeping all\nleaves. Length agreement is enforced by the graft constructor below. -/\ndef forestLeaves : List ClosedCutTree → List (Set Point) → List (Set Point) :=\n  List.rec (motive := fun _ => List (Set Point) → List (Set Point))\n    (fun _ => [])\n    (fun tree _ previous domains =>\n      match domains with\n      | [] => []\n      | s :: sets => closedLeaves tree s ++ previous sets)\n\nprivate theorem forestLeaves_append (left right : List ClosedCutTree)\n    (xs ys : List (Set Point)) (hlen : left.length = xs.length) :\n    forestLeaves (left ++ right) (xs ++ ys) =\n      forestLeaves left xs ++ forestLeaves right ys := by\n  induction left generalizing xs with\n  | nil =>\n      have hx : xs = [] := List.length_eq_zero_iff.mp hlen.symm\n      subst xs\n      rfl\n  | cons tree trees ih =>\n      cases xs with\n      | nil => simp at hlen\n      | cons s sets =>\n          have htail : trees.length = sets.length := Nat.succ.inj hlen\n          simpa only [List.cons_append, forestLeaves, List.append_assoc] using\n            congrArg (fun tail => closedLeaves tree s ++ tail) (ih sets htail)\n\n/-- Substitute one actual adaptive subtree at every skeleton leaf. All\nsupplied trees are consumed once, in the skeleton\u0027s original leaf order. -/\ndef graftSubtrees (skeleton : ClosedCutTree) (trees : List ClosedCutTree)\n    (hsize : trees.length = splitCount skeleton + 1) :\n    {refined : ClosedCutTree //\n      ∀ s, closedLeaves refined s = forestLeaves trees (closedLeaves skeleton s)} := by\n  induction skeleton generalizing trees with\n  | leaf =>\n      cases trees with\n      | nil => simp [splitCount_leaf] at hsize\n      | cons tree rest =>\n          have hrest : rest = [] := by\n            apply List.length_eq_zero_iff.mp\n            simp only [List.length_cons, splitCount_leaf] at hsize\n            omega\n          subst rest\n          exact ⟨tree, fun s => by simp [forestLeaves,closedLeaves]⟩\n  | split axis cut left right ihL ihR =>\n      let n := splitCount left + 1\n      have htotal : trees.length = n + (splitCount right + 1) := by\n        simp only [splitCount_split] at hsize\n        dsimp [n]\n        omega\n      have htake : (trees.take n).length = splitCount left + 1 := by\n        rw [List.length_take, Nat.min_eq_left (by omega : n ≤ trees.length)]\n      have hdrop : (trees.drop n).length = splitCount right + 1 := by\n        rw [List.length_drop]\n        omega\n      obtain ⟨left\u0027,hleft⟩ := ihL (trees.take n) htake\n      obtain ⟨right\u0027,hright⟩ := ihR (trees.drop n) hdrop\n      refine ⟨.split axis cut left\u0027 right\u0027, ?_⟩\n      intro s\n      let sL := s ∩ {t : Point | t axis ≤ (cut : ℝ) / coordinateDenominator}\n      let sR := s ∩ {t : Point | (cut : ℝ) / coordinateDenominator ≤ t axis}\n      change closedLeaves left\u0027 sL ++ closedLeaves right\u0027 sR =\n        forestLeaves trees (closedLeaves left sL ++ closedLeaves right sR)\n      rw [hleft,hright]\n      have hlen : (trees.take n).length = (closedLeaves left sL).length := by\n        rw [htake,closedLeaves_length]\n      conv_rhs => rw [← List.take_append_drop n trees]\n      rw [forestLeaves_append _ _ _ _ hlen]\n\n/-- Keep the recursive constructor\u0027s proof projection behind a theorem before\nspecialising it to a concrete skeleton. -/\nprivate theorem graftSubtrees_closedLeaves\n    (skeleton : ClosedCutTree) (trees : List ClosedCutTree)\n    (hsize : trees.length = splitCount skeleton + 1) (s : Set Point) :\n    closedLeaves (graftSubtrees skeleton trees hsize).val s =\n      forestLeaves trees (closedLeaves skeleton s) :=\n  (graftSubtrees skeleton trees hsize).property s\n\n/-- Raw integer boxes produced by the adaptive subtree at each ORIGINAL\nseed. This uses the raised z0 lower endpoints in the source inventory. -/\ndef sourceIntegerForest : List ClosedCutTree → List SeedCell → List SeedCell :=\n  List.rec (motive := fun _ => List SeedCell → List SeedCell)\n    (fun _ => [])\n    (fun tree _ previous domains =>\n      match domains with\n      | [] => []\n      | c :: cells => integerLeafBoxes tree c.1 c.2 ++ previous cells)\n\n/-- This is an exact ordered list identity, including empty source portions\nand both copies of closed split faces. No source cover is supplied as input. -/\ntheorem forestLeaves_eq_source_integer_domains\n    (trees : List ClosedCutTree) (cells : List SeedCell) :\n    forestLeaves trees (cells.map rootCell) =\n      (sourceIntegerForest trees cells).map rootCell := by\n  induction trees generalizing cells with\n  | nil => simp [forestLeaves,sourceIntegerForest]\n  | cons tree trees ih =>\n      cases cells with\n      | nil => simp [forestLeaves,sourceIntegerForest]\n      | cons c cells =>\n          simp only [List.map_cons,forestLeaves,sourceIntegerForest,List.map_append]\n          rw [ih]\n          congr 1\n          exact compact_closedLeaves_eq_integer_boxes tree c.1 c.2\n\nprivate theorem initialTree_splitCount : splitCount initialTree + 1 = 21 := by\n  have h := closedLeaves_initialTree_length\n  rw [closedLeaves_length] at h\n  exact h\n\n/-- A fully specified constructor at the actual original 21-seed skeleton.\nThe argument is the future immutable list of adaptive subtrees, not a\nnumerical enclosure or a hypothesis of the desired compact estimate. -/\ndef originalAdaptiveTree (trees : List ClosedCutTree) (hsize : trees.length = 21) :\n    ClosedCutTree :=\n  (graftSubtrees initialTree trees (hsize.trans initialTree_splitCount.symm)).val\n\n/-- Compare the constructor as a function before specialising its value\nprojection or transporting the equality through the leaf recursor. -/\nprivate theorem originalAdaptiveTree_eq_graftSubtrees :\n    originalAdaptiveTree =\n      fun (trees : List ClosedCutTree) (hsize : trees.length = 21) =>\n        (graftSubtrees initialTree trees (hsize.trans initialTree_splitCount.symm)).val := rfl\n\n/-- The missing source-to-tree dictionary for arbitrary adaptive descendants\nof all 21 actual raw seeds. This prevents choosing later axes from the\nskeleton\u0027s unnormalised boxes and preserves original x-outer/y-inner order. -/\ntheorem originalAdaptiveTree_closedLeaves (trees : List ClosedCutTree)\n    (hsize : trees.length = 21) :\n    closedLeaves (originalAdaptiveTree trees hsize) compactRegion =\n      (sourceIntegerForest trees initialSeeds).map rootCell := by\n  calc\n    closedLeaves (originalAdaptiveTree trees hsize) compactRegion =\n        closedLeaves\n          (graftSubtrees initialTree trees (hsize.trans initialTree_splitCount.symm)).val\n          compactRegion :=\n      congrFun (congrArg closedLeaves\n        (congrFun (congrFun originalAdaptiveTree_eq_graftSubtrees trees) hsize))\n        compactRegion\n    _ = forestLeaves trees (closedLeaves initialTree compactRegion) :=\n      graftSubtrees_closedLeaves initialTree trees\n        (hsize.trans initialTree_splitCount.symm) compactRegion\n    _ = forestLeaves trees (initialSeeds.map rootCell) :=\n      congrArg (forestLeaves trees) closedLeaves_initialTree_eq_original_seedCells\n    _ = (sourceIntegerForest trees initialSeeds).map rootCell :=\n      forestLeaves_eq_source_integer_domains trees initialSeeds\n\n/-- Exact equality with the ORIGINAL compact correction; this theorem has no\ncharge premise, positivity premise or analytic enclosure premise. -/\ntheorem originalCompact_eq_source_integer_forest (trees : List ClosedCutTree)\n    (hsize : trees.length = 21) :\n    originalCompactThirdCorrection =\n      (((sourceIntegerForest trees initialSeeds).map rootCell).map\n        (fun c => ∫ t in c, compactKernel t)).sum := by\n  rw [originalCompactThirdCorrection_eq_sum_closedLeaves\n      (originalAdaptiveTree trees hsize),originalAdaptiveTree_closedLeaves]\n\n/-- The existing positional binder can now consume the raw producer forest\nwith a proved leaf identity, instead of an assumed family/domain alignment. -/\ntheorem originalAdaptiveTree_charge_binding (trees : List ClosedCutTree)\n    (htrees : trees.length = 21) (charges : List ℤ)\n    (hcharges : charges.length = splitCount (originalAdaptiveTree trees htrees) + 1) :\n    LocalChargeBound\n        (attachCharges (originalAdaptiveTree trees htrees) charges hcharges).val\n        compactRegion ↔\n      List.Forall₂ (fun c q =>\n        (∫ t in c, compactKernel t) ≤ (q : ℝ) / 2^80)\n        ((sourceIntegerForest trees initialSeeds).map rootCell) charges := by\n  rw [attachCharges_local_iff,originalAdaptiveTree_closedLeaves]\n\n/-- In particular, the COMPLETE charge list is indexed by the complete raw\nforest, not by the positive-width heap. Exact leaves cannot be omitted. -/\ntheorem sourceIntegerForest_charge_length (trees : List ClosedCutTree)\n    (htrees : trees.length = 21) (charges : List ℤ)\n    (hcharges : charges.length = splitCount (originalAdaptiveTree trees htrees) + 1) :\n    charges.length = (sourceIntegerForest trees initialSeeds).length := by\n  have hlen := closedLeaves_length (originalAdaptiveTree trees htrees) compactRegion\n  rw [originalAdaptiveTree_closedLeaves,List.length_map] at hlen\n  exact hcharges.trans hlen.symm\n\nprivate theorem integerLeafBoxes_length (tree : ClosedCutTree)\n    (a b : Fin 3 → ℤ) :\n    (integerLeafBoxes tree a b).length = splitCount tree + 1 := by\n  have h := congrArg List.length (compact_closedLeaves_eq_integer_boxes tree a b)\n  simp only [List.length_map,closedLeaves_length] at h\n  exact h.symm\n\n/-- The complete raw forest has one more leaf for EVERY adaptive split;\nthe heap\u0027s filter on positive enclosure width is not present in this count. -/\ntheorem sourceIntegerForest_length (trees : List ClosedCutTree) (cells : List SeedCell)\n    (hsize : trees.length = cells.length) :\n    (sourceIntegerForest trees cells).length =\n      (trees.map splitCount).sum + trees.length := by\n  induction trees generalizing cells with\n  | nil => simp [sourceIntegerForest]\n  | cons tree trees ih =>\n      cases cells with\n      | nil => simp at hsize\n      | cons c cells =>\n          have htail : trees.length = cells.length := Nat.succ.inj hsize\n          simp only [sourceIntegerForest,List.length_append,integerLeafBoxes_length,\n            List.map_cons,List.sum_cons,List.length_cons]\n          rw [ih cells htail]\n          omega\n\n/-- If the frozen two-million split history is later supplied, its complete\nsource leaf inventory must contain 2,000,021 entries. This does not assert\nthat the missing history is supplied, or identify heap entries with leaves. -/\ntheorem frozen_original_full_leaf_count (trees : List ClosedCutTree)\n    (htrees : trees.length = 21)\n    (hsplits : (trees.map splitCount).sum = 2000000) :\n    (sourceIntegerForest trees initialSeeds).length = 2000021 := by\n  have hsize : trees.length = initialSeeds.length := by\n    rw [initialSeeds_eq_records,records_length]\n    exact htrees\n  rw [sourceIntegerForest_length trees initialSeeds hsize,hsplits,htrees]\n\nend\nend ImbalancedChen.P2OriginalAdaptiveForestSourceIdentitySourceOnly\r\n","definitionPatches":[{"old":"def forestLeaves : List ClosedCutTree → List (Set Point) → List (Set Point)\n  | tree :: trees, s :: sets => closedLeaves tree s ++ forestLeaves trees sets\n  | _, _ => []\n\n","new":"def forestLeaves : List ClosedCutTree → List (Set Point) → List (Set Point) :=\n  List.rec (motive := fun _ => List (Set Point) → List (Set Point))\n    (fun _ => [])\n    (fun tree _ previous domains =>\n      match domains with\n      | [] => []\n      | s :: sets => closedLeaves tree s ++ previous sets)\n\n"},{"old":"def sourceIntegerForest : List ClosedCutTree → List SeedCell → List SeedCell\n  | tree :: trees, c :: cells =>\n      integerLeafBoxes tree c.1 c.2 ++ sourceIntegerForest trees cells\n  | _, _ => []\n\n","new":"def sourceIntegerForest : List ClosedCutTree → List SeedCell → List SeedCell :=\n  List.rec (motive := fun _ => List SeedCell → List SeedCell)\n    (fun _ => [])\n    (fun tree _ previous domains =>\n      match domains with\n      | [] => []\n      | c :: cells => integerLeafBoxes tree c.1 c.2 ++ previous cells)\n\n"}],"proofPatches":[],"original_sha256":"6a08b33581f5ff540aa2b61be54783967090bbbcc79dd66fd6f6e3227541bc6f","original_git_blob":"808f19f951eccf86dcbac019e60f87c3940ed1ba","candidate_sha256":"c24578f4b2564d343c9810aec61f12f91f5072473a73e411b19cdc645b943f43"}''')
target="ImbalancedChen.P2OriginalAdaptiveForestSourceIdentity"
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
assert hashlib.sha1(b"blob "+str(len(source)).encode()+b"\0"+source).hexdigest()==payload["original_git_blob"]
import base64,gzip
assert len(source)>0 and hashlib.sha256(source).hexdigest()==payload["original_sha256"]
candidate=payload["candidate"].encode("utf-8")
patches=payload["definitionPatches"]+payload["proofPatches"]
expected_candidate=source
for patch in patches:
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert expected_candidate.count(old)==1
 expected_candidate=expected_candidate.replace(old,new,1)
assert candidate==expected_candidate
restored=candidate
for patch in reversed(patches):
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert restored.count(new)==1
 restored=restored.replace(new,old,1)
assert restored==source
assert hashlib.sha256(candidate).hexdigest()==payload["candidate_sha256"]
out.mkdir(parents=True,exist_ok=False)
candidate_module="AdaptiveForestCandidate"
relative=pathlib.Path(candidate_module+".lean")
candidate_path=out/relative
candidate_path.parent.mkdir(parents=True,exist_ok=True)
candidate_path.write_bytes(candidate)
(out/"AdaptiveForest-original.lean").write_bytes(source)
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
 "purpose":"isolated AdaptiveForest forestLeaves/sourceIntegerForest List.rec candidate compile replay original full-owned audit",
 "source_pin":pin,"module":target,"candidate_module":candidate_module,"canonical_closure_size":len(nodes),
 "original_source":info(out/"AdaptiveForest-original.lean"),"candidate_source":info(candidate_path),
 "source_changes":"forestLeaves and sourceIntegerForest named recursion to direct List.rec carrying the second list; identical empty/truncated pairings and append order",
 "inverse_source_bytes_equal":True,"all_other_definitions_and_all_theorem_statements_unchanged":True,
 "proof_only_adaptations":payload["proofPatches"],
 "all_original_theorem_complete_blocks_unchanged":not payload["proofPatches"],
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
  receipt["audit_summary"]={"owned_count":len(names),"exact_inventory":True,"all_safe_nonpartial_nonaxiom":True,"allowed_axioms_only":True,"axiom_union":sorted({a for d in declarations for a in d["axioms"]}),"updated_declarations":[{k:d[k] for k in ["name","unsafe","partial","axiom","axioms"]} for d in declarations if ".forestLeaves" in d["name"] or ".sourceIntegerForest" in d["name"]]}
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
P24_ADAPTIVE_FOREST_REC_01


