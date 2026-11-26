set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_TREE_FOLD_01'
import hashlib, json, os, pathlib, signal, subprocess, sys, time
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-tree-fold-20261126/attempt-001")
payload=json.loads(r'''{"candidate":"import ImbalancedChen.P2OriginalPriorityForestLedger\n\n/-!\nIsolated computable fold over the existing source-indexed tree.\nThis module adds only the shared fold and its equations; it does not replace\nthe canonical Ledger or claim canonical compilation/audit credit.\n-/\n\nnamespace ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly\n\nopen P4AOriginalInitialSeedInventorySourceOnly\nopen P2OriginalAdaptiveSourceSplitSourceOnly\nopen P2OriginalPrioritySerialQueueSourceOnly\n\n/-- A total fold with an explicit structural fuel argument. -/\ndef treeFoldFuel {enclose : SeedCell → Bounds} {β : Type*}\n    (fallback : β) (leaf : SeedCell → ℕ → β)\n    (split : SeedCell → β → β → β) (fuel : ℕ) :\n    {c : SeedCell} → SourceTree enclose c → β :=\n  Nat.rec (motive := fun _ => {c : SeedCell} → SourceTree enclose c → β)\n    (fun {_} _ => fallback)\n    (fun _ previous {_} tree =>\n      match tree with\n      | .leaf c serial => leaf c serial\n      | .split c _ left right => split c (previous left) (previous right))\n    fuel\n\nprivate theorem treeFoldFuel_stable {enclose : SeedCell → Bounds} {β : Type*}\n    (fallback : β) (leaf : SeedCell → ℕ → β)\n    (split : SeedCell → β → β → β) {c : SeedCell}\n    (tree : SourceTree enclose c) (n m : ℕ)\n    (hn : sizeOf tree < n) (hm : sizeOf tree < m) :\n    treeFoldFuel fallback leaf split n tree =\n      treeFoldFuel fallback leaf split m tree := by\n  induction tree generalizing n m with\n  | leaf c serial =>\n      cases n with\n      | zero => omega\n      | succ n =>\n          cases m with\n          | zero => omega\n          | succ m => rfl\n  | split c width left right ihL ihR =>\n      cases n with\n      | zero => omega\n      | succ n =>\n          cases m with\n          | zero => omega\n          | succ m =>\n              have hnL : sizeOf left < n := by\n                simp only [SourceTree.split.sizeOf_spec] at hn\n                omega\n              have hnR : sizeOf right < n := by\n                simp only [SourceTree.split.sizeOf_spec] at hn\n                omega\n              have hmL : sizeOf left < m := by\n                simp only [SourceTree.split.sizeOf_spec] at hm\n                omega\n              have hmR : sizeOf right < m := by\n                simp only [SourceTree.split.sizeOf_spec] at hm\n                omega\n              change split c (treeFoldFuel fallback leaf split n left)\n                  (treeFoldFuel fallback leaf split n right) =\n                split c (treeFoldFuel fallback leaf split m left)\n                  (treeFoldFuel fallback leaf split m right)\n              exact congrArg₂ (split c) (ihL n m hnL hmL) (ihR n m hnR hmR)\n\n/-- The size bound is sufficient for every branch; it is not a node count. -/\ndef treeFold {enclose : SeedCell → Bounds} {β : Type*}\n    (fallback : β) (leaf : SeedCell → ℕ → β)\n    (split : SeedCell → β → β → β) {c : SeedCell}\n    (tree : SourceTree enclose c) : β :=\n  treeFoldFuel fallback leaf split (sizeOf tree + 1) tree\n\ntheorem treeFold_leaf {enclose : SeedCell → Bounds} {β : Type*}\n    (fallback : β) (leaf : SeedCell → ℕ → β)\n    (split : SeedCell → β → β → β) (c : SeedCell) (serial : ℕ) :\n    treeFold fallback leaf split (SourceTree.leaf (enclose := enclose) c serial) =\n      leaf c serial := by\n  rfl\n\ntheorem treeFold_split {enclose : SeedCell → Bounds} {β : Type*}\n    (fallback : β) (leaf : SeedCell → ℕ → β)\n    (split : SeedCell → β → β → β) (c : SeedCell)\n    (width : c.1 (originalAxis c) + 2 ≤ c.2 (originalAxis c))\n    (left : SourceTree enclose (sourceLeft c))\n    (right : SourceTree enclose (sourceRight c)) :\n    treeFold fallback leaf split (SourceTree.split c width left right) =\n      split c (treeFold fallback leaf split left) (treeFold fallback leaf split right) := by\n  have hleft : sizeOf left < sizeOf (SourceTree.split c width left right) := by\n    simp only [SourceTree.split.sizeOf_spec]\n    omega\n  have hright : sizeOf right < sizeOf (SourceTree.split c width left right) := by\n    simp only [SourceTree.split.sizeOf_spec]\n    omega\n  change split c\n      (treeFoldFuel fallback leaf split (sizeOf (SourceTree.split c width left right)) left)\n      (treeFoldFuel fallback leaf split (sizeOf (SourceTree.split c width left right)) right) =\n    split c (treeFoldFuel fallback leaf split (sizeOf left + 1) left)\n      (treeFoldFuel fallback leaf split (sizeOf right + 1) right)\n  exact congrArg₂ (split c)\n    (treeFoldFuel_stable fallback leaf split left _ _ hleft (by omega))\n    (treeFoldFuel_stable fallback leaf split right _ _ hright (by omega))\n\nend ImbalancedChen.P2OriginalPriorityForestLedgerSourceOnly\n"}''')
target="ImbalancedChen.P2OriginalPriorityForestLedger"
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
assert hashlib.sha1(b"blob "+str(len(source)).encode()+b"\0"+source).hexdigest()=="5df3acd15f06032d9bfd09b92966ec9ce1ee1a3c"
import base64,gzip
assert len(source)>0 and hashlib.sha256(source).hexdigest()=="eaa2da888add0b1790c829e43dad138b2bed8721500fdf97fe42eb95863a1af1"
candidate=payload["candidate"].encode("utf-8")
assert candidate.startswith(b"import ImbalancedChen.P2OriginalPriorityForestLedger\n")
assert b"inductive SourceTree" not in candidate and b"inductive SourceForest" not in candidate
assert b"noncomputable" not in candidate
assert hashlib.sha256(candidate).hexdigest()=="0f42b6bbc9b1e1079170162ed4095b7a23b95571ba6be652c39de38249dd9cc1"
out.mkdir(parents=True,exist_ok=False)
candidate_module="TreeFoldCandidate"
relative=pathlib.Path(candidate_module+".lean")
candidate_path=out/relative
candidate_path.parent.mkdir(parents=True,exist_ok=True)
candidate_path.write_bytes(candidate)
(out/"Ledger-original.lean").write_bytes(source)
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
 "purpose":"isolated additional total tree-fold helpers over canonical Ledger; compile replay original full-owned audit",
 "source_pin":pin,"module":target,"candidate_module":candidate_module,"canonical_closure_size":len(nodes),
 "original_source":info(out/"Ledger-original.lean"),"candidate_source":info(candidate_path),
 "source_changes":"new total Nat.rec fuel fold and sufficient-fuel/leaf/split proofs; canonical declarations imported unchanged",
 "canonical_source_imported_unchanged":True,"no_existing_declaration_redefined":True,
 "proof_only_adaptations":{},
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
print("P24_TREE_FOLD_CANDIDATE_BEGIN "+json.dumps({k:receipt[k] for k in ["source_pin","module","candidate_module","canonical_closure_size","candidate_source","original_source","template","audit_source","registry_sha256_before"]},ensure_ascii=False),flush=True)
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
 print("P24_TREE_FOLD_CANDIDATE_STAGE "+json.dumps(stage,ensure_ascii=False),flush=True)
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
  receipt["audit_summary"]={"owned_count":len(names),"exact_inventory":True,"all_safe_nonpartial_nonaxiom":True,"allowed_axioms_only":True,"axiom_union":sorted({a for d in declarations for a in d["axioms"]}),"forbidden_recursive_helpers_absent":not any("_unsafe_rec" in n for n in names)}
 perform("original_full_owned_audit_exact_inventory_and_rules",check_audit)
receipt["postchecks"]=postchecks
receipt["postcheck_errors"]=errors
receipt["registry_sha256_after"]=digest(registry)
receipt["wrapper_exit_code"]=rc if rc!=0 else (125 if errors else 0)
write("receipt.json",receipt)
print("P24_TREE_FOLD_CANDIDATE_DONE "+json.dumps({"receipt":info(out/"receipt.json"),"stages":receipt["stages"],"postchecks":postchecks,"postcheck_errors":errors,"wrapper_exit_code":receipt["wrapper_exit_code"],"audit_summary":receipt.get("audit_summary")},ensure_ascii=False),flush=True)
for name in ["receipt.json"]+[s["stage"]+".log" for s in receipt["stages"]]:
 raw=(out/name).read_bytes()
 compressed=gzip.compress(raw,mtime=0)
 packet={"file":info(out/name),"encoding":"base64(gzip(raw))","gzip_bytes":len(compressed),"gzip_sha256":hashlib.sha256(compressed).hexdigest(),"data":base64.b64encode(compressed).decode()}
 print("P24_TREE_FOLD_EVIDENCE "+json.dumps(packet),flush=True)
raise SystemExit(receipt["wrapper_exit_code"])

P24_TREE_FOLD_01
