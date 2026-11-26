set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_LEDGER_RECURSORS_02'
import hashlib, json, os, pathlib, signal, subprocess, sys, time, base64, gzip
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-ledger-recursors-20261126/attempt-002")
payload=json.loads(gzip.decompress(base64.b64decode("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")))
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
expected_candidate=source
for patch in payload["patches"]:
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert expected_candidate.count(old)==1
 expected_candidate=expected_candidate.replace(old,new,1)
assert candidate==expected_candidate
restored=candidate
for patch in reversed(payload["patches"]):
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert restored.count(new)==1
 restored=restored.replace(new,old,1)
assert restored==source
assert hashlib.sha256(candidate).hexdigest()=="11e2a50288146a94cbb6351fd6f5b279469c6cce1d6af437569260d54880cc0c"
out.mkdir(parents=True,exist_ok=False)
candidate_module="LedgerCandidate"
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
 "purpose":"isolated five Ledger named recursion repairs with total tree fold; compile replay original full-owned audit",
 "source_pin":pin,"module":target,"candidate_module":candidate_module,"canonical_closure_size":len(nodes),
 "original_source":info(out/"Ledger-original.lean"),"candidate_source":info(candidate_path),
 "source_changes":"five named recursions replaced by total treeFold/List.rec; shared public fold and leaf/split equation proofs; all 32 original theorem heads unchanged; seven proof bodies only normalize already-proved fold equations or List.rec IHs",
 "inverse_source_bytes_equal":True,"all_other_definitions_and_all_theorem_statements_unchanged":True,
 "proof_only_adaptations":["tree_integer_boxes", "forest_integer_boxes", "tree_entry_enclose", "tree_refinement_exists", "tree_refines_entries", "forest_refines_entries", "seedForest_entries_length"],
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
print("P24_LEDGER_CANDIDATE_BEGIN "+json.dumps({k:receipt[k] for k in ["source_pin","module","candidate_module","canonical_closure_size","candidate_source","original_source","template","audit_source","registry_sha256_before"]},ensure_ascii=False),flush=True)
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
 print("P24_LEDGER_CANDIDATE_STAGE "+json.dumps(stage,ensure_ascii=False),flush=True)
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
print("P24_LEDGER_CANDIDATE_DONE "+json.dumps({"receipt":info(out/"receipt.json"),"stages":receipt["stages"],"postchecks":postchecks,"postcheck_errors":errors,"wrapper_exit_code":receipt["wrapper_exit_code"],"audit_summary":receipt.get("audit_summary")},ensure_ascii=False),flush=True)
for name in ["receipt.json"]+[s["stage"]+".log" for s in receipt["stages"]]:
 raw=(out/name).read_bytes()
 compressed=gzip.compress(raw,mtime=0)
 packet={"file":info(out/name),"encoding":"base64(gzip(raw))","gzip_bytes":len(compressed),"gzip_sha256":hashlib.sha256(compressed).hexdigest(),"data":base64.b64encode(compressed).decode()}
 print("P24_LEDGER_EVIDENCE "+json.dumps(packet),flush=True)
raise SystemExit(receipt["wrapper_exit_code"])

P24_LEDGER_RECURSORS_02
