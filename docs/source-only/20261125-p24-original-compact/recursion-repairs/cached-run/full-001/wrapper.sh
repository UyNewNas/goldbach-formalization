set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_CACHED_FULL_01'
import hashlib, json, os, pathlib, signal, subprocess, sys, time, base64, gzip
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-cached-run-recursors-20261126/full-001")
payload=json.loads(gzip.decompress(base64.b64decode("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")))
target="ImbalancedChen.P2OriginalCompactCachedRun"
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
assert hashlib.sha1(b"blob "+str(len(source)).encode()+b"\0"+source).hexdigest()=="a29463272ddf98167513f02adf70f653f8643ae2"
import base64,gzip
assert len(source)>0 and hashlib.sha256(source).hexdigest()=="b97e7cf8d0be80ccc693db96497250223c7f3a8256726311a457c1be84ccd9b0"
candidate=payload["candidate"].encode("utf-8")
expected_candidate=source
for patch in payload["patches"]:
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert expected_candidate.count(old)==1
 expected_candidate=expected_candidate.replace(old,new,1)
production=payload["production"].encode("utf-8")
assert production==expected_candidate
assert candidate==b"import TreeFoldCandidate\n"+production
restored=production
for patch in reversed(payload["patches"]):
 old=patch["old"].encode("utf-8");new=patch["new"].encode("utf-8")
 assert restored.count(new)==1
 restored=restored.replace(new,old,1)
assert restored==source
assert hashlib.sha256(candidate).hexdigest()=="3e14618365ae1a3bd43ae7adad5817f2d7dad58e6ae67ceddedef3e62c3675da"
helper_dir=pathlib.Path("/workspace/p24-tree-fold-20261126/attempt-002")
helper_expected={
 "receipt.json":"698b33e4bc13c7d10913b4e55d2f41b99636a55a525549a80cef6911dc3d18af",
 "TreeFoldCandidate.lean":"8a46d925da6ccc0f469d21449e24eeb7dd3d2921abba9b4cec757d9ecfc08778",
 "lib/TreeFoldCandidate.olean":"e2acd8b11f8ce4c4fd1184327bfa819a1f344468e79f89b02dec505c355a583c",
}
def check_helper():
 assert {name:digest(helper_dir/name) for name in helper_expected}==helper_expected
 h=json.loads((helper_dir/"receipt.json").read_text())
 assert h["wrapper_exit_code"]==0 and h["all_three_stages_passed"] is True
 assert all(h["postchecks"].values()) and not h["postcheck_errors"]
 assert h["native_before"]==native_before and h["runtime_sha256"]==runtime_expected
 assert h["verifier_sha256"]==expected and h["source_pin"]==pin
 assert h["registry_sha256_before"]==registry_before==h["registry_sha256_after"]
check_helper()
out.mkdir(parents=True,exist_ok=False)
candidate_module="CachedRunCandidate"
relative=pathlib.Path(candidate_module+".lean")
candidate_path=out/relative
candidate_path.parent.mkdir(parents=True,exist_ok=True)
candidate_path.write_bytes(candidate)
(out/"P2OriginalCompactCachedRun-production.lean").write_bytes(production)
(out/"CachedRun-original.lean").write_bytes(source)
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
env["LEAN_PATH"]=str(candidate_lib)+os.pathsep+str(helper_dir/"lib")+os.pathsep+original_env["LEAN_PATH"]
flags=["-t0","-j1","-M11264","-DwarningAsError=true","-DmaxRecDepth=50000","-DmaxHeartbeats=40000000"]
receipt={
 "purpose":"isolated eight CachedRun explicit recursor replacements; compile replay original full-owned audit",
 "source_pin":pin,"module":target,"candidate_module":candidate_module,"canonical_closure_size":len(nodes),
 "original_source":info(out/"CachedRun-original.lean"),"candidate_source":info(candidate_path),
 "source_changes":"eight structural recursion replacements using original address/seed and treeFold; only actual proof normalization changes",
 "inverse_source_bytes_equal":True,"all_other_definitions_and_all_theorem_statements_unchanged":True,
 "proof_only_adaptations":["cachedSeedForest_eq", "cachedSplitTreeAt_eq", "cachedSplitForestAt_eq", "cachedTreeJobs_eq", "cachedForestJobs_eq", "cachedTreeEntries_eq", "cachedEntries_eq", "cachedSplitForestAt_eq_zero"],
 "production_candidate":info(out/"P2OriginalCompactCachedRun-production.lean"),
 "diagnostic_only_import":"TreeFoldCandidate",
 "shared_helper_receipt_sha256":helper_expected["receipt.json"],
 "shared_helper_frozen_files":helper_expected,
 "template":info(out/"OriginalAuditTemplate.lean"),"audit_source":info(out/"Audit.lean"),
 "template_target_replacements":2,"template_other_bytes_equal":True,
 "canonical_source_and_object":before["project"][target],
 "registry_sha256_before":registry_before,"native_before":native_before,
 "runtime_sha256":runtime_expected,"verifier_sha256":expected,
 "before_snapshot_sha256":jd(before),"lean_path":env["LEAN_PATH"],"lean_sysroot":env["LEAN_SYSROOT"],
 "environment_only_delta":"isolated candidate lib and audited helper lib prepended; original ExternalSnapshot environment retained after them",
 "production_changed":False,"registry_writeback":False,"native_qualification_run":False,
 "canonical_credit":False,"full_P2_credit":False,"stages":[],
}
write("receipt.json",receipt)
print("P24_CACHED_CANDIDATE_BEGIN "+json.dumps({k:receipt[k] for k in ["source_pin","module","candidate_module","canonical_closure_size","candidate_source","original_source","template","audit_source","registry_sha256_before"]},ensure_ascii=False),flush=True)
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
 print("P24_CACHED_CANDIDATE_STAGE "+json.dumps(stage,ensure_ascii=False),flush=True)
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
 assert (out/"P2OriginalCompactCachedRun-production.lean").read_bytes()==production
 check_helper()
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
print("P24_CACHED_CANDIDATE_DONE "+json.dumps({"receipt":info(out/"receipt.json"),"stages":receipt["stages"],"postchecks":postchecks,"postcheck_errors":errors,"wrapper_exit_code":receipt["wrapper_exit_code"],"audit_summary":receipt.get("audit_summary")},ensure_ascii=False),flush=True)
for name in ["receipt.json"]+[s["stage"]+".log" for s in receipt["stages"]]:
 raw=(out/name).read_bytes()
 compressed=gzip.compress(raw,mtime=0)
 packet={"file":info(out/name),"encoding":"base64(gzip(raw))","gzip_bytes":len(compressed),"gzip_sha256":hashlib.sha256(compressed).hexdigest(),"data":base64.b64encode(compressed).decode()}
 print("P24_CACHED_EVIDENCE "+json.dumps(packet),flush=True)
raise SystemExit(receipt["wrapper_exit_code"])

P24_CACHED_FULL_01
