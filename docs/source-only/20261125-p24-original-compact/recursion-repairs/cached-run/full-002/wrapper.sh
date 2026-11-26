set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_CACHED_FULL_02'
import hashlib, json, os, pathlib, signal, subprocess, sys, time, base64, gzip
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-cached-run-recursors-20261126/full-002")
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
assert hashlib.sha256(candidate).hexdigest()=="ff2687744856f9e7e2ff03a574a06026e30240820bd5b6fe007731eaa9960ee2"
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

P24_CACHED_FULL_02
