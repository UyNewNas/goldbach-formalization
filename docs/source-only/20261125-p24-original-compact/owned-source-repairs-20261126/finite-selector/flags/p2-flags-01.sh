set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_FINITE_SELECTOR_DRIVER'
import hashlib, json, os, pathlib, signal, subprocess, sys, time
root=pathlib.Path("/workspace/p2-4-compact-proof-20261125")
out=pathlib.Path("/workspace/p24-finite-selector-flags-20261126/attempt-001")
payload=json.loads(r'''{"flags":"/- Diagnostic only. Complete owned inventory and flags, with transitive axioms.\nNo full-type or acceptance credit. Original compiled source and object remain untouched. -/\nimport ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector\nimport Lean\nimport Lean.Util.CollectAxioms\n\nopen Lean Elab Command in\nrun_cmd do\n  let env ← getEnv\n  let moduleName := `ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector\n  let some idx := env.getModuleIdx? moduleName\n    | throwError \"Missing target module\"\n  let names := env.const2ModIdx.fold (init := (#[] : Array Name)) fun ns n i =>\n    if i == idx && (env.find? n).isSome then ns.push n else ns\n  let mut serialized : Array Name := #[]\n  let mut found := false\n  for i in List.range env.header.modules.size do\n    let imported := env.header.modules[i]!\n    if imported.module == moduleName then\n      if found then throwError \"Duplicate module\"\n      found := true\n      let data := env.header.moduleData[i]!\n      if data.isModule || !imported.importAll || !imported.hasData then\n        throwError \"Incomplete imported legacy data\"\n      serialized := data.constNames\n  unless found && names.size > 0 && names.qsort Name.lt == serialized.qsort Name.lt do\n    throwError \"Complete serialized/environment inventory mismatch\"\n  let inventory := Json.mkObj [\n    (\"module\", toJson moduleName.toString),\n    (\"serialized\", toJson (serialized.map Name.toString)),\n    (\"environment\", toJson (names.map Name.toString)),\n    (\"owned_count\", toJson names.size),\n    (\"diagnostic_only\", toJson true), (\"acceptance_credit\", toJson false)]\n  liftIO <| IO.println s!\"P24_FINITE_SELECTOR_FLAGS_INVENTORY {inventory.compress}\"\n  let mut flagged : Array Name := #[]\n  let mut unsafeNames : Array Name := #[]\n  let mut partialNames : Array Name := #[]\n  let mut axiomNames : Array Name := #[]\n  let mut emitted : Array Name := #[]\n  for name in names.qsort Name.lt do\n    let some info := env.find? name\n      | throwError \"Missing inventoried declaration {name}\"\n    let kind := match info with\n      | .axiomInfo _ => \"axiom\"\n      | .defnInfo _ => \"definition\"\n      | .thmInfo _ => \"theorem\"\n      | .opaqueInfo _ => \"opaque\"\n      | .quotInfo _ => \"quotient\"\n      | .inductInfo _ => \"inductive\"\n      | .ctorInfo _ => \"constructor\"\n      | .recInfo _ => \"recursor\"\n    let axioms ← collectAxioms name\n    let forbidden := axioms.filter fun ax => !#[`propext, `Classical.choice, `Quot.sound].contains ax\n    let rejected := info.isUnsafe || info.isPartial || info.isAxiom || !forbidden.isEmpty\n    if rejected then flagged := flagged.push name\n    if info.isUnsafe then unsafeNames := unsafeNames.push name\n    if info.isPartial then partialNames := partialNames.push name\n    if info.isAxiom then axiomNames := axiomNames.push name\n    emitted := emitted.push name\n    let record := Json.mkObj [\n      (\"module\", toJson moduleName.toString), (\"name\", toJson name.toString),\n      (\"user_name\", toJson (privateToUserName name).toString),\n      (\"private\", toJson (isPrivateName name)), (\"kind\", toJson kind),\n      (\"unsafe\", toJson info.isUnsafe), (\"partial\", toJson info.isPartial),\n      (\"axiom\", toJson info.isAxiom),\n      (\"axioms\", toJson (axioms.map Name.toString)),\n      (\"forbidden_axioms\", toJson (forbidden.map Name.toString)),\n      (\"rejected_by_original_flag_rules\", toJson rejected)]\n    liftIO <| IO.println s!\"P24_FINITE_SELECTOR_FLAGS_DECL {record.compress}\"\n  unless emitted == names.qsort Name.lt do\n    throwError \"Diagnostic output did not cover every owned declaration\"\n  let summary := Json.mkObj [\n    (\"module\", toJson moduleName.toString), (\"diagnostic_only\", toJson true),\n    (\"owned_count\", toJson names.size), (\"emitted_count\", toJson emitted.size),\n    (\"serialized_environment_equal\", toJson true),\n    (\"flagged_names\", toJson (flagged.map Name.toString)),\n    (\"unsafe_names\", toJson (unsafeNames.map Name.toString)),\n    (\"partial_names\", toJson (partialNames.map Name.toString)),\n    (\"axiom_names\", toJson (axiomNames.map Name.toString)),\n    (\"original_flag_rules_satisfied\", toJson flagged.isEmpty),\n    (\"full_types_checked\", toJson false), (\"transitive_axioms_checked\", toJson true),\n    (\"compile_credit\", toJson false), (\"kernel_credit\", toJson false),\n    (\"acceptance_credit\", toJson false), (\"full_owned_audit_credit\", toJson false),\n    (\"finite_A_credit\", toJson false), (\"P2_acceptance_credit\", toJson false)]\n  liftIO <| IO.println s!\"P24_FINITE_SELECTOR_FLAGS_SUMMARY {summary.compress}\"\n"}''')
target="ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector"
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
assert hashlib.sha1(b"blob "+str(len(source)).encode()+b"\0"+source).hexdigest()=="df536731c2b67dd2129522f1a96b9470cd405f4f"
out.mkdir(parents=True,exist_ok=False)
(out/"FiniteSelector-original.lean").write_bytes(source)
(out/"Flags.lean").write_text(payload["flags"],encoding="utf-8")
write("before-snapshot.json",before)
write("selected-records.json",{n:records[n] for n in nodes})
env=external.environment(os.environ)
command=[LEAN,"-t0","-j1","-M11264","-DwarningAsError=true","-DmaxRecDepth=50000","-DmaxHeartbeats=40000000","Flags.lean"]
receipt={
 "task":"single-module complete owned flags diagnostic",
 "source_pin":pin,"module":target,"closure_size":len(nodes),
 "diagnostic_only":True,"acceptance_credit":False,"canonical_credit":False,"full_owned_audit_credit":False,
 "original_module_compile_started":False,"original_full_audit_repeated":False,"production_changed":False,
 "source":info(out/"FiniteSelector-original.lean"),"diagnostic_source":info(out/"Flags.lean"),
 "object":before["project"][target],"registry_sha256_before":registry_before,
 "native_before":native_before,"runtime_sha256":runtime_expected,"verifier_sha256":expected,
 "before_snapshot_sha256":jd(before),"before_snapshot_file":info(out/"before-snapshot.json"),
 "command":command,"lean_path":env["LEAN_PATH"],"lean_sysroot":env["LEAN_SYSROOT"],
}
write("receipt.json",receipt)
print("P24_FINITE_SELECTOR_FLAGS_BEGIN "+json.dumps(receipt,ensure_ascii=False),flush=True)
started=time.monotonic()
timed_out=False
with (out/"flags.log").open("wb") as log:
 proc=subprocess.Popen(command,cwd=out,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 try: rc=proc.wait(timeout=650)
 except subprocess.TimeoutExpired:
  timed_out=True
  os.killpg(proc.pid,signal.SIGKILL)
  proc.wait()
  rc=124
receipt.update({"child_exit_code":rc,"child_timed_out":timed_out,"child_seconds":time.monotonic()-started,"flags_log":info(out/"flags.log")})
postchecks={}
errors=[]
def perform(name,action):
 try:
  action()
  postchecks[name]=True
 except Exception as e:
  postchecks[name]=False
  errors.append({"check":name,"error":type(e).__name__+": "+str(e)})
perform("source_pin_tracked_clean_verifier_bytes",check_source)
def runtime_check():
 assert {n:digest(n) for n in runtime_expected}==runtime_expected
 assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=MATHLIB,text=True).strip()==PIN
perform("runtime_bytes_and_pin_unchanged",runtime_check)
def native_check():
 assert external.verify()==native_before
perform("native_binding_unchanged",native_check)
def binding_check():
 after=snapshot(root,lib,nodes,toolchain,external)
 write("after-snapshot.json",after)
 assert after==before
 assert digest(registry)==registry_before
 verify_compilation(json.loads(registry.read_text()),nodes,after)
perform("all_closure_source_objects_and_registry_unchanged",binding_check)
full_nodes=project_nodes(root,"ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint")
assert len(full_nodes)==324
assert hashlib.sha256(("\n".join(full_nodes)+"\n").encode()).hexdigest()=="c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
searches=[
 ("firstMax-generated-references",["rg","-n",r"firstMax\.(eq_[0-9]+|_sunfold|_unsafe_rec)",*[str(n["source"]) for n in full_nodes.values()]]),
 ("firstMax-source-references",["rg","-n","firstMax",str(nodes[target]["source"])]),
]
receipt["source_reference_searches"]=[]
for name,cmd in searches:
 r=subprocess.run(cmd,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(name+".log")).write_bytes(r.stdout)
 assert r.returncode in (0,1)
 receipt["source_reference_searches"].append({"name":name,"exit_code":r.returncode,"log":info(out/(name+".log")),"searched_scope":324 if name=="firstMax-generated-references" else 1})
if rc==0:
 lines=(out/"flags.log").read_text().splitlines()
 decls=[json.loads(x[len("P24_FINITE_SELECTOR_FLAGS_DECL "):]) for x in lines if x.startswith("P24_FINITE_SELECTOR_FLAGS_DECL ")]
 summaries=[json.loads(x[len("P24_FINITE_SELECTOR_FLAGS_SUMMARY "):]) for x in lines if x.startswith("P24_FINITE_SELECTOR_FLAGS_SUMMARY ")]
 inventories=[json.loads(x[len("P24_FINITE_SELECTOR_FLAGS_INVENTORY "):]) for x in lines if x.startswith("P24_FINITE_SELECTOR_FLAGS_INVENTORY ")]
 assert len(summaries)==len(inventories)==1
 names=[d["name"] for d in decls]
 assert len(names)==len(set(names))==summaries[0]["owned_count"]
 assert sorted(names)==sorted(inventories[0]["serialized"])==sorted(inventories[0]["environment"])
 receipt["summary"]=summaries[0]
 receipt["bad_declarations"]=[d for d in decls if d["rejected_by_original_flag_rules"]]
receipt["postchecks"]=postchecks
receipt["postcheck_errors"]=errors
receipt["registry_sha256_after"]=digest(registry)
receipt["wrapper_exit_code"]=rc if rc!=0 else (125 if errors else 0)
write("receipt.json",receipt)
print("P24_FINITE_SELECTOR_FLAGS_RECEIPT "+json.dumps({"file":info(out/"receipt.json"),"receipt":receipt},ensure_ascii=False),flush=True)
for name in ["flags","firstMax-generated-references","firstMax-source-references"]:
 data=(out/(name+".log")).read_bytes()
 if len(data)<=1200000:
  print("P24_FINITE_SELECTOR_FULL_LOG_BEGIN "+name,flush=True)
  sys.stdout.buffer.write(data)
  sys.stdout.buffer.flush()
  print("\nP24_FINITE_SELECTOR_FULL_LOG_END "+name,flush=True)
 else:
  print("P24_FINITE_SELECTOR_FULL_LOG_RETAINED "+json.dumps(info(out/(name+".log"))),flush=True)
raise SystemExit(receipt["wrapper_exit_code"])

P24_FINITE_SELECTOR_DRIVER
