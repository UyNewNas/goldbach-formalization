set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'P24_FLAGS_READBACK'
import hashlib,json,pathlib,re,subprocess,sys,time
root=pathlib.Path.cwd()
out=pathlib.Path("/workspace/p24-finite-selector-flags-20261126/attempt-001")
pre=json.loads((out/"receipt.json").read_text())
target=pre["module"]
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==pre["source_pin"]
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
def digest(path):
 with pathlib.Path(path).open("rb") as f:return hashlib.file_digest(f,"sha256").hexdigest()
def info(path):return {"path":str(path),"bytes":pathlib.Path(path).stat().st_size,"sha256":digest(path)}
assert {n:digest(root/n) for n in pre["verifier_sha256"]}==pre["verifier_sha256"]
assert {n:digest(n) for n in pre["runtime_sha256"]}==pre["runtime_sha256"]
registry=root/".lake/p2-private/records.json"
assert digest(registry)==pre["registry_sha256_before"]
sys.path.insert(0,str(root/"verification/part2"))
from run_winner9_private_audit import LEAN, MATHLIB, PIN, project_nodes, snapshot, verify_compilation
from winner9_external_snapshot import ExternalSnapshot, mark_project_nodes
assert subprocess.check_output(["git","rev-parse","HEAD"],cwd=MATHLIB,text=True).strip()==PIN
external=ExternalSnapshot(pathlib.Path(pre["native_before"]["snapshot"]),lean=LEAN,mathlib_pin=PIN,project_lib=root/".lake/p2-private/lib")
assert external.binding()==pre["native_before"]
before=json.loads((out/"before-snapshot.json").read_text())
after=json.loads((out/"after-snapshot.json").read_text())
assert before==after
nodes=project_nodes(root,target)
mark_project_nodes(nodes,set(external.modules))
current=snapshot(root,root/".lake/p2-private/lib",nodes,before["toolchain"],external)
assert current==before
verify_compilation(json.loads(registry.read_text()),nodes,current)
raw=(out/"flags.log").read_bytes()
print("P24_FINITE_SELECTOR_RECOVERED_FLAGS_BEGIN",flush=True)
sys.stdout.buffer.write(raw);sys.stdout.buffer.flush()
print("\nP24_FINITE_SELECTOR_RECOVERED_FLAGS_END",flush=True)
lines=raw.decode("utf-8").splitlines()
decls=[json.loads(x[len("P24_FINITE_SELECTOR_FLAGS_DECL "):]) for x in lines if x.startswith("P24_FINITE_SELECTOR_FLAGS_DECL ")]
summaries=[json.loads(x[len("P24_FINITE_SELECTOR_FLAGS_SUMMARY "):]) for x in lines if x.startswith("P24_FINITE_SELECTOR_FLAGS_SUMMARY ")]
inventories=[json.loads(x[len("P24_FINITE_SELECTOR_FLAGS_INVENTORY "):]) for x in lines if x.startswith("P24_FINITE_SELECTOR_FLAGS_INVENTORY ")]
assert len(summaries)==len(inventories)==1
names=[d["name"] for d in decls]
assert len(names)==len(set(names))==summaries[0]["owned_count"]
assert sorted(names)==sorted(inventories[0]["serialized"])==sorted(inventories[0]["environment"])
full=project_nodes(root,"ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint")
assert len(full)==324
assert hashlib.sha256(("\n".join(full)+"\n").encode()).hexdigest()=="c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
pattern=re.compile(r"firstMax\.(?:eq_[0-9]+|_sunfold|_unsafe_rec)")
references=[]
for name,node in full.items():
 for line_no,line in enumerate(pathlib.Path(node["source"]).read_text().splitlines(),1):
  if pattern.search(line): references.append({"module":name,"line":line_no,"text":line})
own_refs=[{"line":i,"text":s} for i,s in enumerate(pathlib.Path(nodes[target]["source"]).read_text().splitlines(),1) if "firstMax" in s]
receipt={
 "purpose":"read-only recovery of existing FiniteSelector flags; no Lean subprocess",
 "original_task_id":"2213320c951f4045be5c5c916b76a59d","original_wrapper_exit_code":1,
 "original_wrapper_failure":"FileNotFoundError: rg after flags child and saved after-snapshot",
 "original_lean_child_exit_code":None,"original_lean_child_exit_code_not_preserved":True,
 "source_pin":pre["source_pin"],"source":pre["source"],"object":pre["object"],
 "flags_log":info(out/"flags.log"),"enumeration_complete":True,
 "summary":summaries[0],"bad_declarations":[d for d in decls if d["rejected_by_original_flag_rules"]],
 "all_closure_source_objects_before_after_current_equal":True,"verify_compilation_passed":True,
 "registry_sha256":digest(registry),"registry_unchanged":True,"native_binding_unchanged":True,
 "source_tracked_clean_and_tool_hashes_unchanged":True,
 "reference_scan_scope":324,"generated_equation_references":references,"local_firstMax_references":own_refs,
 "new_lean_executions":0,"acceptance_credit":False,"canonical_credit":False,"full_owned_audit_credit":False,
}
path=out/"recovery-receipt.json"
assert not path.exists()
path.write_text(json.dumps(receipt,ensure_ascii=False,indent=2)+"\n")
print("P24_FINITE_SELECTOR_RECOVERY_RECEIPT "+json.dumps({"file":info(path),"receipt":receipt},ensure_ascii=False),flush=True)
P24_FLAGS_READBACK
