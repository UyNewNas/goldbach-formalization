set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PY'
import hashlib,json,os,subprocess,sys,time
from pathlib import Path
root=Path.cwd()
pin="909214bbfb5ca9caa74fcc1b6f95b469bf43e125"
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==pin
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
assert os.statvfs(root).f_bavail*os.statvfs(root).f_frsize>=256*1024*1024
expected={
"verification/part2/run_winner9_private_checks.py":"164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
"verification/part2/run_winner9_private_audit.py":"571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
"verification/part2/winner9_private_audit_template.lean":"2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
"verification/part2/export_winner9_private_evidence.py":"fc0f97f4941339d9c0cb149055b233bf7a0daa3b8eff3da2998c921885948645"
}
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
for path,sha in expected.items():assert digest(path)==sha,(path,digest(path))
sys.path.insert(0,str(root/"verification/part2"))
from run_winner9_private_audit import project_nodes
roots=["ImbalancedChen.P2OriginalCompactQ80CompleteSoundness","ImbalancedChen.P2OriginalCompactCachedRun","ImbalancedChen.P2OriginalCompactQ80FixedBindings","ImbalancedChen.P4AOrdinaryRootFirstIntegral","ImbalancedChen.Part4ActualThirdFiniteDensityReserve"]
full=list(project_nodes(root,"ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"))
assert len(full)==324
fingerprint=hashlib.sha256(("\n".join(full)+"\n").encode()).hexdigest()
assert fingerprint=="c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
symbolic=set()
for name in roots:symbolic.update(project_nodes(root,name))
assert len(symbolic)==321
assert set(full)-symbolic=={"ImbalancedChen.P2OriginalCompactArchivedTotalCandidate","ImbalancedChen.P2OriginalCompactCachedEndpointCandidate","ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"}
out=root/".lake/p24-audit-export/symbolic-preflight-001"
assert not out.exists()
registry=root/".lake/p2-private/records.json"
before=digest(registry)
print(json.dumps({"phase":"symbolic_audit_preflight","source_pin":pin,"full_scope":324,"symbolic_scope":321,"ordered_fingerprint":fingerprint,"finite_A_credit":False,"whole_functional_credit":False}),flush=True)
start=time.monotonic()
subprocess.run([sys.executable,"-B","verification/part2/export_winner9_private_evidence.py",*full,"--output-dir",str(out),"--split","all"],check=True)
manifest_path=out/"manifest.json"
manifest=json.loads(manifest_path.read_text())
accepted=set(manifest["accepted_modules"])
unselected=set(manifest["unselected_modules"])
assert accepted.isdisjoint(unselected)
assert accepted|unselected==set(full)
assert manifest["duplicate_owned_declarations"]=={}
assert manifest["full_p2_complete"] is False
eligible=[name for name in full if name in symbolic and name in unselected]
after=digest(registry)
assert before==after
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==pin
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
result={
"phase":"symbolic_audit_preflight","source_pin":pin,"full_scope":324,"symbolic_scope":321,
"ordered_fingerprint":fingerprint,"manifest":str(manifest_path),"manifest_sha256":digest(manifest_path),
"selected_module_count":len(accepted),"selected_symbolic_count":len(accepted&symbolic),
"selected_modules":sorted(accepted),"unselected_modules":[name for name in full if name in unselected],
"eligible_missing_symbolic_count":len(eligible),"eligible_missing_symbolic_modules":eligible,
"duplicate_owned_declarations":manifest["duplicate_owned_declarations"],
"finite_A_credit":False,"whole_functional_credit":False,"full_scope_audit_complete":len(accepted)==324,
"registry_sha256_before":before,"registry_sha256_after":after,
"elapsed_seconds":time.monotonic()-start,"exporter_exit_code":0,"full_p2_complete":False}
(out/"p24-symbolic-preflight-summary.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result),flush=True)
PY
