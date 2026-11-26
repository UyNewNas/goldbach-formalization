set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PRE'
import hashlib,json,subprocess
from pathlib import Path
old="909214bbfb5ca9caa74fcc1b6f95b469bf43e125"
new="6e616f4e0372555f7a78bcdba3e198d0e277eec8"
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==old
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
receipt=json.loads(Path("/workspace/p24-logpoint-natrec-20261126/attempt-002/diagnostic.json").read_text())
assert receipt["diagnostic_passed"] is True and receipt["original_replay_and_owned_rules_passed"] is True
assert receipt["source_sha256"]=="07798022d2370d12091d123a8f55ab106ee08a02b5dd104ce84d30aed3882552"
fetch=subprocess.run(["git","fetch","origin",new],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert fetch.returncode==0,"git fetch failed; credentials and raw stderr not emitted"
subprocess.run(["git","merge","--ff-only",new],check=True)
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==new
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
assert hashlib.sha256(Path("ImbalancedChen/P2HistoricLogPointInterpreter.lean").read_bytes()).hexdigest()==receipt["source_sha256"]
PRE
python3 -B - <<'PY'
import hashlib,json,sys,subprocess,time
from pathlib import Path
sys.path.insert(0,str(Path("verification/part2").resolve()))
from run_winner9_private_audit import project_nodes
roots=["ImbalancedChen.P2OriginalCompactQ80CompleteSoundness","ImbalancedChen.P2OriginalCompactCachedRun","ImbalancedChen.P2OriginalCompactQ80FixedBindings","ImbalancedChen.P4AOrdinaryRootFirstIntegral","ImbalancedChen.Part4ActualThirdFiniteDensityReserve"]
all_names=list(project_nodes(Path.cwd(),"ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint"))
assert len(all_names)==324
assert hashlib.sha256(("\n".join(all_names)+"\n").encode()).hexdigest()=="c1c9c343b36095651f8bb71408a82faf9e4b285d8dad80e634e9cf6b257d396f"
prereq=set()
for name in roots: prereq.update(project_nodes(Path.cwd(),name))
assert len(prereq)==321
assert len(project_nodes(Path.cwd(),"ImbalancedChen.P2OriginalCompactArchivedTotalCandidate"))==102
assert hashlib.sha256(Path("verification/part2/run_winner9_private_checks.py").read_bytes()).hexdigest()=="164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac"
assert hashlib.sha256(Path("ImbalancedChen/P2OriginalCompactCachedRun.lean").read_bytes()).hexdigest()=="b97e7cf8d0be80ccc693db96497250223c7f3a8256726311a457c1be84ccd9b0"
assert hashlib.sha256(Path("ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean").read_bytes()).hexdigest()=="03e45537c9309e79c46fd924383d850935cb2b82a5de7ac4205731f4df048fcd"
common=[sys.executable,"-B","verification/part2/run_winner9_private_checks.py","--baseline-root","/workspace/p2-4-compact-proof-20261125/.lake/p24-baseline-8657/attempt-001","--external-snapshot","/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json","--memory-mb","11264","--workers","1","--threads","1"]
print(json.dumps({"source_pin":"6e616f4e0372555f7a78bcdba3e198d0e277eec8","phase":"strict_symbolic_after_node_blocks_natrec_01","prerequisite_scope":321,"target_scope":102,"full_scope":324}),flush=True)
print("P24_STRICT_SYMBOLIC_NODE_BLOCKS_NATREC_01_BEGIN",flush=True)
start=time.time_ns()
proc=subprocess.Popen(common+["--time-budget-seconds","3000"]+roots)
seen={}
def report():
    for path in sorted(Path(".lake/p2-private/logs").glob("*.log")):
        if path.stat().st_mtime_ns < start: continue
        pos=seen.get(str(path),0)
        with path.open("rb") as f:
            f.seek(pos)
            new=f.read()
        if new:
            sys.stdout.buffer.write(("\nLIVE_MODULE_LOG "+str(path)+" offset="+str(pos)+"\n").encode()+new+b"\n")
            sys.stdout.buffer.flush()
            seen[str(path)]=pos+len(new)
while True:
    try: rc=proc.wait(timeout=30)
    except subprocess.TimeoutExpired:
        report()
        continue
    report()
    raise SystemExit(rc)
PY