set -euo pipefail
cd /workspace/p2-4-compact-proof-20261125
export PYTHONDONTWRITEBYTECODE=1
export GIT_OPTIONAL_LOCKS=0
exec 9<.lake/p2-private/p24-migration.lock
flock -n 9
python3 -B - <<'PY'
import base64,hashlib,json,os,re,subprocess,sys,time
from pathlib import Path
root=Path.cwd()
pin="909214bbfb5ca9caa74fcc1b6f95b469bf43e125"
assert subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()==pin
assert not subprocess.check_output(["git","status","--porcelain","--untracked-files=no"],text=True).strip()
assert os.statvfs(root).f_bavail*os.statvfs(root).f_frsize>=64*1024*1024
source=root/"ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.lean"
out=root/".lake/p24-diagnostic/finite-a-kernel-raw-05"
out.mkdir(parents=True,exist_ok=False)
markerlog=out/"markers.log"
original=source.read_bytes()
assert hashlib.sha256(original).hexdigest()=="f3b608cd96e21bd7bc425526d3731f86ed2440874a00ff61f14f3cfeb77e0e54"
candidate=original
assert hashlib.sha256(candidate).hexdigest()=="f3b608cd96e21bd7bc425526d3731f86ed2440874a00ff61f14f3cfeb77e0e54"
raw_tactic="open Lean Meta Elab Tactic in\nelab \"p24_kernel_decide_raw\" : tactic => withoutRecover do\n  closeMainGoalUsing `p24_kernel_decide_raw fun expectedType _ => do\n    let mut expectedType ← instantiateMVars expectedType\n    if expectedType.hasFVar then\n      expectedType ← zetaReduce expectedType\n    if expectedType.hasMVar || expectedType.hasFVar then\n      throwError \"p24_kernel_decide_raw requires a closed proposition\"\n    let pf ← mkDecideProof expectedType\n    let env ← getEnv\n    if env.hasUnsafe expectedType || env.hasUnsafe pf then\n      throwError \"p24_kernel_decide_raw requires a safe proposition and proof\"\n    let levelsInType := (collectLevelParams {} expectedType).params\n    let lemmaLevels :=\n      (← Term.getLevelNames).reverse.filter levelsInType.contains\n    let saved ← Tactic.saveState\n    tryCatchRuntimeEx\n      (do\n        let lemmaName ← withOptions (Elab.async.set · false) do\n          mkAuxLemma lemmaLevels expectedType pf\n        return mkConst lemmaName (lemmaLevels.map .param))\n      (fun ex => do\n        saved.restore\n        throw ex)\n\n"
diagnostic_source=candidate.decode().replace("import Std.Data.TreeMap.Raw.WF\n","import Std.Data.TreeMap.Raw.WF\nimport Lean.Elab.Tactic.Decide\n")
assert diagnostic_source.count("  decide +kernel")==1
diagnostic_source=diagnostic_source.replace("/-!\n",raw_tactic+"/-!\n",1).replace("  decide +kernel","  p24_kernel_decide_raw")
lines=diagnostic_source.splitlines(keepends=True)
markers={}
def marker(label):
    return ('#eval IO.FS.withFile "'+str(markerlog)+'" .append fun h => do\n'
            '  h.putStrLn "'+label+'"\n'
            '  h.flush\n\n')
for i,line in enumerate(lines):
    m=re.match(r"^(?:private )?(?:noncomputable )?(?:def|abbrev|theorem)\s+([A-Za-z0-9_.]+)",line)
    if not m:continue
    point=i
    j=i-1
    while j>=0 and not lines[j].strip():j-=1
    if j>=0 and lines[j].rstrip().endswith("-/"):
        while j>=0 and "/-" not in lines[j]:j-=1
        assert j>=0
        point=j
    j=point-1
    while j>=0 and not lines[j].strip():j-=1
    while j>=0 and re.match(r"^set_option .* in\s*$",lines[j]):
        point=j;j-=1
        while j>=0 and not lines[j].strip():j-=1
    markers.setdefault(point,[]).append(marker("P24_BEFORE_"+m.group(1)))
instrumented="".join("".join(markers.get(i,[]))+line for i,line in enumerate(lines))
restored=instrumented
for blocks in markers.values():
    for entry in blocks:restored=restored.replace(entry,"")
assert restored==diagnostic_source
instrumented+="\n"+marker("P24_AFTER_ALL_DECLARATIONS")
probe=out/"Probe.lean"
probe.write_bytes(instrumented.encode())
sys.path.insert(0,str(root/"verification/part2"))
from winner9_external_snapshot import ExternalSnapshot
lean="/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean"
external=ExternalSnapshot(Path("/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/qualifications/attempt-003/EXTERNAL_SNAPSHOT.json"),lean=lean,mathlib_pin="e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",project_lib=root/".lake/p2-private/lib")
env=external.environment(dict(os.environ))
native_before=external.verify()
registry=root/".lake/p2-private/records.json"
obj=root/".lake/p2-private/lib/ImbalancedChen/P2OriginalCompactArchivedTotalCandidate.olean"
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file() else None
before={"source":digest(source),"registry":digest(registry),"canonical_object":digest(obj)}
flags=["-t0","-j1","-M11264","-DwarningAsError=true","-DmaxRecDepth=50000","-DmaxHeartbeats=40000000","-DElab.async=false"]
smoke=out/"Smoke.lean"
smoke.write_bytes(base64.b64decode("aW1wb3J0IExlYW4uRWxhYi5UYWN0aWMuRGVjaWRlCgpvcGVuIExlYW4gTWV0YSBFbGFiIFRhY3RpYyBpbgplbGFiICJwMjRfa2VybmVsX2RlY2lkZV9yYXciIDogdGFjdGljID0+IHdpdGhvdXRSZWNvdmVyIGRvCiAgY2xvc2VNYWluR29hbFVzaW5nIGBwMjRfa2VybmVsX2RlY2lkZV9yYXcgZnVuIGV4cGVjdGVkVHlwZSBfID0+IGRvCiAgICBsZXQgbXV0IGV4cGVjdGVkVHlwZSDihpAgaW5zdGFudGlhdGVNVmFycyBleHBlY3RlZFR5cGUKICAgIGlmIGV4cGVjdGVkVHlwZS5oYXNGVmFyIHRoZW4KICAgICAgZXhwZWN0ZWRUeXBlIOKGkCB6ZXRhUmVkdWNlIGV4cGVjdGVkVHlwZQogICAgaWYgZXhwZWN0ZWRUeXBlLmhhc01WYXIgfHwgZXhwZWN0ZWRUeXBlLmhhc0ZWYXIgdGhlbgogICAgICB0aHJvd0Vycm9yICJwMjRfa2VybmVsX2RlY2lkZV9yYXcgcmVxdWlyZXMgYSBjbG9zZWQgcHJvcG9zaXRpb24iCiAgICBsZXQgcGYg4oaQIG1rRGVjaWRlUHJvb2YgZXhwZWN0ZWRUeXBlCiAgICBsZXQgZW52IOKGkCBnZXRFbnYKICAgIGlmIGVudi5oYXNVbnNhZmUgZXhwZWN0ZWRUeXBlIHx8IGVudi5oYXNVbnNhZmUgcGYgdGhlbgogICAgICB0aHJvd0Vycm9yICJwMjRfa2VybmVsX2RlY2lkZV9yYXcgcmVxdWlyZXMgYSBzYWZlIHByb3Bvc2l0aW9uIGFuZCBwcm9vZiIKICAgIGxldCBsZXZlbHNJblR5cGUgOj0gKGNvbGxlY3RMZXZlbFBhcmFtcyB7fSBleHBlY3RlZFR5cGUpLnBhcmFtcwogICAgbGV0IGxlbW1hTGV2ZWxzIDo9CiAgICAgICjihpAgVGVybS5nZXRMZXZlbE5hbWVzKS5yZXZlcnNlLmZpbHRlciBsZXZlbHNJblR5cGUuY29udGFpbnMKICAgIGxldCBzYXZlZCDihpAgVGFjdGljLnNhdmVTdGF0ZQogICAgdHJ5Q2F0Y2hSdW50aW1lRXgKICAgICAgKGRvCiAgICAgICAgbGV0IGxlbW1hTmFtZSDihpAgd2l0aE9wdGlvbnMgKEVsYWIuYXN5bmMuc2V0IMK3IGZhbHNlKSBkbwogICAgICAgICAgbWtBdXhMZW1tYSBsZW1tYUxldmVscyBleHBlY3RlZFR5cGUgcGYKICAgICAgICByZXR1cm4gbWtDb25zdCBsZW1tYU5hbWUgKGxlbW1hTGV2ZWxzLm1hcCAucGFyYW0pKQogICAgICAoZnVuIGV4ID0+IGRvCiAgICAgICAgc2F2ZWQucmVzdG9yZQogICAgICAgIHRocm93IGV4KQoKdGhlb3JlbSBwMjRfcmF3X2tlcm5lbF9zbW9rZSA6ICgxNyA6IE5hdCkgKiAyMyArIDYgPSAzOTcgOj0gYnkKICBwMjRfa2VybmVsX2RlY2lkZV9yYXcKCiNwcmludCBheGlvbXMgcDI0X3Jhd19rZXJuZWxfc21va2UK"))
assert digest(smoke)=="df56fea377ce6dbb6e164a4bd1edfa0d6df2e82b53902f99ae90ff046fe8b529"
smoke_command=[lean,*flags,"-o",str(out/"Smoke.olean"),str(smoke)]
smoke_run=subprocess.run(smoke_command,env=env,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
(out/"smoke.log").write_bytes(smoke_run.stdout)
sys.stdout.buffer.write(smoke_run.stdout);sys.stdout.buffer.flush()
print(json.dumps({"diagnostic_smoke_exit_code":smoke_run.returncode,"smoke_sha256":digest(smoke)}),flush=True)
assert smoke_run.returncode==0
cmd=[lean,*flags,"-o",str(out/"Probe.olean"),str(probe)]
print(json.dumps({"diagnostic_only":True,"all_credit":False,"source_pin":pin,"before":before,"candidate_sha256":hashlib.sha256(candidate).hexdigest(),"probe_sha256":digest(probe),"child_timeout":300,"flags":flags}),flush=True)
log=out/"probe.log"
start=time.monotonic()
pos=0
mpos=0
timed_out=False
with log.open("wb") as stream:
    proc=subprocess.Popen(cmd,env=env,stdout=stream,stderr=subprocess.STDOUT)
    while True:
        try:
            rc=proc.wait(timeout=10)
            finished=True
        except subprocess.TimeoutExpired:
            finished=False
        raw=log.read_bytes()
        if len(raw)>pos:
            sys.stdout.buffer.write(raw[pos:]);sys.stdout.buffer.flush();pos=len(raw)
        if markerlog.is_file():
            raw=markerlog.read_bytes()
            if len(raw)>mpos:
                sys.stdout.buffer.write(raw[mpos:]);sys.stdout.buffer.flush();mpos=len(raw)
        if finished:break
        if time.monotonic()-start>=300:
            timed_out=True;proc.kill();rc=proc.wait()
            raw=log.read_bytes()
            if len(raw)>pos:sys.stdout.buffer.write(raw[pos:]);sys.stdout.buffer.flush()
            break
child_seconds=time.monotonic()-start
after={"source":digest(source),"registry":digest(registry),"canonical_object":digest(obj)}
assert before==after
native_after=external.verify()
assert native_before==native_after
result={"diagnostic_only":True,"compile_credit":False,"kernel_credit":False,"acceptance_credit":False,"source_pin":pin,"exit_code":rc,"timed_out":timed_out,"child_elapsed_seconds":child_seconds,"before":before,"after":after,"native_binding_equal":True,"log_sha256":digest(log),"markers_sha256":digest(markerlog),"candidate_sha256":hashlib.sha256(candidate).hexdigest(),"probe_sha256":digest(probe),"flags":flags}
(out/"diagnostic.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps(result),flush=True)
PY
