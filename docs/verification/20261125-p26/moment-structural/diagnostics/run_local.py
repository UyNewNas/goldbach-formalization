from pathlib import Path
import json,subprocess,os,time,resource,hashlib,sys

root=Path('/workspace/p26-local-checks/moment-structural')
module=sys.argv[1]
timeout=int(sys.argv[2]) if len(sys.argv)>2 else 60
source=root/(module+'.lean')
sha=hashlib.sha256(source.read_bytes()).hexdigest()
run=root/'runs'/module/sha
run.mkdir(parents=True,exist_ok=True)
(run/source.name).write_bytes(source.read_bytes())
lean=Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux/bin/lean')
pkg=Path('/workspace/library-files/p34-proof-work/.lake/packages')
env=os.environ.copy()
env['LEAN_PATH']=':'.join([str(root)]+[str(p) for p in sorted(pkg.glob('*/.lake/build/lib/lean'))])
cmd=[str(lean),'-j1','-M4096','-o',module+'.olean',module+'.lean']
start=time.monotonic()
timed_out=False
with (run/'normal.log').open('w') as log:
    try:
        result=subprocess.run(cmd,cwd=root,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=timeout)
        code=result.returncode
    except subprocess.TimeoutExpired:
        timed_out=True
        code=124
meta={'status':'LOCAL_DIAGNOSTIC_ONLY_NO_PRODUCTION_ACCEPTANCE','command':cmd,'source_sha256':sha,'exit_code':code,'timed_out':timed_out,'seconds':time.monotonic()-start,'peak_child_rss_kib':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'log_sha256':hashlib.sha256((run/'normal.log').read_bytes()).hexdigest(),'lean_commit':'62eed1db4d67327ec8120be05f1a1b0847d74561','mathlib_commit':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','LEAN_PATH':env['LEAN_PATH'],'directory':str(run),'timeout_seconds':timeout,'added_global_or_tactic_budgets':[]}
(run/'RESULT.json').write_text(json.dumps(meta,indent=2)+'\n')
print(json.dumps(meta,indent=2))
print((run/'normal.log').read_text())
raise SystemExit(code)
