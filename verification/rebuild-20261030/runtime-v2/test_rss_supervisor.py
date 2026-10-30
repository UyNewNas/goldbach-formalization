import json,sys,time
from pathlib import Path
from rss_supervisor import supervise
P=sys.executable
cases={
 'normal':('import time;print("normal");time.sleep(.08)','completed',64,3),
 'timeout':('import time;time.sleep(10)','timeout',64,.3),
 'child_grandchild_memory':('import subprocess,sys,time;subprocess.Popen([sys.executable,"-c",'+repr('import subprocess,sys,time;subprocess.Popen([sys.executable,"-c","import time;x=bytearray(80*1024**2);time.sleep(10)"]);time.sleep(10)')+']);time.sleep(10)','memory_limit',64,3),
 'aggregate_children_memory':('import subprocess,sys,time;[subprocess.Popen([sys.executable,"-c","import time;x=bytearray(25*1024**2);time.sleep(10)"]) for _ in range(3)];time.sleep(10)','memory_limit',64,3),
 'setsid_memory':('import subprocess,sys,time;subprocess.Popen([sys.executable,"-c","import time;x=bytearray(80*1024**2);time.sleep(10)"],start_new_session=True);time.sleep(10)','memory_limit',64,3),
 'orphan_setsid_timeout':('import subprocess,sys;subprocess.Popen([sys.executable,"-c","import time;time.sleep(10)"],start_new_session=True)','timeout',64,.3),
}
results={}
for name,(code,reason,mb,seconds) in cases.items():
 r=supervise([P,'-c',code],memory_bytes=mb*1024**2,timeout_seconds=seconds,poll_seconds=.02)
 assert r['reason']==reason and r['termination_verified'],(name,r)
 results[name]=r
 print(name,r['reason'],'peak',r['peak_rss_bytes'],'processes',len(r['observed_processes']),flush=True)
r=supervise([P,'-c','import time;time.sleep(10)'],memory_bytes=64*1024**2,timeout_seconds=3,batch_deadline=time.monotonic()+.2,poll_seconds=.02)
assert r['reason']=='timeout' and r['termination_verified'];results['batch_deadline']=r
r=supervise([P,'-c','raise SystemExit(7)'],memory_bytes=64*1024**2,timeout_seconds=3)
assert r['reason']=='completed' and r['exit_code']==7 and r['termination_verified'];results['nonzero_exit']=r
r=supervise([P,'-c','raise RuntimeError("must not run")'],memory_bytes=64*1024**2,timeout_seconds=3,batch_deadline=time.monotonic()-1)
assert not r['launched'] and r['reason']=='timeout';results['expired_batch_no_launch']=r
Path(__file__).with_name('rss-supervisor-test-results.json').write_text(json.dumps(results,indent=2)+'\n')
