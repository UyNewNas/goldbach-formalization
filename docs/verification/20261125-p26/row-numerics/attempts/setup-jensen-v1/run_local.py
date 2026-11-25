#!/usr/bin/env python3
"""Local bounded diagnostic, adapted from archive-schema/run_check.py.

Only the new owner and the explicitly authorized three absent setup suppliers
may be compiled. This is not the P1 strict all-owned acceptance engine.
"""
from pathlib import Path
import hashlib,json,os,signal,subprocess,sys,time
import psutil

ROOT=Path(__file__).resolve().parent
TOOLCHAIN=Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux')
MODE,MODULE,TAG=sys.argv[1:]
SETUP={
 'ImbalancedChen.P2PositiveAffineSimplexLogJensen',
 'ImbalancedChen.P2DegreeSixLogGapSoundness',
 'ImbalancedChen.P2OriginalLogMomentQ96Checker',
}
OWNER='ImbalancedChen.P2OriginalSaving19RowNumerics'
assert MODULE in SETUP|{OWNER}
assert MODE in {'normal','kernel'}
assert all(c.isalnum() or c in '._-' for c in TAG+MODULE)
IS_SETUP=MODULE in SETUP
PROJECT=ROOT/'local' if IS_SETUP else ROOT
SOURCE=PROJECT/(MODULE.replace('.','/')+'.lean')
OBJECT=PROJECT/'objects'/(MODULE.replace('.','/')+'.olean')
PHASE=MODE+'-'+TAG
LOG=ROOT/'logs'/(PHASE+'.log')
COMMAND=ROOT/'logs'/(PHASE+'-command.json')
RESULT=ROOT/'logs'/(PHASE+'-result.json')
LIMIT=4*1024*1024*1024;WALL=180
assert not COMMAND.exists() and not RESULT.exists(), 'Do not repeat an attempt under the same tag.'

def fp(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}

def frozen_inputs():
 files=list((ROOT/'local/ImbalancedChen').glob('*.lean'))
 files+=list((ROOT/'local/objects/ImbalancedChen').glob('*.olean'))
 files=[p for p in files if p.resolve()!=OBJECT.resolve()]
 return {str(p.relative_to(ROOT)):fp(p) for p in sorted(files)}

if MODE=='normal':
 assert not OBJECT.exists(), 'Never overwrite an existing successful object.'
 backup=ROOT/'attempts'/TAG/SOURCE.name
 backup.parent.mkdir(parents=True,exist_ok=True)
 assert not backup.exists()
 backup.write_bytes(SOURCE.read_bytes())
 argv=[str(TOOLCHAIN/'bin/lean'),'-j1','-DmaxRecDepth=1000000','-DmaxHeartbeats=0','-o',str(OBJECT),str(SOURCE)]
else:
 previous=json.loads((ROOT/'logs'/('normal-'+TAG+'-result.json')).read_text())
 assert previous['status']=='succeeded' and previous['exit_code']==0
 assert fp(SOURCE)==previous['source'] and fp(OBJECT)==previous['object']
 argv=[str(TOOLCHAIN/'bin/leanchecker'),'--verbose',MODULE]
OBJECT.parent.mkdir(parents=True,exist_ok=True)
env=os.environ.copy();env['PATH']=str(TOOLCHAIN/'bin')+os.pathsep+env.get('PATH','')
env['LEAN_PATH']=os.pathsep.join([str(ROOT/'objects'),str(ROOT/'local/objects')]+[str(p) for p in sorted(Path('/workspace/library-files/p34-proof-work/.lake/packages').glob('*/.lake/build/lib/lean'))]);env['LEAN_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1'
record={'mode':MODE,'module':MODULE,'tag':TAG,'argv':argv,'cwd':str(PROJECT),'source':fp(SOURCE),'LEAN_PATH':env['LEAN_PATH'],'rss_limit_bytes':LIMIT,'wall_limit_seconds':WALL,'rss_sample_seconds':0.02,'started_unix':time.time(),'inputs_before':frozen_inputs(),'production_modified':False,'actual_row_guard_claimed':False,'environment_setup_only':IS_SETUP,'new_formalization_credit':not IS_SETUP,'P1_strict_claimed':False,'remote_jobs_submitted':False}
COMMAND.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'phase':PHASE,'module':MODULE,'environment_setup_only':IS_SETUP}),flush=True)
start=time.monotonic();peak=0;cpu_peak=0.;reason=None
with LOG.open('w') as output:
 p=subprocess.Popen(argv,cwd=PROJECT,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
 proc=psutil.Process(p.pid)
 while True:
  rc=p.poll();rss=0
  try:
   ps=[proc]+proc.children(recursive=True)
   rss=sum(q.memory_info().rss for q in ps if q.is_running())
   cpu=sum(q.cpu_times().user+q.cpu_times().system for q in ps if q.is_running())
   peak=max(peak,rss);cpu_peak=max(cpu_peak,cpu)
  except (psutil.NoSuchProcess,psutil.AccessDenied):pass
  if rc is not None:break
  if rss>LIMIT:reason='memory_limit'
  elif time.monotonic()-start>WALL:reason='timeout'
  if reason:
   os.killpg(p.pid,signal.SIGKILL);break
  time.sleep(0.02)
 rc=p.wait()
record.update({'exit_code':rc,'status':reason or ('succeeded' if rc==0 else 'failed'),'elapsed_seconds':time.monotonic()-start,'peak_rss_bytes':peak,'sampled_cpu_seconds':cpu_peak,'log':fp(LOG),'object':fp(OBJECT) if OBJECT.exists() else None,'inputs_after':frozen_inputs()})
assert record['inputs_before']==record['inputs_after']
RESULT.write_text(json.dumps(record,indent=2)+'\n')
print(LOG.read_text(),end='',flush=True)
print(json.dumps({k:record[k] for k in ['module','status','exit_code','elapsed_seconds','peak_rss_bytes','object']}),flush=True)
sys.exit(0 if record['status']=='succeeded' else 1)
