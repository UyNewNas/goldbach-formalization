from pathlib import Path
import hashlib, json, os, signal, subprocess, sys, time
import psutil

ROOT = Path(__file__).resolve().parent
TOOLCHAIN = Path('/workspace/library-files/p34-runtime/lean-4.33.0-rc1-linux')
BASE_LIB = Path('/workspace/p26-recovery-candidates/archive-char-input/local/lib/lean')
MANIFEST = json.loads((ROOT/'MANIFEST.json').read_text())
STAGES = {
    'data': 'ImbalancedChen.P2OriginalSaving19CharacterCore00',
    'length': 'ImbalancedChen.P2OriginalSaving19CharacterLength00',
    'parse': 'ImbalancedChen.P2OriginalSaving19CharacterParse00',
}
MODE, STAGE = sys.argv[1:]
assert MODE in {'normal','kernel'} and STAGE in STAGES
assert not (MODE == 'kernel' and STAGE == 'data'), 'This stage is normal-only by task scope.'
MODULE = STAGES[STAGE]
SOURCE = ROOT/(MODULE.replace('.','/')+'.lean')
OBJECT = ROOT/'objects'/(MODULE.replace('.','/')+'.olean')
PHASE = MODE+'-'+STAGE
LOG = ROOT/'logs'/(PHASE+'.log')
RESULT = ROOT/'logs'/(PHASE+'-result.json')
COMMAND = ROOT/'logs'/(PHASE+'-command.json')
LIMIT = 4*1024*1024*1024
WALL_LIMIT = 180

def fingerprint(p):
    b=p.read_bytes()
    return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}

def invariant_fingerprints():
    records=[]
    for original in [MANIFEST['fixture']]+MANIFEST['reused_objects']:
        got=fingerprint(Path(original['path']))
        assert got['bytes']==original['bytes'] and got['sha256']==original['sha256'], got
        records.append(got)
    return records

def require_completed(mode,stage):
    path=ROOT/'logs'/(mode+'-'+stage+'-result.json')
    row=json.loads(path.read_text())
    assert row['status']=='succeeded' and row['exit_code']==0, row
    assert fingerprint(Path(row['object']['path']))==row['object'], 'Dependency object changed.'
    return row

assert not COMMAND.exists() and not RESULT.exists(), 'One attempt per stage: refusing replay.'
for p in (ROOT/'logs').glob('*-result.json'):
    assert json.loads(p.read_text())['status']=='succeeded', 'Previous failure requires stop.'
if MODE=='normal':
    assert not OBJECT.exists(), 'Refusing to overwrite an existing object.'
    if STAGE=='length': require_completed('normal','data')
    if STAGE=='parse': require_completed('kernel','length')
else:
    require_completed('normal',STAGE)
expected=next(r for r in MANIFEST['files'] if r['module']==MODULE)
source_info=fingerprint(SOURCE)
assert source_info['sha256']==expected['sha256'] and source_info['bytes']==expected['bytes']
before=invariant_fingerprints()
OBJECT.parent.mkdir(parents=True,exist_ok=True)
if MODE=='normal':
    argv=[str(TOOLCHAIN/'bin/lean'),'-j1','-DmaxRecDepth=1000000','-DmaxHeartbeats=0','-o',str(OBJECT),str(SOURCE)]
else:
    argv=[str(TOOLCHAIN/'bin/leanchecker'),'--verbose',MODULE]
env=os.environ.copy()
env['PATH']=str(TOOLCHAIN/'bin')+os.pathsep+env.get('PATH','')
env['LEAN_PATH']=str(ROOT/'objects')+os.pathsep+str(BASE_LIB)
env['LEAN_NUM_THREADS']='1';env['OMP_NUM_THREADS']='1'
record={'mode':MODE,'stage':STAGE,'module':MODULE,'argv':argv,'cwd':str(ROOT),
        'source':source_info,'LEAN_PATH':env['LEAN_PATH'],'rss_limit_bytes':LIMIT,
        'wall_seconds':WALL_LIMIT,'rss_sample_seconds':0.02,'started_unix':time.time(),
        'invariants_before':before,'object':None,'old_Core_equivalence_claimed':False,
        'production_modified':False,'remote_jobs_submitted':False}
COMMAND.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
start=time.monotonic();peak=0;cpu_peak=0.;reason=None
with LOG.open('w') as out:
    proc=subprocess.Popen(argv,cwd=ROOT,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
    process=psutil.Process(proc.pid)
    while True:
        rc=proc.poll();rss=0
        try:
            processes=[process]+process.children(recursive=True)
            rss=sum(q.memory_info().rss for q in processes if q.is_running())
            cpu=sum(q.cpu_times().user+q.cpu_times().system for q in processes if q.is_running())
            peak=max(peak,rss);cpu_peak=max(cpu_peak,cpu)
        except (psutil.NoSuchProcess,psutil.AccessDenied):
            pass
        elapsed=time.monotonic()-start
        if rc is not None: break
        if rss>LIMIT: reason='memory_limit'
        elif elapsed>WALL_LIMIT: reason='timeout'
        if reason:
            os.killpg(proc.pid,signal.SIGKILL)
            break
        time.sleep(0.02)
    rc=proc.wait()
record.update({'exit_code':rc,'status':reason or ('succeeded' if rc==0 else 'failed'),
               'elapsed_seconds':time.monotonic()-start,'peak_rss_bytes':peak,
               'sampled_cpu_seconds':cpu_peak,'log':fingerprint(LOG),
               'object':fingerprint(OBJECT) if OBJECT.exists() else None,
               'invariants_after':invariant_fingerprints()})
RESULT.write_text(json.dumps(record,indent=2)+'\n')
print(LOG.read_text(),end='',flush=True)
print(json.dumps(record),flush=True)
sys.exit(0 if record['status']=='succeeded' else 1)
