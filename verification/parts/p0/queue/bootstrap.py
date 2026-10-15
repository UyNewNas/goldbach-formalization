#!/usr/bin/env python3
"""Fresh exact-pin source checkout plus only the selected official Mathlib cache.
Does not build the project root or any Goldbach theorem. P0 owns all execution.
"""
from pathlib import Path
import datetime, fcntl, hashlib, json, os, re, signal, subprocess, sys, time
ROOT=Path(__file__).resolve().parents[4]
sys.path.insert(0,str(ROOT))
from verification.verify_variable_envelope_boxes import lean_code

def sha(p):
    with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
    out=ROOT/'.lake/p0-queue/bootstrap';out.mkdir(parents=True,exist_ok=False)
    report={'status':'RUNNING','started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'mode':'FRESH_PINNED_TARGET_CLOSURE','full_root_build':False,'stages':[],'manifest_sha256':sha(ROOT/'lake-manifest.json'),'script_sha256':sha(Path(__file__))}
    def save(): (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    save(); lock_path=os.environ['CHEN_HEAVY_LOCK_PATH'];lock_fd=os.open(lock_path,os.O_CREAT|os.O_WRONLY,0o600);fcntl.flock(lock_fd,fcntl.LOCK_EX|fcntl.LOCK_NB)
    env=os.environ.copy();env['LEAN_NUM_THREADS']='2';env.pop('LEAN_PATH',None);env.pop('LEAN_SRC_PATH',None)
    proc=None
    def stop(sig,frame):
        if proc is not None and proc.poll() is None:
            os.killpg(proc.pid,signal.SIGTERM)
            try:proc.wait(timeout=10)
            except subprocess.TimeoutExpired:os.killpg(proc.pid,signal.SIGKILL);proc.wait()
        raise RuntimeError('Interrupted '+str(sig))
    signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    def run(command,label,cwd=ROOT,timeout=1200):
        nonlocal proc
        start=time.monotonic();log=out/(label+'.log')
        with log.open('wb') as f:
            proc=subprocess.Popen(command,cwd=cwd,env=env,stdout=f,stderr=subprocess.STDOUT,pass_fds=(lock_fd,),start_new_session=True)
            report['active_child']={'pid':proc.pid,'command':command,'label':label};save()
            try:code=proc.wait(timeout=timeout)
            except subprocess.TimeoutExpired:stop(signal.SIGTERM,None)
        record={'label':label,'command':command,'exit_code':code,'seconds':round(time.monotonic()-start,3),'sha256':sha(log)};report['stages'].append(record);report.pop('active_child',None);save();print(json.dumps(record),flush=True)
        if code:raise RuntimeError(label+' failed: '+str(code))
    try:
        packages=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
        report['pins']={p['name']:p['rev'] for p in packages};save()
        for p in packages:
            target=ROOT/'.lake/packages'/p['name']
            if target.exists():raise RuntimeError('Refusing unrecorded existing package '+str(target))
            target.mkdir(parents=True)
            run(['git','init'],p['name']+'-init',target,60)
            run(['git','remote','add','origin',p['url']],p['name']+'-remote',target,60)
            run(['git','fetch','--depth','1','origin',p['rev']],p['name']+'-fetch',target,600)
            run(['git','checkout','--detach','FETCH_HEAD'],p['name']+'-checkout',target,120)
            assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=target,text=True).strip()==p['rev']
        run([sys.executable,'verification/parts/p0/check_pins.py'],'pins-before',timeout=60)
        reallean=Path(subprocess.check_output(['elan','which','lean'],text=True).strip());realroot=reallean.parent.parent
        shadow=out/'toolchain';shadow.mkdir();(shadow/'bin').mkdir()
        for p in realroot.iterdir():
            if p.name!='bin':(shadow/p.name).symlink_to(p,target_is_directory=p.is_dir())
        for p in (realroot/'bin').iterdir():
            if p.name!='lean':(shadow/'bin'/p.name).symlink_to(p,target_is_directory=p.is_dir())
        wrapper=shadow/'bin/lean'
        wrapper.write_text('''#!/usr/bin/env python3
import fcntl,json,os,sys,time
args=[]; skip=False
for a in sys.argv[1:]:
    if skip:skip=False;continue
    if a in ['-j','-M']:skip=True;continue
    if a.startswith('-j') or a.startswith('-M'):continue
    args.append(a)
fd=os.open(os.environ['P0_COMPILER_SLOT'],os.O_CREAT|os.O_WRONLY,0o600)
fcntl.flock(fd,fcntl.LOCK_EX);os.set_inheritable(fd,True)
cmd=[os.environ['P0_REAL_LEAN'],'-t0','-j2','-M4096',*args]
with open(os.environ['P0_COMPILER_LOG'],'a') as f:f.write(json.dumps({'pid':os.getpid(),'command':cmd})+'\\n')
os.execv(cmd[0],cmd)
''');wrapper.chmod(0o755)
        env.update(LEAN_SYSROOT=str(shadow),LAKE_OVERRIDE_LEAN='true',LAKE_NO_CACHE='true',LAKE_ARTIFACT_CACHE='false',P0_REAL_LEAN=str(reallean),P0_COMPILER_SLOT=str(out/'compiler.lock'),P0_COMPILER_LOG=str(out/'compiler-commands.jsonl'))
        env['PATH']=str(shadow/'bin')+':'+env['PATH']
        report['runtime_sha256']={str(reallean):sha(reallean),str(realroot/'bin/lake'):sha(realroot/'bin/lake'),str(wrapper):sha(wrapper)}
        roots=[ROOT]+[ROOT/'.lake/packages'/p['name'] for p in packages]
        todo=[m for r in json.loads((ROOT/'automation/dispatch.json').read_text())['requests'] for m in r['modules']]+['Lean.Util.CollectAxioms']; seen={}; mathlib=set()
        while todo:
            module=todo.pop()
            if module in seen:continue
            rel=Path(module.replace('.','/')+'.lean'); found=next((p/rel for p in roots if (p/rel).is_file()),None)
            if found is None:continue  # Official bundled Lean/Lake source boundary.
            seen[module]={'path':str(found.relative_to(ROOT)),'sha256':sha(found)}
            if str(found).startswith(str(ROOT/'.lake/packages/mathlib/Mathlib')):
                mathlib.add(module);continue  # Official cache computes its exact transitive closure.
            for line in lean_code(found.read_text()).splitlines():
                if re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+',line):
                    todo += re.sub(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?','',line).split()
        assert mathlib,'No Mathlib target boundary found'
        report['target_source_walk']=seen;report['mathlib_cache_roots']=sorted(mathlib);save()
        run([str(realroot/'bin/lake'),'--no-cache','exe','cache','get',*sorted(mathlib)],'official-mathlib-cache',timeout=1800)
        run([sys.executable,'verification/parts/p0/check_pins.py'],'pins-after',timeout=60)
        assert sha(ROOT/'lake-manifest.json')==report['manifest_sha256'],'Manifest changed'
        assert sha(Path(__file__))==report['script_sha256'],'Bootstrap changed'
        assert all(sha(ROOT/v['path'])==v['sha256'] for v in seen.values()),'Source changed'
        report['status']='PASS_OFFICIAL_CACHE_ONLY';report['goldbach_or_project_proof_compiled']=False
    except BaseException as e:report.update(status='FAILED',failure=str(e));print(str(e),file=sys.stderr)
    finally:report['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();save()
    return 0 if report['status']=='PASS_OFFICIAL_CACHE_ONLY' else 1
if __name__=='__main__':sys.exit(main())
