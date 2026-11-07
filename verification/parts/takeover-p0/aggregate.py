"""Run the unchanged root-import aggregate with pinned Lake and bounded Lean jobs."""
from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, sys, time
from runtime import ROOT, STATE, BIN, environment

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

native = Path('/home/slava/codex-lean-ve/integration-build')
old = Path('/home/slava/codex-lean-ve/project-build')
marker = STATE / 'aggregate-cache-copy.json'
if not marker.exists():
    if native.exists(): raise RuntimeError('Unrecorded preexisting native integration cache')
    shutil.copytree(old, native)
    marker.write_text(json.dumps({'source':str(old),'destination':str(native),
        'role':'untrusted prior Lake cache; lake --rehash will validate every consumed trace',
        'files':len([p for p in native.rglob('*') if p.is_file()])},indent=2)+'\n')
build = ROOT / '.lake/build'
if not build.exists(): build.symlink_to(native, target_is_directory=True)
elif build.resolve() != native: raise RuntimeError('Unexpected aggregate build directory')
shadow = STATE / 'toolchain'
shadow.mkdir(exist_ok=True)
for child in BIN.parent.iterdir():
    if child.name == 'bin': continue
    target=shadow/child.name
    if not target.exists(): target.symlink_to(child,target_is_directory=child.is_dir())
(shadow/'bin').mkdir(exist_ok=True)
for child in BIN.iterdir():
    if child.name == 'lean': continue
    target=shadow/'bin'/child.name
    if not target.exists(): target.symlink_to(child,target_is_directory=child.is_dir())
wrapper=shadow/'bin/lean'
wrapper.write_text('''#!/usr/bin/python3
import os,sys,fcntl
from pathlib import Path
sys.path.insert(0, '''+repr(str(ROOT/'verification/parts/takeover-p0'))+''')
from runtime import acquire_slot,LOCKS,ROOT,PROVIDERS,BIN
source=next((Path(a) for a in sys.argv[1:] if a.endswith('.lean') and Path(a).is_file()),None)
locks=[]
if source is not None:
    source=source.resolve()
    bases=[ROOT,*[p for p in PROVIDERS.iterdir() if p.is_dir()]]
    for base in bases:
        try: module='.'.join(source.relative_to(base).with_suffix('').parts)
        except ValueError: continue
        lock=(LOCKS/(module+'.lock')).open('a+');fcntl.flock(lock,fcntl.LOCK_EX);locks.append(lock);break
    locks.append(acquire_slot())
for lock in locks: os.set_inheritable(lock.fileno(),True)
real=BIN/'lean'
os.execv(str(real),[str(real),*sys.argv[1:]])
''')
wrapper.chmod(0o755)
env=environment();env.pop('LEAN_PATH',None)
env['LEAN_SYSROOT']=str(shadow);env['LAKE_OVERRIDE_LEAN']='true'
env['PATH']=str(shadow/'bin')+':'+env['PATH']
stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
out=STATE/'aggregate-runs'/stamp;out.mkdir(parents=True)
command=[str(BIN/'lake'),'--rehash','--no-cache','build','+ImbalancedChen']
inputs={str(p.relative_to(ROOT)):sha(p) for p in [ROOT/'ImbalancedChen.lean',ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json']}
record={'status':'RUNNING','command':command,'runner_pid':os.getpid(),'input_sha256':inputs,
    'scope':'normal pinned Lake root-import aggregate; explicit +ImbalancedChen excludes unimported development leaves',
    'cache_policy':'old copied objects/traces are input cache only, checked by Lake --rehash',
    'concurrency':'same two global Lean slots and module locks as direct runner'}
started=time.monotonic()
with (out/'stdout.log').open('wb') as stream:
    proc=subprocess.Popen(command,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
    record['child_pid']=proc.pid;(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':'RUNNING','pid':proc.pid,'output':str(out)}),flush=True)
    code=proc.wait()
record.update(exit_code=code,seconds=round(time.monotonic()-started,3),input_sha256_after={name:sha(ROOT/name) for name in inputs})
record['status']='PASS' if code==0 and record['input_sha256_after']==inputs else 'FAILED'
(out/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
if code: print((out/'stdout.log').read_text()[-18000:])
sys.exit(0 if record['status']=='PASS' else 1)
