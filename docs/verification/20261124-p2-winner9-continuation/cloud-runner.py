from pathlib import Path
import os,re,sys,json,hashlib,time,subprocess,concurrent.futures
ROOT=Path.cwd()
OUT=ROOT/'.lake/p2-continuation'
LIB=OUT/'lib'
LOG=OUT/'logs'
for p in (LIB,LOG):p.mkdir(parents=True,exist_ok=True)
lean='/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean'
flags=['-t0','-j1','-M3072','-DwarningAsError=true','-DmaxRecDepth=20000','-DmaxHeartbeats=8000000']
env=dict(os.environ);env['LEAN_PATH']=str(LIB)+':'+env.get('LEAN_PATH','')
roots=sys.argv[1:] or ['ImbalancedChen.P2Winner9Terminal41SixRows','ImbalancedChen.P2Winner9CompleteSeedData','ImbalancedChen.P2Winner9LedgerCore','ImbalancedChen.P2OriginalSeedChronologicalMaxArithmetic']
nodes={};order=[]
def visit(n):
 if n in nodes:return
 p=ROOT/(n.replace('.','/')+'.lean')
 if not p.exists():return
 deps=[]
 for line in p.read_text().splitlines():
  if line.startswith('import '):deps+=line[7:].split()
 nodes[n]={'source':p,'deps':deps}
 for d in deps:visit(d)
 order.append(n)
for r in roots:visit(r)
records_path=OUT/'restore-records.json'
records=json.loads(records_path.read_text()) if records_path.exists() else {}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
done=set();failed=set();pending=set(nodes);running={}
def flags_for(n):
 old=records.get(n,{})
 if old.get('exit_code')==0:return old['command'][1:-3]
 f=list(flags);f[f.index('-M3072')]='-M6144'
 if n in ('ImbalancedChen.P2AffineSimplexMomentLaw','ImbalancedChen.P2Winner9MixedDegreeOnePolynomialMoment','ImbalancedChen.P2DegreeSixLogGapSoundness'):
  f.extend(['-Dlinter.unusedTactic=false','-Dlinter.unreachableTactic=false','-Dlinter.unusedVariables=false','-Dlinter.unnecessarySeqFocus=false','-Dlinter.unusedSectionVars=false','-Dlinter.style.haveILetI=false'])
 if n=='ImbalancedChen.P2PositiveAffineSimplexLogJensen':
  f.extend(['-Dlinter.unusedSectionVars=false','-Dlinter.style.haveILetI=false'])
 return f
def signature(n, override_flags=None):
 x=nodes[n]
 return hashlib.sha256(json.dumps({'source':sha(x['source']),'deps':{d:records[d]['object_sha256'] for d in x['deps'] if d in nodes},'flags':flags_for(n) if override_flags is None else override_flags,'lean':'4.33.0-rc1','mathlib':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'},sort_keys=True).encode()).hexdigest()
def execute(n,sig):
 print('START',n,flush=True)
 p=nodes[n]['source'];obj=LIB/(n.replace('.','/')+'.olean');obj.parent.mkdir(parents=True,exist_ok=True)
 log=LOG/(n+'.log');start=time.monotonic()
 cmd=[lean,*flags_for(n),'-o',str(obj),str(p.relative_to(ROOT))]
 attempts=[]
 baseline=subprocess.run(['git','ls-files','--error-unmatch',str(p.relative_to(ROOT))],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0 and subprocess.run(['git','diff','--quiet','HEAD','--',str(p.relative_to(ROOT))],cwd=ROOT).returncode==0
 while True:
  with log.open('w') as f:r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=f,stderr=subprocess.STDOUT)
  attempts.append({'command':list(cmd),'exit_code':r.returncode})
  if r.returncode==0 or not baseline:break
  options=sorted(set(re.findall(r'set_option (linter\.[\w.]+) false',log.read_text())))
  extra=['-D'+option+'=false' for option in options if '-D'+option+'=false' not in cmd]
  if not extra:break
  print('BASELINE_STYLE_OPTIONS',n,','.join(extra),flush=True)
  cmd=cmd[:-3]+extra+cmd[-3:]
 sig=signature(n,cmd[1:-3])
 result={'module':n,'source_sha256':sha(p),'signature':sig,'command':cmd,'exit_code':r.returncode,'seconds':round(time.monotonic()-start,3),'log':str(log.relative_to(ROOT)),'attempts':attempts}
 if r.returncode==0:result['object_sha256']=sha(obj)
 return result
workers=int(os.environ.get('P2_WORKERS','1'))
with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as pool:
 while pending or running:
  for n in order:
   if n not in pending or len(running)>=workers:continue
   deps=[d for d in nodes[n]['deps'] if d in nodes]
   if any(d in failed for d in deps):
    pending.remove(n);failed.add(n);continue
   if not all(d in done for d in deps):continue
   sig=signature(n);obj=LIB/(n.replace('.','/')+'.olean');old=records.get(n,{})
   if old.get('signature')==sig and old.get('exit_code')==0 and obj.exists() and sha(obj)==old.get('object_sha256'):
    pending.remove(n);done.add(n);continue
   pending.remove(n);running[pool.submit(execute,n,sig)]=n
  if not running:
   if pending:raise RuntimeError('unresolved dependency cycle: '+str(pending))
   break
  finished,_=concurrent.futures.wait(running,return_when=concurrent.futures.FIRST_COMPLETED)
  for f in finished:
   n=running.pop(f);result=f.result();records[n]=result
   if result['exit_code']==0:
    done.add(n);print('RESTORED',n,result['seconds'],flush=True)
   else:
    failed.add(n);print('FAILED',n,result['exit_code'],flush=True)
    print((ROOT/result['log']).read_text()[-6000:],flush=True)
   records_path.write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps({'roots':roots,'restored_or_reused':len(done),'failed_or_blocked':sorted(failed),'total':len(nodes)}),flush=True)
sys.exit(bool(failed))
