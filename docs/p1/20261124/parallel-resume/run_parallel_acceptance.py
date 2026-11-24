#!/usr/bin/env python3
"""Reuse completed normal builds; run kernel and full-owned audits on two existing lanes."""
from pathlib import Path
import concurrent.futures,datetime,hashlib,json,re,subprocess,sys,time
P=Path('/workspace/blue-member-build')
R=Path('/workspace/p1-complete-proof/20261124-resume/batch1-parallel-acceptance')
B=Path('/workspace/p1-complete-proof/20261124-resume/batch1-normal')
STATES=[Path('/workspace/blue-build-tools/member-runtime-evidence/state.json'),Path('/workspace/blue-build-tools/runtime-evidence/state.json')]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def save(p,d):
 with p.open('x') as f:json.dump(d,f,ensure_ascii=False,indent=2)
def snap(m):
 rel=m.replace('.','/')
 paths=[rel+'.lean','.lake/build/lib/lean/'+rel+'.olean','.lake/build/lib/lean/'+rel+'.ilean','.lake/build/ir/'+rel+'.c','.lake/build/ir/'+rel+'.setup.json','.lake/build/lib/lean/'+rel+'.trace']
 assert all((P/s).is_file() for s in paths),m
 return {s:{'bytes':(P/s).stat().st_size,'sha256':sha(P/s)} for s in paths}
def run(L,name,args):
 rec={'argv':args,'cwd':str(P),'started_utc':now()};t=time.monotonic()
 with (L/(name+'.log')).open('x') as out:p=subprocess.run(args,cwd=P,stdout=out,stderr=subprocess.STDOUT)
 rec.update(exit_code=p.returncode,elapsed_seconds=time.monotonic()-t,finished_utc=now(),log=name+'.log',log_sha256=sha(L/(name+'.log')))
 save(L/(name+'-command.json'),rec)
 print(json.dumps({'lane':L.name,'stage':name,'exit_code':p.returncode,'seconds':rec['elapsed_seconds']}),flush=True)
 if p.returncode:raise RuntimeError((L.name,name,p.returncode))
 return rec
def lane(i):
 L=R/f'lane-{i}';modules=json.loads((L/'MODULES.json').read_text());state=STATES[i]
 G=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(state)]
 baseline={m:snap(m) for m in modules};save(L/'BEFORE_KERNEL.json',baseline)
 readiness=run(L,'stock-readiness-before',G+['lake','--no-build','build']+['+'+m+':olean' for m in modules])
 kernels={}
 for m in modules:
  kernels[m]=run(L,m.split('.')[-1]+'-kernel',G+['lake','env','leanchecker','--verbose',m])
  assert snap(m)==baseline[m],('changed_during_kernel',m)
 template=(Path('/workspace/p1-complete-proof/20261124-resume/accepted-batch102-two')/'PublicAudit.lean').read_text()
 template=re.sub(r'^import ImbalancedChen\.[^\n]+\n','',template,flags=re.M)
 template=''.join('import '+m+'\n' for m in modules)+template
 template=re.sub(r'let modules := #\[[^\n]*\]', 'let modules := #['+', '.join('`'+m for m in modules)+']',template,count=1)
 with (L/'PublicAudit.lean').open('x') as out:out.write(template)
 audit=run(L,'all-owned-types-axioms',G+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--root='+str(L),str(L/'PublicAudit.lean')])
 text=(L/'all-owned-types-axioms.log').read_text()
 records=[json.loads(s) for s in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',text)]
 inventory=[json.loads(s)['names'] for s in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})',text)]
 names=[x['name'] for x in records];assert len(inventory)==1 and sorted(names)==sorted(inventory[0])
 assert len(set(names))==len(names) and {x['module'] for x in records}==set(modules)
 assert all(x['kind']!='axiom' and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in records)
 assert not any(s in text for s in ['sorryAx','…','⋯','...'])
 save(L/'OWNED_EXPORTS.json',records)
 after=run(L,'stock-readiness-after',G+['lake','--no-build','build']+['+'+m+':olean' for m in modules])
 assert {m:snap(m) for m in modules}==baseline
 normal=json.loads((B/'COMMAND.json').read_text())
 assert all(m in normal['built_modules'] for m in modules)
 install=json.loads((B/'SOURCE_INSTALL.json').read_text())
 expected={x['module']:x['after_sha256'] for x in install['source_updates']}
 assert all(baseline[m][m.replace('.','/')+'.lean']['sha256']==expected[m] for m in modules)
 result={'status':'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS','modules':{m:expected[m] for m in modules},'reused_normal_command':normal,'kernel_commands':kernels,'audit_command':audit,'stock_readiness_before':readiness,'stock_readiness_after':after,'source_plus_five_outputs':baseline,'total_owned_exports':len(records),'total_public_exports':sum(not x['is_private'] for x in records),'full_owned_including_private_generated':True,'only_standard_axioms':True,'pp_all_true_no_elisions':True,'source_plus_five_outputs_unchanged_across_kernel_and_audit':True,'successful_normal_not_repeated':True,'whole_P1_complete':False,'verified_utc':now(),'runtime_state':str(state),'runtime_state_sha256':sha(state)}
 save(L/'VALIDATION_RESULTS.json',result)
 print('LANE_PASS',i,len(modules),len(records),flush=True)
if len(sys.argv)>1:
 lane(int(sys.argv[1]));raise SystemExit(0)
R.mkdir(exist_ok=False)
normal=json.loads((B/'COMMAND.json').read_text());modules=normal['built_modules'];assert len(modules)==13
save(R/'TARGETS.json',modules)
def launch(i):
 L=R/f'lane-{i}';L.mkdir();save(L/'MODULES.json',modules[i::2])
 args=['python3','/workspace/blue-build-tools/serialize_validation_lane.py','--state',str(STATES[i]),'--receipt',str(L/'VALIDATION_LANE.json'),'python3',__file__,str(i)]
 return subprocess.run(args,cwd=P).returncode
started=now();t=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:codes=list(pool.map(launch,[0,1]))
result={'started_utc':started,'finished_utc':now(),'elapsed_seconds':time.monotonic()-t,'lane_exit_codes':codes,'modules':modules,'two_existing_lanes':True,'normal_builds_not_repeated':True,'whole_P1_complete':False}
save(R/'PARALLEL_RESULT.json',result);print('PARALLEL_RESULT',json.dumps(result),flush=True)
raise SystemExit(0 if codes==[0,0] else 1)
