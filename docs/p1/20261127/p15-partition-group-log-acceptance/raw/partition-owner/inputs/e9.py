#!/usr/bin/env python3
"""Reuse SHA-bound normal logs; preserve the existing two-lane kernel/full-owned audit."""
from pathlib import Path
import argparse,concurrent.futures,datetime,hashlib,json,re,subprocess,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--plan',required=True,type=Path)
parser.add_argument('--receipt-root',type=Path)
parser.add_argument('--prepare-only',action='store_true',help='Create receipt/lane inputs without invoking Lean, Lake, or guards.')
parser.add_argument('--lane',type=int,choices=[0,1],help='Run one already prepared lane inside the existing serializer.')
A=parser.parse_args()
PLAN_PATH=A.plan.resolve();PLAN_BYTES=PLAN_PATH.read_bytes();PLAN=json.loads(PLAN_BYTES)
assert PLAN['schema']=='p1_completed_normal_multibatch_audit_plan_v1'
P=Path(PLAN['project']);R=A.receipt_root or Path(PLAN['receipt_root'])
STATES=[Path(p) for p in PLAN['runtime_states']]
assert len(STATES)==2 and len(PLAN['lanes'])==2
modules=[m for lane_plan in PLAN['lanes'] for m in lane_plan['modules']]
assert len(modules)==len(set(modules)) and set(modules)==set(PLAN['modules'])
assert not (set(modules)&set(PLAN['excluded_prior13']))
assert not (set(modules)&set(PLAN['reused_complete_modules']))
assert [l['id'] for l in PLAN['lanes']]==[0,1]
ANSI=re.compile(r'\x1b\[[0-?]*[ -/]*[@-~]')
BUILT=re.compile(r'^\s*[✔⚠ℹ]\ufe0f?\s+\[[^\]\r\n]+\]\s+Built\s+(ImbalancedChen(?:\.[A-Za-z0-9_]+)+)(?::olean)?(?=\s|$)',re.M)

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
def check_project_sources(selected):
 deps=set().union(*(set(PLAN['modules'][m]['project_closure']) for m in selected))
 expected={m:PLAN['expected_project_sources'][m] for m in sorted(deps)}
 assert all(sha(P/(m.replace('.','/')+'.lean'))==s for m,s in expected.items()),'project dependency source differs from plan'
 return expected
def normal_evidence(selected):
 evidence={}
 for key in sorted({PLAN['modules'][m]['normal_log'] for m in selected}):
  expected=PLAN['normal_logs'][key];path=Path(expected['path'])
  assert sha(path)==expected['sha256'],('normal_log_sha256_mismatch',str(path))
  raw=ANSI.sub('',path.read_text());built=BUILT.findall(raw)
  assert set(built)==set(expected['expected_built_modules']),('complete_built_header_set_mismatch',str(path))
  selected_here=[m for m in selected if PLAN['modules'][m]['normal_log']==key]
  assert set(selected_here)<=set(built)
  headers=[{'line':n,'text':s,'module':match.group(1)} for n,s in enumerate(raw.splitlines(),1)
           if (match:=BUILT.match(s)) and match.group(1) in selected_here]
  evidence[key]={'path':str(path),'sha256':expected['sha256'],'source_commit':expected['source_commit'],
                 'all_actual_built_modules':built,'selected_actual_built_headers':headers,
                 'selected_sources':{m:PLAN['modules'][m]['source_sha256'] for m in selected_here},
                 'success_symbols_accepted':['✔','⚠','ℹ'],'whole_normal_batch_exit0_required':False}
 return evidence
def run(L,name,args):
 rec={'argv':args,'cwd':str(P),'started_utc':now()};t=time.monotonic()
 with (L/(name+'.log')).open('x') as out:p=subprocess.run(args,cwd=P,stdout=out,stderr=subprocess.STDOUT)
 rec.update(exit_code=p.returncode,elapsed_seconds=time.monotonic()-t,finished_utc=now(),log=name+'.log',log_sha256=sha(L/(name+'.log')))
 save(L/(name+'-command.json'),rec)
 print(json.dumps({'lane':L.name,'stage':name,'exit_code':p.returncode,'seconds':rec['elapsed_seconds']}),flush=True)
 if p.returncode:raise RuntimeError((L.name,name,p.returncode))
 return rec
def lane(i):
 L=R/f'lane-{i}';selected=json.loads((L/'MODULES.json').read_text());state=STATES[i]
 assert selected==PLAN['lanes'][i]['modules']
 assert sha(R/'AUDIT_PLAN.json')==hashlib.sha256(PLAN_BYTES).hexdigest()
 G=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(state)]
 normal=normal_evidence(selected);save(L/'REUSED_NORMAL_EVIDENCE.json',normal)
 dependency_sources=check_project_sources(selected);save(L/'PROJECT_SOURCE_BINDING.json',dependency_sources)
 baseline={m:snap(m) for m in selected};save(L/'BEFORE_KERNEL.json',baseline)
 expected={m:PLAN['modules'][m]['source_sha256'] for m in selected}
 assert all(baseline[m][m.replace('.','/')+'.lean']['sha256']==expected[m] for m in selected)
 readiness=run(L,'stock-readiness-before',G+['lake','--no-build','build']+['+'+m+':olean' for m in selected])
 kernels={}
 for m in selected:
  kernels[m]=run(L,m.split('.')[-1]+'-kernel',G+['lake','env','leanchecker','--verbose',m])
  assert snap(m)==baseline[m],('changed_during_kernel',m)
 template_path=Path(PLAN['audit_template']['path'])
 assert sha(template_path)==PLAN['audit_template']['sha256'],'full-owned audit template differs'
 template=template_path.read_text()
 template=re.sub(r'^import ImbalancedChen\.[^\n]+\n','',template,flags=re.M)
 template=''.join('import '+m+'\n' for m in selected)+template
 template,count=re.subn(r'let modules := #\[[^\n]*\]', 'let modules := #['+', '.join('`'+m for m in selected)+']',template,count=1)
 assert count==1,'full-owned audit module-array substitution did not match'
 with (L/'PublicAudit.lean').open('x') as out:out.write(template)
 audit=run(L,'all-owned-types-axioms',G+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--root='+str(L),str(L/'PublicAudit.lean')])
 text=(L/'all-owned-types-axioms.log').read_text()
 records=[json.loads(s) for s in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',text)]
 inventory=[json.loads(s)['names'] for s in re.findall(r'MEMBER_OWNED_NAMES (\{[^\n]+\})',text)]
 names=[x['name'] for x in records];assert len(inventory)==1 and sorted(names)==sorted(inventory[0])
 assert len(set(names))==len(names) and {x['module'] for x in records}==set(selected)
 assert all(x['kind']!='axiom' and set(x['axioms'])<={'propext','Classical.choice','Quot.sound'} for x in records)
 assert not any(s in text for s in ['sorryAx','…','⋯','...'])
 save(L/'OWNED_EXPORTS.json',records)
 after=run(L,'stock-readiness-after',G+['lake','--no-build','build']+['+'+m+':olean' for m in selected])
 assert {m:snap(m) for m in selected}==baseline
 assert check_project_sources(selected)==dependency_sources
 assert normal_evidence(selected)==normal
 assert sha(R/'AUDIT_PLAN.json')==hashlib.sha256(PLAN_BYTES).hexdigest()
 result={'status':'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS','modules':expected,'reused_normal_evidence':normal,'kernel_commands':kernels,'audit_command':audit,'stock_readiness_before':readiness,'stock_readiness_after':after,'source_plus_five_outputs':baseline,'project_dependency_sources':dependency_sources,'total_owned_exports':len(records),'total_public_exports':sum(not x['is_private'] for x in records),'full_owned_including_private_generated':True,'only_standard_axioms':True,'pp_all_true_no_elisions':True,'source_plus_five_outputs_unchanged_across_kernel_and_audit':True,'successful_normal_not_repeated':True,'audit_template_sha256':PLAN['audit_template']['sha256'],'plan_sha256':hashlib.sha256(PLAN_BYTES).hexdigest(),'whole_P1_complete':False,'verified_utc':now(),'runtime_state':str(state),'runtime_state_sha256':sha(state)}
 save(L/'VALIDATION_RESULTS.json',result)
 print('LANE_PASS',i,len(selected),len(records),flush=True)
def prepare():
 R.mkdir(exist_ok=False)
 with (R/'AUDIT_PLAN.json').open('xb') as f:f.write(PLAN_BYTES)
 save(R/'PLAN_BINDING.json',{'path':str(PLAN_PATH),'sha256':hashlib.sha256(PLAN_BYTES).hexdigest(),'runner_sha256':sha(Path(__file__)),'prepared_utc':now(),'no_compiler_invoked_by_preparation':True})
 save(R/'TARGETS.json',modules)
 for i,lp in enumerate(PLAN['lanes']):
  L=R/f'lane-{i}';L.mkdir();save(L/'MODULES.json',lp['modules'])
def launch(i):
 L=R/f'lane-{i}'
 args=['python3','/workspace/blue-build-tools/serialize_validation_lane.py','--state',str(STATES[i]),'--receipt',str(L/'VALIDATION_LANE.json'),'python3',str(Path(__file__).resolve()),'--plan',str(R/'AUDIT_PLAN.json'),'--receipt-root',str(R),'--lane',str(i)]
 return subprocess.run(args,cwd=P).returncode
if A.lane is not None:
 assert not A.prepare_only
 lane(A.lane);raise SystemExit(0)
prepare()
if A.prepare_only:
 print('PREPARED',str(R),'lane_sizes',[len(lp['modules']) for lp in PLAN['lanes']],flush=True)
 raise SystemExit(0)
started=now();t=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:codes=list(pool.map(launch,[0,1]))
result={'started_utc':started,'finished_utc':now(),'elapsed_seconds':time.monotonic()-t,'lane_exit_codes':codes,'modules':modules,'plan_sha256':hashlib.sha256(PLAN_BYTES).hexdigest(),'two_existing_lanes':True,'normal_builds_not_repeated':True,'whole_P1_complete':False}
save(R/'PARALLEL_RESULT.json',result);print('PARALLEL_RESULT',json.dumps(result),flush=True)
raise SystemExit(0 if codes==[0,0] else 1)
