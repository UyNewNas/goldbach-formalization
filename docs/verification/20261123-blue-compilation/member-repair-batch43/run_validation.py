from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
R=Path('/workspace/blue-member-repair-batch43');P=Path('/workspace/blue-member-build');MAIN=Path('/workspace/goldbach-formalization');STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json');EXPECTED=json.loads((R/'EXPECTED_SOURCES.json').read_text());G=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(STATE)]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def snap(mod):
 rel=mod.replace('.','/');paths=[rel+'.lean','.lake/build/lib/lean/'+rel+'.olean','.lake/build/lib/lean/'+rel+'.ilean','.lake/build/ir/'+rel+'.c','.lake/build/ir/'+rel+'.setup.json','.lake/build/lib/lean/'+rel+'.trace'];return {s:{'bytes':(P/s).stat().st_size,'sha256':sha(P/s)} for s in paths if (P/s).exists()}
def run(name,argv,log):
 recpath=R/(name+'-command.json')
 if recpath.exists():
  x=json.loads(recpath.read_text());assert x['exit_code']==0,('previous_failure',name);return x
 t=time.monotonic();rec={'name':name,'argv':argv,'cwd':str(P),'started_utc':now()}
 with (R/log).open('x') as out:child=subprocess.run(argv,cwd=P,stdout=out,stderr=subprocess.STDOUT)
 rec.update(exit_code=child.returncode,finished_utc=now(),elapsed_seconds=time.monotonic()-t,log=log,log_sha256=sha(R/log));write(recpath,rec);print(json.dumps(rec),flush=True)
 return rec
assert all(sha(P/(m.replace('.','/')+'.lean'))==s for m,s in EXPECTED.items())
# One stock readiness pass shares importer metadata; this command is prohibited from compiling.
if not (R/'stock-readiness-command.json').exists():
 rec=run('stock-readiness',G+['lake','--no-build','build']+['+'+m+':olean' for m in EXPECTED],'stock-readiness.log')
 text=(R/'stock-readiness.log').read_text();fails=re.findall(r'(?m)^error: ([A-Za-z0-9_.]+):',text);write(R/'STOCK_READINESS.json',{'exit_code':rec['exit_code'],'failed_targets':fails,'selected_targets':list(EXPECTED),'raw_log':'stock-readiness.log','no_build_enforced':True});assert rec['exit_code'] in [0,3]
 failed=re.findall(r'(?m)^✖ .*? (?:Building|Running) ([A-Za-z0-9_.]+)',text);assert set(failed)<=set(EXPECTED),('unready imported supplier',failed)
normal=[];kernel=[];baselines={};pending=[]
for mod in EXPECTED:
 short=mod.split('.')[-1]
 prior=R/(short+'-normal-command.json')
 if prior.exists() and json.loads(prior.read_text())['exit_code']!=0:
  pending.append(mod);continue
 rec=run(short+'-normal',G+['lake','build',mod+':olean'],short+'-normal.log');normal.append(rec)
 if rec['exit_code']:
  write(R/(short+'-FAILED_STAGE.json'),{'module':mod,'stage':'normal','record':rec});pending.append(mod);continue
 saved=R/(short+'-AFTER_NORMAL.json');baseline=json.loads(saved.read_text()) if saved.exists() else snap(mod);assert len(baseline)==6 and snap(mod)==baseline;baselines[mod]=baseline
 if not saved.exists():write(saved,baseline)
 rec=run(short+'-kernel',G+['lake','env','leanchecker','--verbose',mod],short+'-kernel.log');kernel.append(rec)
 if rec['exit_code']:write(R/'FAILED_STAGE.json',{'module':mod,'stage':'kernel','record':rec});raise SystemExit(rec['exit_code'])
 assert snap(mod)==baseline
 savedkernel=R/(short+'-AFTER_KERNEL.json')
 if savedkernel.exists():assert json.loads(savedkernel.read_text())==baseline
 else:write(savedkernel,baseline)
if pending:
 write(R/'PENDING_REPAIRS.json',pending);print('PENDING_REPAIRS',pending,flush=True);raise SystemExit(1)
rec=run('all-public-types-axioms',G+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--root='+str(R),str(R/'PublicAudit.lean')],'types-axioms.log')
if rec['exit_code']:raise SystemExit(rec['exit_code'])
assert all(snap(m)==baselines[m] for m in EXPECTED)
text=(R/'types-axioms.log').read_text();records=[json.loads(s) for s in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',text)];names={x['name'] for x in records};assert len(names)==len(records) and {x['module'] for x in records}==set(EXPECTED)
axioms={}
for n,b in re.findall(r"(?m)^'([^']+)' depends on axioms:\s*\[([^]]*)\]",text):axioms[n]=[re.sub(r'\.\{[^}]*\}$','',x.strip()) for x in b.split(',') if x.strip()]
for n in re.findall(r"(?m)^'([^']+)' does not depend on any axioms",text):axioms[n]=[]
assert set(axioms)==names and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values());assert not any(x['is_axiom_declaration'] for x in records);assert not any(t in text for t in ['sorryAx','…','⋯','...'])
for x in records:x['transitive_axioms']=axioms[x['name']]
write(R/'PUBLIC_EXPORTS.json',records)
state=json.loads(STATE.read_text());targets=[str(P/(m.replace('.','/')+'.lean')) for m in EXPECTED]+[str(R/'PublicAudit.lean')];events={}
for line in Path(state['log']).read_text().splitlines():
 e=json.loads(line)
 if e.get('tool')=='lean':
  for target in targets:
   if target in e.get('command',[]):events[target]=e
assert set(events)==set(targets)
for e in events.values():assert all(v in e['command'] for v in ['-t0','-j2','-M12288','maxRecDepth=100000','maxHeartbeats=4000000'])
write(R/'ACTUAL_RUNTIME_COMMANDS.json',{'state':str(STATE),'state_sha256':sha(STATE),'serial_compiler_lock':state['slot'],'actual_compiler_commands':events})
counts={m:sum(x['module']==m for x in records) for m in EXPECTED};write(R/'VALIDATION_RESULTS.json',{'status':'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_PUBLIC_TYPES_AXIOMS','modules':EXPECTED,'normal_commands':normal,'kernel_commands':kernel,'audit_command':rec,'public_export_counts':counts,'total_public_exports':len(records),'only_standard_axioms':True,'pp_all_true_no_elisions':True,'source_plus_five_outputs_unchanged_across_kernel_and_audit':True,'source_plus_five_outputs':baselines,'successful_tests_repeated':False,'P6_or_frozen_archives_modified':False,'committed':False,'verified_utc':now()});print('PASS',counts,flush=True)
