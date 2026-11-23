from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
R=Path('/workspace/blue-mask-transport-repair');P=Path('/workspace/blue-member-build');M=Path('/workspace/goldbach-formalization');STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json');MOD='ImbalancedChen.CurrentChenP5SelectedMaskTransport';REL=MOD.replace('.','/');EXPECTED='7d803e10e417a48a68de8ff8c5facb51ecf757194c53a307988784cf3aa4267c';G=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(STATE)]
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def snapshot():
 paths=[REL+'.lean','.lake/build/lib/lean/'+REL+'.olean','.lake/build/lib/lean/'+REL+'.ilean','.lake/build/ir/'+REL+'.c','.lake/build/ir/'+REL+'.setup.json','.lake/build/lib/lean/'+REL+'.trace'];return {s:{'bytes':(P/s).stat().st_size,'sha256':sha(P/s)} for s in paths if (P/s).exists()}
assert json.loads((R/'stock-readiness/PROCESS.json').read_text())['all_imports_replayed_only_target_requires_build'];assert sha(P/(REL+'.lean'))==sha(M/(REL+'.lean'))==EXPECTED
stages=[('normal_module_build',G+['lake','build',MOD+':olean'],'normal-build.log'),('kernel_replay',G+['lake','env','leanchecker','--verbose',MOD],'kernel.log'),('all_environment_public_types_axioms',G+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--root='+str(R),str(R/'PublicAudit.lean')],'types-axioms.log')];results=[];baseline=None
for name,argv,log in stages:
 t=time.monotonic();rec={'name':name,'argv':argv,'cwd':str(P),'started_utc':now()}
 with (R/log).open('x') as out:child=subprocess.run(argv,cwd=P,stdout=out,stderr=subprocess.STDOUT)
 rec.update(exit_code=child.returncode,finished_utc=now(),elapsed_seconds=time.monotonic()-t,log=log,log_sha256=sha(R/log),source_plus_five_outputs_after_stage=snapshot());write(R/(name+'-command.json'),rec);results.append(rec);print(json.dumps({k:v for k,v in rec.items() if k!='source_plus_five_outputs_after_stage'}),flush=True)
 if child.returncode:write(R/'VALIDATION_RESULTS.json',{'status':'FAILED_STAGE','module':MOD,'stages':results});raise SystemExit(child.returncode)
 if baseline is None:baseline=snapshot();assert len(baseline)==6
 else:assert baseline==snapshot()
text=(R/'types-axioms.log').read_text();records=[json.loads(s) for s in re.findall(r'AUDIT_RECORD (\{[^\n]+\})',text)];names={x['name'] for x in records};source_names=set(json.loads((R/'PUBLIC_SOURCE_DECLARATIONS.json').read_text()));assert source_names<=names and len(names)==len(records)
axioms={}
for n,body in re.findall(r"(?m)^'([^']+)' depends on axioms:\s*\[([^]]*)\]",text):axioms[n]=[re.sub(r'\.\{[^}]*\}$','',x.strip()) for x in body.split(',') if x.strip()]
for n in re.findall(r"(?m)^'([^']+)' does not depend on any axioms",text):axioms[n]=[]
assert set(axioms)==names and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values());assert not any(x['is_axiom_declaration'] for x in records);assert not any(t in text for t in ['sorryAx','…','⋯','...'])
for x in records:x['transitive_axioms']=axioms[x['name']]
write(R/'PUBLIC_EXPORTS.json',records);assert sha(P/(REL+'.lean'))==sha(M/(REL+'.lean'))==EXPECTED
state=json.loads(STATE.read_text());targets=[str(P/(REL+'.lean')),str(R/'PublicAudit.lean')];events={}
for line in Path(state['log']).read_text().splitlines():
 e=json.loads(line)
 if e.get('tool')=='lean':
  for target in targets:
   if target in e.get('command',[]):events[target]=e
assert set(events)==set(targets)
for e in events.values():assert all(v in e['command'] for v in ['-t0','-j2','-M12288','maxRecDepth=100000','maxHeartbeats=4000000'])
write(R/'ACTUAL_RUNTIME_COMMANDS.json',{'state':str(STATE),'state_sha256':sha(STATE),'serial_compiler_lock':state['slot'],'actual_compiler_commands':events})
x={'status':'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_PUBLIC_TYPES_AXIOMS','module':MOD,'source_sha256':EXPECTED,'stages':results,'source_plus_five_outputs':snapshot(),'source_and_all_five_outputs_unchanged_across_kernel_audit':True,'source_public_declarations':len(source_names),'all_environment_public_exports':len(records),'pp_all_check_at_print_axioms_for_every_environment_public_export':True,'all_type_output_no_elisions':True,'only_standard_axioms':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'actual_runtime_commands':'ACTUAL_RUNTIME_COMMANDS.json','environment_moduleNames_cached_once':True,'axiom_dependency_collected_once_by_builtin_print_axioms':True,'successful_tests_repeated':False,'P6_or_frozen_archives_modified':False,'committed':False,'verified_utc':now()};write(R/'VALIDATION_RESULTS.json',x);receipt=json.loads((R/'REPAIR_RECEIPT.json').read_text());receipt.update(status=x['status'],validation_results='VALIDATION_RESULTS.json');write(R/'REPAIR_RECEIPT.json',receipt);print(json.dumps({k:v for k,v in x.items() if k not in ['stages','source_plus_five_outputs']}),flush=True)
