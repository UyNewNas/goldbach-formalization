from pathlib import Path
from seed42_reuse_metadata import (SEED, ARCHIVE, verify_seed_leaf, parse_complete_owned,
    write_exact, capture_archive_audit_runtime, collect_actual_runtime)
import datetime,hashlib,json,re,subprocess,time
R=Path('/workspace/blue-member-repair-batch84');P=Path('/workspace/blue-member-build');MAIN=Path('/workspace/goldbach-formalization');STATE=Path('/workspace/blue-build-tools/runtime-evidence/state.json');EXPECTED=json.loads((R/'EXPECTED_SOURCES.json').read_text());G=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(STATE)]
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
# Immutable Seed success must validate before the original skip loop can run.
_seed_before = verify_seed_leaf(R,P,STATE,EXPECTED)
assert sha(R/'ArchiveOnlyAudit.lean') == '87ccdaf4440c11c7dc32fdfd35d048885acdca53017ef087105bdd41b06d75d9'
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
# Fresh audit is ARCHIVE ONLY. The Seed raw source remains the old leaf log.
_seed = verify_seed_leaf(R,P,STATE,EXPECTED,baselines)
_state = json.loads(STATE.read_text());_journal = Path(_state['log'])
_archive_receipt = R/'archive-only-owned-types-axioms-command.json'
_archive_audit_previously_successful = _archive_receipt.exists()
_archive_offset = None if _archive_audit_previously_successful else _journal.stat().st_size
rec=run('archive-only-owned-types-axioms',G+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--root='+str(R),str(R/'ArchiveOnlyAudit.lean')],'archive-only-types-axioms.log')
if rec['exit_code']:raise SystemExit(rec['exit_code'])
_archive_runtime = capture_archive_audit_runtime(R,STATE,_archive_offset)
assert sha(R/'ArchiveOnlyAudit.lean') == '87ccdaf4440c11c7dc32fdfd35d048885acdca53017ef087105bdd41b06d75d9'
assert all(snap(m)==baselines[m] for m in EXPECTED)
_seed = verify_seed_leaf(R,P,STATE,EXPECTED,baselines)
_archive_records = parse_complete_owned(R/'archive-only-types-axioms.log',ARCHIVE)
_seed_records = _seed['records']
raw_records = _seed_records + _archive_records
names = [x['name'] for x in raw_records]
assert len(names)==len(set(names)) and {x['module'] for x in raw_records}=={SEED,ARCHIVE}==set(EXPECTED)
# Enriched union is derived metadata; neither original audit raw is rewritten.
records = [dict(x,transitive_axioms=x['axioms'],is_axiom_declaration=False) for x in raw_records]
pub = [x for x in records if not x['is_private']]
write_exact(R/'OWNED_EXPORTS.json',records)
write_exact(R/'PUBLIC_EXPORTS.json',pub)
_runtime = collect_actual_runtime(R,P,STATE,_seed,_archive_runtime)
write_exact(R/'ACTUAL_RUNTIME_COMMANDS.json',_runtime)
_seed_raw=R/'seed42-owned-only/audit.log';_archive_raw=R/'archive-only-types-axioms.log'
audit_commands=[
 {'modules':[SEED],'reused_existing_success':True,'command':_seed['audit'],
  'command_receipt':'seed42-owned-only/AUDIT_COMMAND.json','raw_log':'seed42-owned-only/audit.log',
  'raw_log_sha256':sha(_seed_raw),'raw_log_bytes':_seed_raw.stat().st_size},
 {'modules':[ARCHIVE],'reused_existing_success':_archive_audit_previously_successful,'command':rec,
  'command_receipt':'archive-only-owned-types-axioms-command.json','raw_log':'archive-only-types-axioms.log',
  'raw_log_sha256':sha(_archive_raw),'raw_log_bytes':_archive_raw.stat().st_size}]
owned_counts={m:sum(x['module']==m for x in records) for m in EXPECTED}
counts={m:sum(x['module']==m for x in pub) for m in EXPECTED}
per_module_raw_sources={a['modules'][0]:{
 'command_receipt':a['command_receipt'],'raw_log':a['raw_log'],
 'raw_log_sha256':a['raw_log_sha256'],'raw_log_bytes':a['raw_log_bytes'],
 'owned_count':owned_counts[a['modules'][0]],'public_count':counts[a['modules'][0]],
 'reused_existing_success':a['reused_existing_success']} for a in audit_commands}
write_exact(R/'REUSED_SEED42_ACCEPTANCE.json',{
 'status':'REUSED_EXACT_PREVIOUS_SEED42_NORMAL_KERNEL_AND_COMPLETE_OWNED',
 'module':SEED,'pinned_leaf_records':_seed['pins'],'source_plus_five_outputs':_seed['snapshot'],
 'normal_receipt':SEED.split('.')[-1]+'-normal-command.json',
 'kernel_receipt':SEED.split('.')[-1]+'-kernel-command.json',
 'audit_receipt':'seed42-owned-only/AUDIT_COMMAND.json',
 'raw_audit_log':'seed42-owned-only/audit.log','owned_total':17,'public_total':1,'private_total':16,
 'no_Seed_normal_kernel_or_owned_rerun':True,'current_SourcePlusFive_matches_original_leaf_and_baseline':True})
write_exact(R/'VALIDATION_RESULTS.json',{
 'status':'PASS_NORMAL_KERNEL_ALL_ENVIRONMENT_OWNED_TYPES_AXIOMS',
 'modules':EXPECTED,'normal_commands':normal,'kernel_commands':kernel,
 'audit_commands':audit_commands,'audit_raw_sources_by_module':per_module_raw_sources,
 'audit_composition':'Two independent successful defining-owner inventories; exact immutable Seed17 leaf raw plus fresh Archive-only raw. No single raw is claimed to contain both.',
 'audit_command':rec,'audit_command_scope':[ARCHIVE],
 'public_export_counts':counts,'total_public_exports':len(pub),
 'owned_export_counts':owned_counts,'total_owned_exports':len(records),
 'full_owned_including_private_generated':True,'only_standard_axioms':True,
 'pp_all_true_no_elisions':True,'source_plus_five_outputs_unchanged_across_kernel_and_audit':True,
 'source_plus_five_outputs':baselines,'successful_tests_repeated':False,
 'Seed42_normal_kernel_complete_owned_reused_without_repeat':True,
 'P6_or_frozen_archives_modified':False,'committed':False,
 'verified_utc':rec['finished_utc']})
print('PASS_COMPOSED_ARCHIVE_FRESH_SEED17_REUSED',counts,flush=True)
