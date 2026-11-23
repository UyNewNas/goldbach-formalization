"""Install one qualified, missing P6 portable native group only during the natural controller handoff window."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time
R=Path('/workspace/blue-member-aggregate-evidence');P6=Path('/workspace/blue-p6-build/.lake/packages/goldbach');MEM=Path('/workspace/blue-member-build/.lake/packages/goldbach');MOD='MathlibNt.SieveTheory.LiLiuBuchstabTailPropagation';REL=MOD.replace('.','/')
STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def release(status,receipt):
 write(R/'P6_SINGLE_NATIVE_INSTALL_RECEIPT.json',receipt)
 write(R/'REUSE_WINDOW_RELEASED.json',{'status':status,'released_utc':now(),'receipt':'P6_SINGLE_NATIVE_INSTALL_RECEIPT.json','no_extra_source_slot':True})
print(json.dumps({'status':'WAITING_FOR_NATURAL_WINDOW','utc':now()}),flush=True)
while not (R/'REUSE_WINDOW_OPEN.json').exists():time.sleep(5)
assert not (R/'attempt-1-command-running.json').exists()
receipt={'module':MOD,'started_utc':now(),'source_files_modified':False,'P6_files_modified':False,'native_executables_installed':False,'no_clobber':True}
if (MEM/('.lake/build/lib/lean/'+REL+'.olean')).exists():
 receipt.update(status='SKIPPED_MEMBER_GROUP_ALREADY_EXISTS_AFTER_OLD_CONTROLLER',current_olean_sha256=sha(MEM/('.lake/build/lib/lean/'+REL+'.olean')))
 release(receipt['status'],receipt);print(json.dumps(receipt),flush=True);raise SystemExit(0)
# No controller is building this module: old controller completed; the ten-root controller is gated; Prototype writes separate paths.
source_arg=str(MEM/(REL+'.lean'));active=[]
for proc in Path('/proc').iterdir():
 if not proc.name.isdigit():continue
 try:argv=[s for s in (proc/'cmdline').read_bytes().decode().split('\0') if s]
 except (FileNotFoundError,ProcessLookupError,PermissionError,UnicodeDecodeError):continue
 if source_arg in argv:active.append({'pid':int(proc.name),'argv':argv})
if active:
 receipt.update(status='REJECTED_MEMBER_SOURCE_QUEUED_OR_ACTIVE',active=active);release(receipt['status'],receipt);raise SystemExit(0)
q=json.loads((R/'P6_SINGLE_NATIVE_IMPORT_QUALIFICATION.json').read_text());assert q['unresolved_count']==0 and q['all_checked_matches']
rechecks=[];blocked=[]
for e in q['current_checks']:
 p=Path(e['P6_path']);m=Path(e['Member_path'])
 if e['method']=='FRESH_SHA256_BOTH_NATIVE_FACETS':
  ok=sha(p)==sha(m)==e['sha256']
 else:
  st=p.stat();ok=str(p.resolve())==str(m.resolve())==e['resolved'] and (st.st_size,st.st_mtime_ns,st.st_ctime_ns)==(e['bytes'],e['mtime_ns'],e['ctime_ns'])
 rechecks.append({'module':e['module'],'P6_path':str(p),'Member_path':str(m),'sha256':e['sha256'],'same_actual_object_bytes_reconfirmed':ok,'method':e['method']})
 if not ok:blocked.append(e)
ps=json.loads(Path('/workspace/blue-build-tools/runtime-evidence/state.json').read_text());ms=json.loads(STATE.read_text())
core='/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean'
assert ps['runtime_sha256'][core]==ms['runtime_sha256'][core]
assert ps['policy']==ms['policy']
setup=json.loads((P6/('.lake/build/ir/'+REL+'.setup.json')).read_text());assert setup['name']==MOD and setup['package']=='goldbach' and setup['options']=={} and setup['plugins']==setup['dynlibs']==[] and setup['isModule'] is False
registered=json.loads(Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json').read_text())['native_sources'][MOD]['sha256']
assert sha(P6/(REL+'.lean'))==sha(MEM/(REL+'.lean'))==registered
runtime_events=[json.loads(line) for line in Path(ps['log']).read_text().splitlines() if source_arg.replace('/blue-member-build/','/blue-p6-build/') in line]
production=next(e for e in reversed(runtime_events) if e.get('tool')=='lean' and str(P6/(REL+'.lean')) in e.get('command',[]))
assert all(f in production['command'] for f in ['-t0','-j2','-M12288'])
receipt.update(source_sha256=registered,setup_options=setup['options'],source_runtime_event=production,runtime_compiler_sha256=ps['runtime_sha256'][core],runtime_policy=ps['policy'],producer_stock_receipt='P6_SINGLE_NATIVE_PRODUCER_STOCK.json',import_qualification_receipt='P6_SINGLE_NATIVE_IMPORT_QUALIFICATION.json',import_facet_rechecks=len(rechecks),common_facets_rehashed=0,native_facets_fresh_sha256=2,actual_import_rechecks=rechecks,blocked_imports=blocked)
if blocked:
 receipt['status']='REJECTED_IMPORT_IDENTITY_CHANGED_BEFORE_WINDOW';release(receipt['status'],receipt);raise SystemExit(0)
# Complete portable group and generated C source only; never copy compiled native executables.
facets=[]
for prefix,suffix in [('.lake/build/lib/lean/','.olean'),('.lake/build/lib/lean/','.olean.private'),('.lake/build/lib/lean/','.olean.server'),('.lake/build/lib/lean/','.ilean'),('.lake/build/lib/lean/','.ir'),('.lake/build/lib/lean/','.ir.sig'),('.lake/build/lib/lean/','.olean.hash'),('.lake/build/lib/lean/','.ilean.hash'),('.lake/build/ir/','.c'),('.lake/build/ir/','.c.hash'),('.lake/build/ir/','.setup.json'),('.lake/build/lib/lean/','.trace')]:
 rel=prefix+REL+suffix;src=P6/rel;dst=MEM/rel
 if not src.exists():continue
 payload=src.read_bytes();h=hashlib.sha256(payload).hexdigest()
 facets.append({'relative_path':rel,'src':src,'dst':dst,'payload':payload,'sha256':h,'bytes':len(payload),'already_present':dst.exists()})
 conflicts=[f['relative_path'] for f in facets if f['dst'].exists() and sha(f['dst'])!=f['sha256']]
if conflicts:
 receipt.update(status='REJECTED_EXISTING_FACET_CONFLICT_NO_CLOBBER',conflicts=conflicts);release(receipt['status'],receipt);raise SystemExit(0)
for f in facets:
 if f['already_present']:continue
 f['dst'].parent.mkdir(parents=True,exist_ok=True)
 with f['dst'].open('xb') as out:out.write(f['payload'])
 assert sha(f['dst'])==sha(f['src'])==f['sha256']
receipt['installed_files']=[{k:v for k,v in f.items() if k not in ['src','dst','payload']} for f in facets]
# Native single-target stock no-build acceptance in destination context. Other shared-guard jobs may run; we count only this source path.
def events():
 return [json.loads(line) for line in Path(ms['log']).read_text().splitlines() if source_arg in line]
write(R/'P6_SINGLE_NATIVE_COPY_COMPLETE.json',{'status':'COPY_COMPLETE_WAITING_STOCK_RELEASE','utc':now(),'files':[{k:v for k,v in f.items() if k not in ['src','dst','payload']} for f in facets]})
while not (R/'STOCK_RELEASED.json').exists():time.sleep(1)
before_events=events();before={f['relative_path']:sha(f['dst']) for f in facets};cmd=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(STATE),'lake','--no-build','build','@goldbach/+'+MOD+':olean'];t=time.monotonic();started=now()
with (R/'member-single-native-stock.log').open('x') as out:child=subprocess.run(cmd,cwd='/workspace/blue-member-build',stdout=out,stderr=subprocess.STDOUT)
after_events=events();after={f['relative_path']:sha(f['dst']) for f in facets}
receipt['destination_stock']={'argv':cmd,'cwd':'/workspace/blue-member-build','started_utc':started,'finished_utc':now(),'elapsed_seconds':time.monotonic()-t,'exit_code':child.returncode,'log':'member-single-native-stock.log','log_sha256':sha(R/'member-single-native-stock.log'),'no_build_enforced':True,'source_compiler_calls_for_target':len(after_events)-len(before_events),'copied_facet_hashes_unchanged':before==after}
receipt['status']='PORTABLE_GROUP_REUSED_STOCK_UP_TO_DATE_ZERO_SOURCE_CALLS' if child.returncode==0 and len(after_events)==len(before_events) and before==after else 'COPIED_GROUP_STOCK_DIAGNOSIS_REQUIRED'
receipt['finished_utc']=now();release(receipt['status'],receipt)
print(json.dumps({k:v for k,v in receipt.items() if k!='actual_import_rechecks'}),flush=True)
raise SystemExit(0)
