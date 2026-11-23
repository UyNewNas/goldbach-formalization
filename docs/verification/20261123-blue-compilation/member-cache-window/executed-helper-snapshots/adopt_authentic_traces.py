"""Qualified adoption of exact existing producer trace bytes; never rebase or synthesize a trace."""
from pathlib import Path
import datetime,hashlib,json,os,subprocess,time,re,sys
R=Path('/workspace/blue-member-aggregate-evidence');O=R/'prototype-qualified';A=O/'trace-adoption-v1';PR=Path('/workspace/blue-reindex-build');ME=Path('/workspace/blue-member-build');STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
A.mkdir(exist_ok=False)
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def stat(p):
 s=p.stat();return {'bytes':s.st_size,'mtime_ns':s.st_mtime_ns,'ctime_ns':s.st_ctime_ns,'dev':s.st_dev,'ino':s.st_ino}
initial=json.loads(Path('/workspace/blue-reindex-build-evidence/CURRENT_PROJECT_CACHE_ELIGIBILITY.json').read_text());prior_groups={g['module']:g for g in initial['groups']};large=json.loads((O/'MANIFEST.json').read_text());cache={x['resolved']:x for x in large['physical_file_identities']};physical={}
def identity(p):
 p=Path(p);s=stat(p);resolved=str(p.resolve());key=(resolved,s['bytes'],s['mtime_ns'],s['ctime_ns'])
 if key in physical:return physical[key]
 old=cache.get(resolved)
 if old and (s['bytes'],s['mtime_ns'],s['ctime_ns'])==(old['bytes'],old['mtime_ns'],old['ctime_ns']):h=old['sha256'];method='DERIVED_STABLE_PREVIOUS_FRESH_QUALIFICATION'
 else:h=sha(p);method='FRESH_SHA256_NEW_OR_CHANGED_RELEVANT_INPUT'
 result=dict(path=str(p),resolved=resolved,sha256=h,method=method,**s);physical[key]=result;return result
state=json.loads(STATE.read_text());core='/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean';runtime={'state':str(STATE),'state_sha256':sha(STATE),'real_lean_sha256':sha(Path(core)),'expected_real_lean_sha256':state['runtime_sha256'][core]};assert runtime['real_lean_sha256']==runtime['expected_real_lean_sha256']
# Producer and consumer use the exact same Member shadow and underlying pinned shared libraries.
libroot=Path(core).parent.parent/'lib/lean';runtime['shared_libraries']=[identity(p) for p in sorted(libroot.glob('*.so')) if p.name.startswith(('libInit','liblean','libLake','libStd'))]
registered=json.loads(Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json').read_text())['project_sources'];suffixes=[('.lake/build/lib/lean/','.olean'),('.lake/build/lib/lean/','.olean.private'),('.lake/build/lib/lean/','.olean.server'),('.lake/build/lib/lean/','.ilean'),('.lake/build/lib/lean/','.ir'),('.lake/build/lib/lean/','.ir.sig'),('.lake/build/lib/lean/','.olean.hash'),('.lake/build/lib/lean/','.ilean.hash'),('.lake/build/ir/','.c'),('.lake/build/ir/','.c.hash')]
log=Path(state['log'])
def source_events():
 es=[]
 for line in log.read_text().splitlines():
  e=json.loads(line);args=e.get('command',[])
  if e.get('tool')=='lean':is_source=any(isinstance(a,str) and a.endswith('.lean') for a in args)
  else:is_source=e.get('tool') in ['clang','leanc','leanir','llvm-ar']
  if is_source:es.append(e)
 return es
all_stages=[]
def adopt(names,stage):
 records=[];nontrace_before={};owned_files=[]
 for short in names:
  mod='ImbalancedChen.'+short;rel='ImbalancedChen/'+short;g=prior_groups[mod];ps=PR/(rel+'.lean');ms=ME/(rel+'.lean');pt=PR/('.lake/build/lib/lean/'+rel+'.trace');mt=ME/('.lake/build/lib/lean/'+rel+'.trace');p_setup=PR/('.lake/build/ir/'+rel+'.setup.json');m_setup=ME/('.lake/build/ir/'+rel+'.setup.json')
  assert sha(ps)==sha(ms)==registered[mod]['sha256']==g['current_source']['sha256']
  assert sha(pt)==g['current_trace']['sha256'];assert not g['blockers'] and g['status']=='FRESH_OWN_COMPILATION_BOUND_TO_CURRENT_INPUTS'
  event=g['actual_guard_command'];assert event['cwd']==str(PR) and event['sysroot']==state['shadow'];assert all(x in event['command'] for x in ['-t0','-j2','-M12288','maxRecDepth=100000','maxHeartbeats=4000000'])
  # Exclude either-end active or queued writer for this specific source.
  active=[]
  for proc in Path('/proc').iterdir():
   if not proc.name.isdigit():continue
   try:argv=[a for a in (proc/'cmdline').read_bytes().decode().split('\0') if a]
   except (FileNotFoundError,ProcessLookupError,PermissionError,UnicodeDecodeError):continue
   if str(ps) in argv or str(ms) in argv:active.append({'pid':proc.name,'argv':argv})
  assert not active,active
  pset=json.loads(p_setup.read_text());mset=json.loads(m_setup.read_text())
  for key in ['plugins','package','options','name','isModule','dynlibs']:assert pset[key]==mset[key],(mod,key)
  assert pset['options']=={} and not pset['plugins'] and not pset['dynlibs'] and pset['isModule'] is False
  assert set(pset['importArts'])==set(mset['importArts'])
  imported=[]
  for imported_mod,arts in pset['importArts'].items():
   oldparts=mset['importArts'][imported_mod]
   assert [len(x) for x in arts]==[len(x) for x in oldparts]
   for part_group,old_group in zip(arts,oldparts):
    for part,oldpart in zip(part_group,old_group):
     assert Path(part).name==Path(oldpart).name,(mod,imported_mod)
     dest=Path(part.replace('/workspace/blue-reindex-build/','/workspace/blue-member-build/').replace('/workspace/blue-p6-build/','/workspace/blue-member-build/'))
     a,b=identity(part),identity(dest);assert a['sha256']==b['sha256'],(mod,imported_mod,part,str(dest));imported.append({'module':imported_mod,'producer':a,'consumer':b,'matched':True})
  p_trace=json.loads(pt.read_text());m_trace=json.loads(mt.read_text());assert p_trace['synthetic'] is False and m_trace['outputs']==p_trace['outputs']
  same=[];missing=[];absent=[]
  for prefix,suffix in suffixes:
   p=PR/(prefix+rel+suffix);m=ME/(prefix+rel+suffix)
   if not p.exists() and not m.exists():absent.append(suffix);continue
   assert p.exists(),('producer facet missing',str(p))
   pi=identity(p)
   if m.exists():
    mi=identity(m);assert pi['sha256']==mi['sha256'],('nontrace existing output mismatch',mod,suffix);same.append({'suffix':suffix,'producer':pi,'consumer':mi})
   else:
    assert suffix in ['.c','.c.hash'],('unexpected missing consumer auxiliary facet',mod,suffix)
    missing.append({'suffix':suffix,'producer':pi,'destination':str(m)})
  assert '.olean' not in absent and '.ilean' not in absent
  c=PR/('.lake/build/ir/'+rel+'.c');ch=PR/('.lake/build/ir/'+rel+'.c.hash');assert c.exists() and ch.exists();assert ch.read_text().strip()+'.c'==p_trace['outputs']['c']
  # Missing authentic C completion is a distinct no-clobber stage before the trace-only stability boundary.
  completed=[]
  for e in missing:
   source=Path(e['producer']['path']);target=Path(e['destination']);payload=source.read_bytes();assert hashlib.sha256(payload).hexdigest()==e['producer']['sha256'];assert not target.exists()
   target.parent.mkdir(parents=True,exist_ok=True)
   with target.open('xb') as out:out.write(payload)
   assert sha(target)==e['producer']['sha256'];completed.append({'suffix':e['suffix'],'path':str(target),'sha256':sha(target),'bytes':target.stat().st_size})
  owned=[ms,m_setup]+[ME/(prefix+rel+suffix) for prefix,suffix in suffixes if (ME/(prefix+rel+suffix)).exists()]
  for f in owned:nontrace_before[str(f)]=sha(f);owned_files.append(f)
  old_bytes=mt.read_bytes();old_stat=stat(mt);old_sha=hashlib.sha256(old_bytes).hexdigest();backup=A/(stage+'-'+short+'-original-Member.trace');backup.write_bytes(old_bytes)
  real_bytes=pt.read_bytes();real_sha=hashlib.sha256(real_bytes).hexdigest();assert real_sha==g['current_trace']['sha256']
  # Recheck source, producer/import identities and exact old trace before atomic replacement.
  assert sha(ps)==sha(ms)==registered[mod]['sha256'];assert stat(mt)==old_stat and sha(mt)==old_sha
  for i in imported:
   for obj in [i['producer'],i['consumer']]:
    f=Path(obj['path']);s=stat(f);assert (s['bytes'],s['mtime_ns'],s['ctime_ns'])==(obj['bytes'],obj['mtime_ns'],obj['ctime_ns']),('input mutated during qualification',str(f))
  temp=mt.with_name(mt.name+'.authentic-producer-adoption.tmp');assert not temp.exists()
  with temp.open('xb') as out:out.write(real_bytes)
  os.replace(temp,mt);assert mt.read_bytes()==pt.read_bytes()==real_bytes
  records.append({'module':mod,'source':identity(ms),'actual_original_guard_event':event,'prior_full_qualification':'/workspace/blue-reindex-build-evidence/CURRENT_PROJECT_CACHE_ELIGIBILITY.json','source_and_runtime_options_match':True,'current_full_actual_import_parts':imported,'own_existing_nontrace_equal_outputs':same,'own_optional_parts_absent_both':absent,'missing_C_completion_before_trace_stability_boundary':completed,'original_trace':{'path':str(mt),'backup':str(backup),'sha256':old_sha,'stat':old_stat},'adopted_authentic_trace':{'source':str(pt),'source_sha256':real_sha,'destination':str(mt),'destination_sha256':sha(mt),'depHash':p_trace['depHash'],'raw_bytes_identical':True,'trace_fields_edited':False,'synthetic_field_edited':False},'setup_written':False,'source_or_proof_written':False})
 for f in owned_files:assert sha(f)==nontrace_before[str(f)]
 write(A/(stage+'-ADOPTION.json'),{'stage':stage,'utc':now(),'runtime':runtime,'groups':records,'nontrace_hashes_after_C_completion_before_adoption':nontrace_before,'nontrace_hashes_stable_after_trace_adoption':True,'original_archive_or_frozen_files_modified':False})
 # Retry exactly the previously failed destination stock batch once after this concrete cache repair.
 old_receipt=json.loads((O/'INSTALL_RECEIPT.json').read_text());argv=old_receipt['stock']['argv'];before=source_events();started=now();t=time.monotonic();logfile=A/(stage+'-stock.log')
 with logfile.open('x') as out:child=subprocess.run(argv,cwd=ME,stdout=out,stderr=subprocess.STDOUT)
 after=source_events();delta=after[len(before):];member=[e for e in delta if e.get('cwd')==str(ME)];others=[e for e in delta if e.get('cwd')!=str(ME)]
 unchanged=all(sha(f)==nontrace_before[str(f)] for f in owned_files);assert unchanged
 restored_stable=all(sha(Path(f['path']))==f['sha256'] for f in old_receipt['installed_files'])
 result={'stage':stage,'argv':argv,'cwd':str(ME),'started_utc':started,'finished_utc':now(),'elapsed_seconds':time.monotonic()-t,'exit_code':child.returncode,'log':str(logfile),'log_sha256':sha(logfile),'Member_source_or_native_compiler_events':member,'Member_source_or_native_compiler_event_count':len(member),'other_project_source_compiler_event_count':len(others),'nontrace_artifacts_stable_from_C_complete_through_adoption_and_stock':unchanged,'original_9_restored_facets_stable':restored_stable,'failed_targets':re.findall(r'^- ([A-Za-z0-9_.]+)$',logfile.read_text(),re.MULTILINE)}
 assert not member and restored_stable
 write(A/(stage+'-STOCK.json'),result);all_stages.append(result);print(json.dumps({k:v for k,v in result.items() if k not in ['argv','Member_source_or_native_compiler_events']},indent=2),flush=True)
 return result
first=adopt(['HalfProductMassFibres','ActualSieveGate'],'stage1')
if first['exit_code']==0:status='PASS_AUTHENTIC_TRACE_ADOPTION_AND_STOCK_NO_MEMBER_SOURCE_CALLS'
elif first['exit_code']==3 and first['failed_targets'] and set(first['failed_targets'])<={'ImbalancedChen.LogCutoffError','ImbalancedChen.PowerErrorBudget'}:
 names=[n.removeprefix('ImbalancedChen.') for n in first['failed_targets']];second=adopt(names,'stage2');status='PASS_AUTHENTIC_TRACE_ADOPTION_AND_STOCK_NO_MEMBER_SOURCE_CALLS' if second['exit_code']==0 else 'FURTHER_STOCK_BLOCKER_REQUIRES_REPORT_NO_ADDITIONAL_ADOPTION'
else:status='FURTHER_STOCK_BLOCKER_REQUIRES_REPORT_NO_ADDITIONAL_ADOPTION'
write(A/'FINAL_RESULT.json',{'status':status,'utc':now(),'stages':all_stages,'only_parent_authorized_suppliers':['HalfProductMassFibres','ActualSieveGate','LogCutoffError','PowerErrorBudget'],'source_proof_setup_or_original_checkpoint_modified':False,'authentic_trace_only_adopted_without_field_edits':True,'separate_missing_C_completion_before_nontrace_stability_boundary':True,'stock_sourcecalls_scoped_to_Member':True});print(status,flush=True)
raise SystemExit(0 if status.startswith('PASS') else 1)
