from pathlib import Path
import hashlib,json,os,datetime
R=Path('/workspace/blue-member-aggregate-evidence');OUT=R/'prototype-qualified';OUT.mkdir(exist_ok=True)
PR=Path('/workspace/blue-reindex-build');ME=Path('/workspace/blue-member-build')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
project=json.loads((R/'PROTOTYPE_PROJECT_REUSE_CANDIDATES.json').read_text())['Member_missing_Prototype_present'];native=json.loads((R/'PROTOTYPE_NATIVE_REUSE_CANDIDATES.json').read_text())['candidates'];items={x['module']:x for x in project+native};events=json.loads((R/'PROTOTYPE_FRESH_PRODUCER_EVENTS.json').read_text())
registered=json.loads(Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json').read_text())
# Reuse prior physical SHA identities only when their actual file stats are unchanged.
cache={}
def add(path,h,size,mtime,ctime,origin,dev=None,ino=None):cache.setdefault(str(Path(path).resolve()),[]).append((h,size,mtime,ctime,origin,dev,ino))
prior=Path('/workspace/artifacts/cdc-qualified-member/INSTALL_RECEIPT.json');x=json.loads(prior.read_text())
for e in x['import_checks']:
 if e.get('matched') and all(k in e for k in ['resolved','sha256','bytes','mtime_ns','ctime_ns']):add(e['resolved'],e['sha256'],e['bytes'],e['mtime_ns'],e['ctime_ns'],str(prior))
pp=Path('/workspace/blue-reindex-build-evidence/CURRENT_PROJECT_CACHE_PHYSICAL_INPUTS.json');x=json.loads(pp.read_text())
for e in x['files']:
 i=e['identity'];st=e['stat_snapshot'];add(i['path'],i['sha256'],i['bytes'],st[3],st[4],str(pp),st[0],st[1])
physical={}
def identity(p):
 p=Path(p);resolved=str(p.resolve());st=p.stat();key=(resolved,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 if key in physical:return physical[key]
 for h,size,mt,ct,origin,dev,ino in cache.get(resolved,[]):
  if (size,mt,ct)==(st.st_size,st.st_mtime_ns,st.st_ctime_ns) and (dev is None or (dev,ino)==(st.st_dev,st.st_ino)):
   result={'resolved':resolved,'bytes':st.st_size,'sha256':h,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns,'method':'DERIVED_EXISTING_SHA256_SAME_PHYSICAL_FILE_UNCHANGED_STATS','prior_receipt':origin};break
 else:result={'resolved':resolved,'bytes':st.st_size,'sha256':sha(p),'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns,'method':'FRESH_SHA256_NEW_PROSPECTIVE_REUSE_INPUT'}
 physical[key]=result;return result
mstate=json.loads(Path('/workspace/blue-build-tools/member-runtime-evidence/state.json').read_text());core='/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean';groups={};checks={}
for mod,item in items.items():
 isproject=mod.startswith('ImbalancedChen.');base=PR if isproject else PR/'.lake/packages/goldbach';dest=ME if isproject else ME/'.lake/packages/goldbach';rel=mod.replace('.','/');src=base/(rel+'.lean');msrc=dest/(rel+'.lean');setup_path=base/('.lake/build/ir/'+rel+'.setup.json');trace_path=base/('.lake/build/lib/lean/'+rel+'.trace');setup=json.loads(setup_path.read_text());trace=json.loads(trace_path.read_text());block=[]
 expected=registered['project_sources' if isproject else 'native_sources'][mod]['sha256']
 source_identity=identity(src);msource_identity=identity(msrc)
 if source_identity['sha256']!=msource_identity['sha256'] or source_identity['sha256']!=expected:block.append('SOURCE_MISMATCH')
 assert setup['name']==mod
 if setup['options']!={} or setup['plugins'] or setup['dynlibs'] or setup['isModule'] is not False:block.append('UNEXPECTED_SETUP_CONFIGURATION')
 text='\n'.join(e.get('message','') for e in trace['log']);matching=[e for e in events[mod] if e['event']['sysroot']+'/bin/lean' in text]
 if not matching:block.append('NO_MATCHING_ORIGINAL_GUARD_EVENT');producer=None
 else:
  producer=matching[-1];event=producer['event'];state=json.loads(Path(producer['state']).read_text());args=event['command']
  if '-t0' not in args:block.append('PRODUCER_NOT_TRUST0')
  if state['runtime_sha256'][core]!=mstate['runtime_sha256'][core]:block.append('COMPILER_BINARY_MISMATCH')
  if isproject and not all(v in args for v in ['maxRecDepth=100000','maxHeartbeats=4000000']):block.append('PROJECT_SOURCE_OPTION_ARGS_MISMATCH')
 if any(e.get('level')=='error' for e in trace['log']):block.append('PRODUCER_TRACE_HAS_ERROR')
 deps=set();import_ids=[]
 for imported,arts in setup['importArts'].items():
  for facet_group in arts:
   for name in facet_group:
    target=Path(name.replace('/workspace/blue-reindex-build/','/workspace/blue-member-build/').replace('/workspace/blue-p6-build/','/workspace/blue-member-build/'))
    key=(name,str(target));sid=identity(name)
    if target.exists():
     tid=identity(target);ok=sid['sha256']==tid['sha256'];provider='EXISTING_DESTINATION_ACTUAL_OBJECT';detail=None
    elif imported in items:
     pbase=PR if imported.startswith('ImbalancedChen.') else PR/'.lake/packages/goldbach';suffix=name.split('/.lake/build/lib/lean/',1)[1] if '/.lake/build/lib/lean/' in name else None
     proposed=pbase/('.lake/build/lib/lean/'+suffix) if suffix else None
     if proposed is None or not proposed.exists():ok=False;tid=None;detail='CANDIDATE_PROVIDER_FACET_MISSING'
     else:tid=identity(proposed);ok=sid['sha256']==tid['sha256'];detail=None;deps.add(imported)
     provider='PROSPECTIVE_SELECTED_GROUP'
    else:ok=False;tid=None;provider='MISSING_DESTINATION_NONCANDIDATE_PROVIDER';detail=imported
    check={'module':imported,'producer_path':name,'destination_path':str(target),'producer_identity':sid,'destination_or_selected_provider_identity':tid,'provider':provider,'matched':ok,'detail':detail}
    if key not in checks:checks[key]=check
    idx=list(checks).index(key) if False else name+' -> '+str(target)
    import_ids.append(idx)
    if not ok:block.append('IMPORT_FACET_BLOCKED:'+idx)
 facets=[]
 for prefix,suffix in [('.lake/build/lib/lean/','.olean'),('.lake/build/lib/lean/','.olean.private'),('.lake/build/lib/lean/','.olean.server'),('.lake/build/lib/lean/','.ilean'),('.lake/build/lib/lean/','.ir'),('.lake/build/lib/lean/','.ir.sig'),('.lake/build/lib/lean/','.olean.hash'),('.lake/build/lib/lean/','.ilean.hash'),('.lake/build/ir/','.c'),('.lake/build/ir/','.c.hash'),('.lake/build/ir/','.setup.json'),('.lake/build/lib/lean/','.trace')]:
  p=base/(prefix+rel+suffix)
  if p.exists():facets.append({'relative_path':prefix+rel+suffix,'source_path':str(p),'destination_path':str(dest/(prefix+rel+suffix)),'identity':identity(p)})
 for suffix in ['.olean','.ilean','.trace']:
  if not any(e['relative_path'].endswith(rel+suffix) for e in facets):block.append('INCOMPLETE_PORTABLE_GROUP:'+suffix)
 groups[mod]={'kind':'project' if isproject else 'native','source':source_identity,'destination_source':msource_identity,'source_sha256':expected,'setup_path':str(setup_path),'setup_identity':identity(setup_path),'setup_options':setup['options'],'isModule':setup['isModule'],'producer':producer,'source_runtime_resource_profile_recorded_without_executable_reuse':True,'producer_trace_identity':identity(trace_path),'prospective_dependencies':sorted(deps-{mod}),'actual_import_keys':import_ids,'blockers':sorted(set(block)),'facets':facets}
# Recursive exact-input eligibility; a prospective importer cannot bypass a blocked supplier.
eligible={m for m,g in groups.items() if not g['blockers']}
changed=True
while changed:
 new={m for m in eligible if set(groups[m]['prospective_dependencies'])<=eligible};changed=new!=eligible;eligible=new
for mod,g in groups.items():g['qualified_for_no_clobber_window']=mod in eligible
manifest={'schema':'prototype-member-local-portable-reuse-qualification-v1','captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Read-only qualification only; installation waits old controller natural handoff','groups':groups,'actual_import_checks':list(checks.values()),'physical_file_identities':list(physical.values()),'summary':{'candidate_groups':len(groups),'project_candidates':len(project),'native_candidates':len(native),'eligible_project':sum(groups[m]['kind']=='project' for m in eligible),'eligible_native':sum(groups[m]['kind']=='native' for m in eligible),'unique_actual_import_pairs':len(checks),'unmatched_import_pairs':sum(not c['matched'] for c in checks.values()),'physical_objects_with_prior_SHA_derived':sum(x['method'].startswith('DERIVED') for x in physical.values()),'fresh_SHA_files':sum(x['method'].startswith('FRESH') for x in physical.values()),'old_CDC617_groups_requalified':False,'whole44k_hash_scan_repeated':False},'qualified_modules':sorted(eligible),'native_executables_eligible':False,'producer_stock_receipt':'../PROTOTYPE_35_PRODUCER_STOCK.json','installation_done':False}
write(OUT/'MANIFEST.json',manifest);write(OUT/'SUMMARY.json',manifest['summary']);print(json.dumps(manifest['summary'],indent=2));print('blocked',[(m,len(g['blockers']),g['blockers'][:1]) for m,g in groups.items() if m not in eligible])
