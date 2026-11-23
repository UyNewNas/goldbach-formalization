from pathlib import Path
import datetime,hashlib,json,time,subprocess
R=Path('/workspace/blue-member-aggregate-evidence');O=R/'prototype-qualified';M=Path('/workspace/blue-member-build');STATE=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json')
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def save_status(x):write(O/'INSTALL_RECEIPT.json',x)
print(json.dumps({'status':'WAITING_QUIESCENT_COPY_WINDOW','utc':now()}),flush=True)
while not (R/'REUSE_WINDOW_OPEN.json').exists():time.sleep(2)
q=json.loads((O/'MANIFEST.json').read_text());groups=q['groups'];pairs={x['producer_path']+' -> '+x['destination_path']:x for x in q['actual_import_checks']};qualified=set(q['qualified_modules']);existing=[];wanted=set();blocked={};stats={};raw_checks={}
owner=Path('/workspace/blue-reindex-build-evidence/MEMBER_REUSE_PRODUCER_PROVENANCE.json');assert owner.exists()
producer_stock=json.loads((R/'PROTOTYPE_35_PRODUCER_STOCK.json').read_text());assert producer_stock['exit_code']==0
# Reuse exact existing digests only on unchanged physical file stats. Rehash changed/new relevant files once, never a whole old common cache.
def check(p,expected):
 p=Path(p)
 raw_key=(str(p),expected['sha256'])
 if raw_key in raw_checks:return raw_checks[raw_key]
 if not p.exists():return False
 st=p.stat();resolved=str(p.resolve());key=(resolved,st.st_size,st.st_mtime_ns,st.st_ctime_ns)
 if key in stats:h=stats[key]['sha256']
 elif resolved==expected['resolved'] and (st.st_size,st.st_mtime_ns,st.st_ctime_ns)==(expected['bytes'],expected['mtime_ns'],expected['ctime_ns']):
  h=expected['sha256'];stats[key]={'resolved':resolved,'sha256':h,'bytes':st.st_size,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns,'method':'DERIVED_PRIOR_QUALIFICATION_UNCHANGED_FILE'}
 else:
  h=sha(p);stats[key]={'resolved':resolved,'sha256':h,'bytes':st.st_size,'mtime_ns':st.st_mtime_ns,'ctime_ns':st.st_ctime_ns,'method':'FRESH_SHA256_CHANGED_OR_NEW_RELEVANT_FILE'}
 raw_checks[raw_key]=(h==expected['sha256'])
 return raw_checks[raw_key]
for mod in sorted(qualified):
 g=groups[mod];olean=next(f for f in g['facets'] if f['relative_path'].endswith('.olean'))
 if Path(olean['destination_path']).exists():existing.append({'module':mod,'status':'ALREADY_HAS_DESTINATION_OLEAN_NOT_OVERWRITTEN'});continue
 wanted.add(mod);reasons=[]
 source=Path(g['destination_source']['resolved'])
 if sha(source)!=g['source_sha256']:reasons.append('DESTINATION_SOURCE_CHANGED')
 for f in g['facets']:
  if not check(f['source_path'],f['identity']):reasons.append('PRODUCER_FACET_CHANGED:'+f['source_path'])
  d=Path(f['destination_path'])
  if d.exists() and sha(d)!=f['identity']['sha256']:reasons.append('NO_CLOBBER_EXISTING_FACET_CONFLICT:'+str(d))
 for key in g['actual_import_keys']:
  c=pairs[key]
  if not check(c['producer_path'],c['producer_identity']):reasons.append('PRODUCER_IMPORT_CHANGED:'+c['producer_path']);continue
  d=Path(c['destination_path'])
  if d.exists():
   if not check(d,c['producer_identity']):reasons.append('DESTINATION_IMPORT_BYTES_DIFFER:'+str(d))
  elif c['module'] not in qualified:reasons.append('MISSING_NONQUALIFIED_PROVIDER:'+c['module'])
 if reasons:blocked[mod]=sorted(set(reasons))
eligible=wanted-set(blocked)
changed=True
while changed:
 new=set()
 for mod in eligible:
  good=True
  for key in groups[mod]['actual_import_keys']:
   c=pairs[key]
   if not Path(c['destination_path']).exists() and c['module'] not in eligible:good=False;break
  if good:new.add(mod)
 changed=new!=eligible;eligible=new
order=[];visiting=set();visited=set()
def visit(m):
 if m in visited:return
 assert m not in visiting,'Unexpected cycle'
 visiting.add(m)
 for dep in groups[m]['prospective_dependencies']:
  if dep in eligible:visit(dep)
 visiting.remove(m);visited.add(m);order.append(m)
for mod in sorted(eligible):visit(mod)
installed=[]
for mod in order:
 for f in groups[mod]['facets']:
  s=Path(f['source_path']);d=Path(f['destination_path']);payload=s.read_bytes();h=hashlib.sha256(payload).hexdigest();assert h==f['identity']['sha256']
  if d.exists():assert sha(d)==h;continue
  d.parent.mkdir(parents=True,exist_ok=True)
  with d.open('xb') as out:out.write(payload)
  assert sha(d)==h
  installed.append({'module':mod,'path':str(d),'bytes':len(payload),'sha256':h})
receipt={'status':'COPY_COMPLETE_WAITING_EXTERNAL_GATE_RELEASE_FOR_STOCK','started_and_copied_utc':now(),'producer_owner_stability_receipt':str(owner),'producer_owner_stability_receipt_sha256':sha(owner),'qualification_manifest_sha256':sha(O/'MANIFEST.json'),'initial_eligible_modules':sorted(qualified),'already_existing_modules_not_overwritten':existing,'copy_eligible_at_window':order,'blocked_before_copy':blocked,'recursively_blocked_at_window':sorted(wanted-eligible-set(blocked)),'installed_files':installed,'window_input_rechecks':list(stats.values()),'source_files_modified':False,'prototype_files_modified':False,'native_executables_installed':False,'no_clobber':True}
save_status(receipt);write(O/'COPY_COMPLETE.json',{'status':'COPY_COMPLETE','utc':now(),'groups':order,'project_groups':sum(groups[m]['kind']=='project' for m in order),'native_groups':sum(groups[m]['kind']=='native' for m in order),'files':len(installed),'receipt':'INSTALL_RECEIPT.json'})
print(json.dumps({'status':'COPY_COMPLETE','modules':order,'files':len(installed),'blocked':{m:r[:1] for m,r in blocked.items()}}),flush=True)
while not (R/'STOCK_RELEASED.json').exists():time.sleep(1)
if order:
 state=json.loads(STATE.read_text());logpath=Path(state['log'])
 def source_events():
  es=[]
  for line in logpath.read_text().splitlines():
   e=json.loads(line)
   if e.get('tool')=='lean' and any(a.endswith('.lean') for a in e.get('command',[]) if isinstance(a,str)):es.append(e)
  return es
 before=source_events();identities_before={f['path']:sha(Path(f['path'])) for f in installed};cmd=['python3','/workspace/blue-build-tools/run_guarded.py','--state',str(STATE),'lake','--no-build','build']+[('+'+m+':olean') if groups[m]['kind']=='project' else ('@goldbach/+'+m+':olean') for m in order];t=time.monotonic();started=now()
 with (O/'member-stock.log').open('x') as out:child=subprocess.run(cmd,cwd=M,stdout=out,stderr=subprocess.STDOUT)
 after=source_events();delta=after[len(before):];own=[e for e in delta if e.get('cwd')==str(M)];other=[e for e in delta if e.get('cwd')!=str(M)];identities_after={f['path']:sha(Path(f['path'])) for f in installed}
 receipt['stock']={'argv':cmd,'cwd':str(M),'exit_code':child.returncode,'started_utc':started,'finished_utc':now(),'elapsed_seconds':time.monotonic()-t,'log':'member-stock.log','log_sha256':sha(O/'member-stock.log'),'stock_no_build_enforced':True,'Member_source_compiler_calls':len(own),'other_project_source_compiler_calls':len(other),'installed_facets_unchanged':identities_before==identities_after,'member_scope_events':own}
 receipt['status']='REUSED_PORTABLE_GROUPS_STOCK_EXIT0_MEMBER_SOURCECALLS0' if child.returncode==0 and not own and identities_before==identities_after else 'COPIED_GROUPS_STOCK_COMPATIBILITY_DIAGNOSIS_REQUIRED'
else:receipt['status']='NO_GROUPS_STILL_MISSING_AND_ELIGIBLE_AT_WINDOW'
receipt['finished_utc']=now();save_status(receipt);write(O/'STOCK_COMPLETE.json',{'status':receipt['status'],'utc':now(),'stock_exit_code':receipt.get('stock',{}).get('exit_code'),'Member_source_compiler_calls':receipt.get('stock',{}).get('Member_source_compiler_calls',0),'groups_installed':order,'receipt':'INSTALL_RECEIPT.json'})
print(json.dumps({'status':receipt['status'],'stock':receipt.get('stock'),'groups':order}),flush=True)
