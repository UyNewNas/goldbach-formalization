from pathlib import Path
import hashlib,json,os,mmap,datetime,re,sys
sys.dont_write_bytecode=True
D=Path(__file__).resolve().parent;PR=Path('/workspace/blue-reindex-build');ME=Path('/workspace/blue-member-build');E=Path('/workspace/blue-reindex-build-evidence')
def sha(p):
 with Path(p).open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
def write(n,d):
 p=D/n;assert not p.exists(),str(p);p.write_text(json.dumps(d,ensure_ascii=False,indent=2)+'\n')
def token(p):
 s=Path(p).stat();return(s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns)
invp=Path('/workspace/p1-complete-proof/modern-frontier-existing-repairs.json');inv=json.loads(invp.read_text());wanted=['ImbalancedChen.P5RealTruncatedMobiusSupport','ImbalancedChen.P5RealCutoffHeathBrownThree'];rows={r['module']:r for r in inv['prototype_repair_candidates']if r['module']in wanted};assert set(rows)==set(wanted)
prior=Path('/workspace/p1-complete-proof/native15-reuse/qualified/MANIFEST.json');prior_install=prior.with_name('INSTALL_RECEIPT.json');prior_install_data=json.loads(prior_install.read_text());prior_token=token(prior)
# Decode only the physical-identity array from existing metadata. Never requalify its15 groups or scan all44k objects.
with prior.open('rb')as f,mmap.mmap(f.fileno(),0,access=mmap.ACCESS_READ)as mm:
 marker=b'"physical_file_identities": ';a=mm.find(marker);assert a>=0;tail=mm[a+len(marker):].decode();oldids,_=json.JSONDecoder().raw_decode(tail)
assert token(prior)==prior_token
cache={x['resolved']:x for x in oldids};del oldids,tail
physical={};all_tokens={};methods={}
def identity(path):
 p=Path(path);r=str(p.resolve());st=token(p)
 if r in physical:
  assert all_tokens[r]==st,'RELEVANT_INPUT_CHANGED:'+r;return r
 old=cache.get(r)
 if old and(st[2],st[3],st[4])==(old['bytes'],old['mtime_ns'],old['ctime_ns']):
  h=old['sha256'];method='DERIVED_NATIVE15_SHA256_SAME_RESOLVED_FILE_UNCHANGED_SIZE_MTIME_CTIME'
 else:h=sha(p);assert token(p)==st;method='FRESH_SHA256_ONLY_NEW_OR_CHANGED_RELEVANT_FILE'
 physical[r]={'resolved':r,'bytes':st[2],'sha256':h,'dev':st[0],'ino':st[1],'mtime_ns':st[3],'ctime_ns':st[4],'method':method,'prior_receipt':str(prior)if old and method.startswith('DERIVED')else None};all_tokens[r]=st;methods[method]=methods.get(method,0)+1;return r
def ident(path):return physical[identity(path)]
statep=Path('/workspace/blue-build-tools/member-runtime-evidence/state.json');state=json.loads(statep.read_text());state_sha=sha(statep);assert state_sha=='9f0688f701d861e3af832a1ab17d8d0fab41c1d30a3261f24922cae058e7b152'
runtime=[]
for p,h in state['runtime_sha256'].items():
 x=ident(p);assert x['sha256']==h,p;runtime.append({'path':p,'identity_key':x['resolved'],'expected_state_sha256':h})
# Existing normal/kernel/std3 receipts are read and bound, never re-executed.
kernp=E/'KERNEL_REPLAY_RECEIPT.json';kern=json.loads(kernp.read_text());auditp=E/'PUBLIC_AUDIT_RECEIPT.json';audit=json.loads(auditp.read_text());assert kern['status']=='PASS_NATIVE_NAMED_MODULE_KERNEL_REPLAY'and kern['target_object_hashes_unchanged'];assert audit['exit_code']==0and not audit['unexpected_axioms']and not audit['contains_sorryAx'];assert kern['guard_state_sha256']==audit['guard_state_sha256']==state_sha
# Read just the two named producer events from guarded logs; no wrapper/compiler command is run.
events={m:[]for m in wanted}
for logp in [Path('/workspace/blue-build-tools/member-runtime-evidence/compiler-commands.jsonl'),Path('/workspace/blue-build-tools/reindex-runtime-evidence/compiler-commands.jsonl')]:
 with logp.open('rb')as f:
  off=0
  for line in f:
   if any(('/ImbalancedChen/'+m.split('.')[-1]+'.lean').encode()in line for m in wanted):
    e=json.loads(line)
    if e.get('tool')=='lean'and e.get('cwd')==str(PR):
     for mod in wanted:
      if str(PR/(mod.replace('.','/')+'.lean'))in e.get('command',[]):events[mod].append({'log':str(logp),'byte_offset':off,'raw_line_sha256':hashlib.sha256(line).hexdigest(),'event':e})
   off+=len(line)
groups={};checks={};current_destination_tokens={}
for mod in wanted:
 r=rows[mod];rel=mod.replace('.','/');sp=PR/(rel+'.lean');mp=ME/(rel+'.lean');src=ident(sp);curr=ident(mp);post=r['original_selection_entry']['sha256'];pre=r['current_exact_preimage']['sha256'];assert src['sha256']==post and curr['sha256']==pre and post!=pre
 assert (E/'verified-isolated-closure/postimages'/ (rel+'.lean')).read_bytes()==sp.read_bytes()
 assert not re.search(r'\b(include_str|include_bytes|__dir__|__file__|readFile|readBinFile)\b',sp.read_text(),re.I)
 setp=PR/('.lake/build/ir/'+rel+'.setup.json');tp=PR/('.lake/build/lib/lean/'+rel+'.trace');setup=json.loads(setp.read_text());trace=json.loads(tp.read_text());assert setup['name']==mod and setup['options']=={}and setup['plugins']==[]and setup['dynlibs']==[]and setup['isModule']is False;assert setup['package']=='imbalancedChen';assert trace['synthetic']is False and trace['schemaVersion']=='2025-09-10'and not any(x.get('level')=='error'for x in trace['log'])
 traces='\n'.join(x.get('message','')for x in trace['log']);matches=[e for e in events[mod]if ' '.join([e['event']['sysroot']+'/bin/lean']+e['event']['input_args'])in traces];assert matches,mod;producer=matches[-1];ev=producer['event'];assert ev['sysroot']==state['shadow']and ev['command'][0]==state['shadow']+'/bin/lean-runtime';assert all(x in ev['command']for x in ['-t0','-j2','-M12288','maxRecDepth=100000','maxHeartbeats=4000000']);assert any(x[0]=='Module.leanArgs: #[-DmaxRecDepth=100000, -DmaxHeartbeats=4000000]'for x in trace['inputs']);assert any(x[0]=='Lean 4.33.0, commit 62eed1db4d67327ec8120be05f1a1b0847d74561'for x in trace['inputs'])
 # All actual importArts parts, including server/private/IR when present, are compared by physical SHA.
 keys=[];deps=set();block=[]
 for imported,parts in setup['importArts'].items():
  for part in parts:
   for pp in part:
    producer_id=identity(pp);dst=Path(pp.replace(str(PR)+'/',str(ME)+'/'));key=pp+' -> '+str(dst)
    if imported in wanted:
     assert imported!=mod;provider='PROSPECTIVE_POST_GROUP_NOT_CURRENT_SOURCE';proposed=PR/('.lake/build/lib/lean/'+imported.replace('.','/')+Path(pp).name[len(imported.split('.')[-1]):]);provider_id=identity(proposed);ok=physical[producer_id]['sha256']==physical[provider_id]['sha256'];deps.add(imported)
     if dst.exists():current=ident(dst);currently_matched=current['sha256']==physical[producer_id]['sha256']
     else:current=None;currently_matched=False
    else:
     provider='EXISTING_SHARED_PHYSICAL_IMPORT';provider_id=identity(dst);ok=physical[producer_id]['sha256']==physical[provider_id]['sha256'];current=physical[provider_id];currently_matched=ok
    checks.setdefault(key,{'module':imported,'producer_path':pp,'prospective_Member_path':str(dst),'producer_identity_key':producer_id,'prospective_provider_identity_key':provider_id,'provider':provider,'matched_for_proposed_post_context':ok,'current_destination_part_matched':currently_matched,'current_destination_identity_key':current['resolved']if current else None});keys.append(key)
    if not ok:block.append('IMPORTED_PART_SHA_MISMATCH:'+key)
 facets=[];dest_conflicts=[]
 for prefix,suffix in [('.lake/build/lib/lean/','.olean'),('.lake/build/lib/lean/','.olean.private'),('.lake/build/lib/lean/','.olean.server'),('.lake/build/lib/lean/','.ilean'),('.lake/build/lib/lean/','.ir'),('.lake/build/lib/lean/','.ir.sig'),('.lake/build/lib/lean/','.olean.hash'),('.lake/build/lib/lean/','.ilean.hash'),('.lake/build/ir/','.c'),('.lake/build/ir/','.c.hash'),('.lake/build/ir/','.setup.json'),('.lake/build/lib/lean/','.trace')]:
  p=PR/(prefix+rel+suffix);d=ME/(prefix+rel+suffix)
  if p.exists():
   ii=identity(p);status='ABSENT'
   if d.exists():status='EXISTING_EQUAL_PRESERVE'if ident(d)['sha256']==physical[ii]['sha256']else'EXISTING_DIFFERING_DO_NOT_OVERWRITE'
   current_destination_tokens[str(d)]=token(d)if d.exists()else None
   if status=='EXISTING_DIFFERING_DO_NOT_OVERWRITE':dest_conflicts.append(str(d))
   facets.append({'relative_path':prefix+rel+suffix,'producer_path':str(p),'destination_path':str(d),'identity_key':ii,'current_destination_status':status})
 assert all(any(f['relative_path']==prel+rel+suf for f in facets)for prel,suf in [('.lake/build/lib/lean/','.olean'),('.lake/build/lib/lean/','.ilean'),('.lake/build/lib/lean/','.trace'),('.lake/build/ir/','.c'),('.lake/build/ir/','.c.hash'),('.lake/build/ir/','.setup.json')])
 for suffix,tag in [('.olean','o'),('.ilean','i'),('.c','c')]:
  p=PR/(('.lake/build/ir/'if suffix=='.c'else'.lake/build/lib/lean/')+rel+suffix+'.hash');h=p.read_text().strip();expected=trace['outputs'][tag][0].split('.')[0]if tag=='o'else trace['outputs'][tag].split('.')[0];assert h==expected,(mod,suffix)
 own=ident(PR/('.lake/build/lib/lean/'+rel+'.olean'));assert kern['target_objects'][mod]['sha256']==own['sha256'];kr=next(x for x in kern['results']if x['module']==mod);assert kr['exit_code']==0and sha(kr['log'])==kr['log_sha256'];assert audit['per_module_public_export_counts'][mod]==r['existing_validation']['actual_public_export_count']
 groups[mod]={'proposed_source_post_sha256':post,'proposed_source_identity_key':src['resolved'],'actual_current_source_pre_sha256':pre,'actual_current_source_identity_key':curr['resolved'],'current_source_is_not_adopted_post':True,'setup_identity_key':identity(setp),'trace_identity_key':identity(tp),'setup_configuration':{k:setup[k]for k in ['plugins','package','options','name','isModule','dynlibs']},'original_trace_synthetic':False,'original_trace_depHash':trace['depHash'],'original_trace_outputs':trace['outputs'],'producer_trace_matching_guard_event':producer,'prospective_dependencies':sorted(deps),'actual_import_keys':keys,'import_modules':len(setup['importArts']),'actual_import_part_occurrences':len(keys),'blockers':block,'facets':facets,'currently_differing_destination_facets_blocking_no_clobber':dest_conflicts,'prior_kernel_object_sha_bound':own['sha256'],'prior_kernel_result':kr,'prior_actual_public_exports':audit['per_module_public_export_counts'][mod],'existing_validation':r['existing_validation'],'native_executable_facets_excluded':True}
# Conditional fixed point; current source mismatch is explicitly a future adoption gate, never bypassed.
eligible={m for m,g in groups.items()if not g['blockers']and not g['currently_differing_destination_facets_blocking_no_clobber']}
while True:
 nxt={m for m in eligible if set(groups[m]['prospective_dependencies'])<=eligible}
 if nxt==eligible:break
 eligible=nxt
contradictions=[]
for p,st in all_tokens.items():
 if token(p)!=st:contradictions.append(p)
for p,st in current_destination_tokens.items():
 q=Path(p);now=token(q)if q.exists()else None
 if now!=st:contradictions.append(p)
assert not contradictions,contradictions
for m,g in groups.items():g['conditional_proposed_post_eligible']=m in eligible;g['currently_installable']=False;g['actual_source_accepted_in_Member']=False
write('PHYSICAL_IDENTITIES.json',{'schema':'two_group_relevant_physical_SHA_stat_bindings_v1','files':list(physical.values())});write('IMPORT_PART_CHECKS.json',{'schema':'two_group_actual_setup_all_parts_v1','checks':checks});write('PRODUCER_EVENTS.json',{'matching_successful_trace_events':{m:groups[m]['producer_trace_matching_guard_event']for m in wanted}})
summary={'candidate_groups':2,'conditionally_eligible_if_both_post_sources_adopted_at_owner_window':sorted(eligible),'currently_installable_groups':0,'actual_source_adoptions':0,'installed_facets':0,'unique_actual_import_pairs':len(checks),'actual_import_part_occurrences_across_two_setups':sum(g['actual_import_part_occurrences']for g in groups.values()),'unmatched_proposed_import_parts':sum(not c['matched_for_proposed_post_context']for c in checks.values()),'prospective_project_import_parts':sum(c['provider'].startswith('PROSPECTIVE')for c in checks.values()),'physical_SHA_methods':methods,'source_options':'maxRecDepth100000,maxHeartbeats4000000;setup{};no plugins/dynlibs;legacy isModulefalse','runtime':'Existing original exact Member stateSHA and actual t0,j2,M12288 producer events; current binaries rechecked against original recorded runtime SHA.','input_snapshot_contradictions':contradictions,'whole44k_617_or_native15_group_qualification_repeated':False,'compiler_kernel_type_axiom_stock_commands_run':0,'native_o_so_exe_facets_eligible':False,'conditional_install_order':wanted}
manifest={'schema':'two_Prototype_known_post_conditional_proposed_source_object_qualification_v1','status':'CONDITIONAL_PROPOSED_POST_CONTEXT_ONLY_NOT_CURRENTLY_INSTALLABLE','captured_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'groups':groups,'summary':summary,'runtime_state':{'path':str(statep),'sha256':state_sha,'same_as_existing_normal_kernel_and_audit_state':True,'runtime_physical_checks':runtime,'state_policy':state['policy']},'prior_SHA_cache':{'manifest':str(prior),'previous_recorded_manifest_sha256':prior_install_data['qualification_manifest_sha256'],'hash_origin_receipt':str(prior_install),'hash_origin_receipt_sha256':sha(prior_install),'manifest_full_hash_not_recomputed':True,'only_physical_identity_array_decoded':True,'manifest_stat_snapshot':prior_token,'manifest_stat_unchanged_after_read':token(prior)==prior_token,'no_old_groups_requalified':True},'evidence_inputs':{str(p):sha(p)for p in [invp,Path('/workspace/p1-complete-proof/prototype-two-known-post-object-precheck/PRECHECK.json'),kernp,auditp,E/'FINAL_TRIAL_RECEIPT.json',E/'EXACT_SELECTION.json']},'additional_files':{n:sha(D/n)for n in ['PHYSICAL_IDENTITIES.json','IMPORT_PART_CHECKS.json','PRODUCER_EVENTS.json']},'mutations':{'only_new_qualification_evidence_files_under_this_directory':True,'current_source_not_adopted':True,'proofs_not_recreated':True,'source_artifact_trace_hash_facet_installs':False,'native_executable_installs':False,'controllers_signals_locks_or_process_changes':False,'compiler_guard_policies_changed':False,'Lean_Lake_checker_audit_or_stock_invoked':False},'strict_future_conditions':['Owner first explicitly releases a stable source+object window after actual target failure has ended or controller natural quiescence; no active/queued/unknown internal-DAG mutation.','Owner adopts exactly these2 previously verified post source payloads; this proposed-source qualification does not itself authorize or perform adoption.','At use time repeat source/runtime/options/producer facet/all actual imported-part SHA-or-unchanged-stat checks, plus complete no-clobber destination checks and stability checks.','Install dependency order Mobius then HBThree, with original trace/hash/source bytes unchanged. Abort on differing existing facets; never rebase trace labels/hashes.','Only owner may run stock --no-build target scope under the existing guard after gate release, verify0 Member source events and unchanged installed facets. No stock outcome is predicted or fabricated.'],'limitations':['Current Member sources remain original preimages, so neither group is presently eligible for installation.','Actual local stock readiness/receipt is intentionally absent.','Prior normal/kernel/std3 evidence belongs to Prototype exact post context, not automatic Member acceptance.','All qualification facts are bounded snapshots; current active modern DAG queue is deliberately not inferred from /proc absence.']}
write('MANIFEST.json',manifest);write('SUMMARY.json',summary)
print(json.dumps({'directory':str(D),'manifest_sha256':sha(D/'MANIFEST.json'),'summary':summary},ensure_ascii=False,indent=2))
