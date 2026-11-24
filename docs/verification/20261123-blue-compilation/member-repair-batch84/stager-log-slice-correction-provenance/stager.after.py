from pathlib import Path
import json,hashlib,re,difflib,shutil,sys
cfg=json.loads(Path(sys.argv[1]).read_text());R=Path(cfg['packet']);R.mkdir();P=Path('/workspace/blue-member-build');MAIN=Path('/workspace/goldbach-formalization');selected=json.loads(Path('/workspace/blue-member-build-evidence/SELECTED_MEMBER_SOURCES.json').read_text());rows={};exceptions={}
def sha(b):return hashlib.sha256(b).hexdigest()
for item in cfg['items']:
 mod=item['module']
 if mod not in selected['project_sources']:
  extra_path=Path(cfg['exact_additional_selected_source_manifest']);extra=json.loads(extra_path.read_text());entry=extra['selected_project_sources'][mod];assert entry['source_sha256']==item['preimage_sha256'],('additional_context_preimage',mod)
 rel=mod.replace('.','/')+'.lean';target=P/rel;main=MAIN/rel;oldb=target.read_bytes();cb=Path(item['candidate']).read_bytes();assert sha(oldb)==item['preimage_sha256'];assert sha(cb)==item['candidate_sha256'];old=oldb.decode();new=cb.decode();replacements=[]
 for label in ([] if (item.get('preserve_complete_published_source_bytes',False) or item.get('preserve_candidate_source_bytes',False)) else item.get('neutral_labels',[])):
  n=new.count(label)
  if n:new=new.replace(label,'Verification records: docs/verification/20261123-blue-compilation.');replacements.append({'before':label,'after':'Verification records: docs/verification/20261123-blue-compilation.','count':n})
 header=new.split('\nnamespace ',1)[0];assert item.get('preserve_complete_published_source_bytes',False) or item.get('preserve_candidate_source_bytes',False) or 'UNCOMPILED' not in header,('unneutralized module status',mod)
 for proc in Path('/proc').iterdir():
  if not proc.name.isdigit():continue
  try:a=[x for x in (proc/'cmdline').read_bytes().decode().split('\0') if x]
  except Exception:continue
  assert str(target) not in a,('active_or_queued_source_writer',proc.name,mod)
 sync=main.exists() and main.read_bytes()==oldb
 if main.exists() and not sync:exceptions[mod]={'preserved_actual_main_sha256':sha(main.read_bytes()),'reason':'Different canonical source preimage; source-owner scope permits sync only identical baselines. Actual build uses isolated selected Member source.'}
 z=R/mod.split('.')[-1];z.mkdir();(z/'baseline.lean').write_bytes(oldb);(z/'candidate.lean').write_bytes(new.encode());(z/'static-candidate-before-owner-comment.lean').write_bytes(cb);(z/'candidate.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='baseline/'+rel,tofile='candidate/'+rel)));pro=z/'static-provenance';pro.mkdir()
 for n in item.get('provenance',[]):
  source=Path(n);assert source.exists();shutil.copyfile(source,pro/source.name)
 post=sha(new.encode());record={'module':mod,'preimage_sha256':sha(oldb),'postimage_sha256':post,'static_candidate_before_owner_comment_sha256':sha(cb),'static_candidate':item['candidate'],'complete_published_source_byte_exact_preserved':item.get('preserve_complete_published_source_bytes',False),'existing_published_source':item.get('existing_published_source'),'current_validation_state_recorded_externally':True,'candidate_source_byte_exact_preserved':item.get('preserve_candidate_source_bytes',False) or item.get('preserve_complete_published_source_bytes',False),'pointer_inserted_this_overlay':('docs/verification/20261123-blue-compilation' in header and 'docs/verification/20261123-blue-compilation' not in old.split('\nnamespace ',1)[0]),'pointer_inserted_by_owner_stager':bool(replacements),'pointer_present_in_adopted_source':'docs/verification/20261123-blue-compilation' in header,'all_original_theorem_headers_numeric_constants_hypotheses_and_integrability_premises_preserved':item.get('all_raw_public_headers_exact',not bool(item.get('explicit_syntax_exceptions'))),'raw_headers_preserved_except_explicit_syntax_exceptions':True,'all_numeric_constants_original_hypotheses_and_integrability_premises_preserved':True,'all_data_expressions_and_algorithms_preserved':item.get('all_data_expressions_and_algorithms_preserved',True),'explicit_syntax_exceptions':item.get('explicit_syntax_exceptions',[]),'all_definition_raw_bytes_preserved_except_listed_exception':True,'root_old_unelaborated_or_unparsed_kernel_type_equality_not_claimed':bool(item.get('explicit_syntax_exceptions') or item.get('notation_scope_support_restoration')),'notation_scope_support_restoration':item.get('notation_scope_support_restoration'),'neutral_status_text_replacements':replacements,'verification_pointer_present_before_owner_canonical_compile':'docs/verification/20261123-blue-compilation' in header,'owner_did_not_insert_pointer_where_no_matching_status_label':not replacements,'main_Member_same_baseline_synchronized':sync,'main_canonical_absent_not_created':not main.exists(),'different_main_source_preserved':exceptions.get(mod),'P6_native_or_frozen_sources_modified':False,'owner_canonical_compiler_invoked_at_staging':False,'original_failure_log':cfg['failure_log']};(z/'SOURCE_COMPARISON.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n');target.write_bytes(new.encode())
 if sync:main.write_bytes(new.encode())
 rows[mod]=record;print(mod,post,'main_sync',sync,'pointer','docs/verification/20261123-blue-compilation' in header,flush=True)
# A mathematical correction to a false internal statement is separate from
# lexical syntax restoration. This applies only to new, unfrozen packets.
for item in cfg['items']:
 if item.get('explicit_statement_corrections'):
  mod=item['module'];record=rows[mod]
  record['explicit_statement_corrections']=item['explicit_statement_corrections']
  record['all_original_theorem_headers_numeric_constants_hypotheses_and_integrability_premises_preserved']=False
  record['raw_headers_preserved_except_explicit_syntax_exceptions']=False
  record['raw_headers_preserved_except_explicitly_listed_statement_or_syntax_exceptions']=True
  record['old_false_internal_statement_not_claimed_kernel_equal_to_new_bound']=True
  (R/mod.split('.')[-1]/'SOURCE_COMPARISON.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
# Authorized preventive reuse is not an observed source failure.
for item in cfg['items']:
 if item.get('authorized_engineering_reuse_without_actual_failure'):
  mod=item['module'];record=rows[mod]
  record['authorized_engineering_reuse_without_actual_failure']=True
  record['actual_source_failure_preceded_this_overlay']=False
  record['engineering_reuse_evidence']=item['engineering_reuse_evidence']
  record['original_failure_log']=None
  (R/mod.split('.')[-1]/'SOURCE_COMPARISON.json').write_text(json.dumps(record,indent=2,ensure_ascii=False)+'\n')
(R/'SOURCE_SELECTION.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n');(R/'EXPECTED_SOURCES.json').write_text(json.dumps({m:x['postimage_sha256'] for m,x in rows.items()},indent=2)+'\n');(R/'MAIN_SOURCE_EXCEPTIONS.json').write_text(json.dumps(exceptions,indent=2)+'\n');(R/'STAGING_CONFIGURATION.json').write_text(json.dumps(cfg,indent=2,ensure_ascii=False)+'\n')
s=Path('/workspace/blue-member-repair-batch8/run_validation.py').read_text().replace('/workspace/blue-member-repair-batch8',str(R)).replace('/workspace/blue-build-tools/runtime-evidence/state.json',cfg['state']);s=s.replace('normal=[];kernel=[];baselines={}\n','normal=[];kernel=[];baselines={};pending=[]\n');s=s.replace("short=mod.split('.')[-1];rec=run(short+'-normal'", "short=mod.split('.')[-1]\n prior=R/(short+'-normal-command.json')\n if prior.exists() and json.loads(prior.read_text())['exit_code']!=0:\n  pending.append(mod);continue\n rec=run(short+'-normal'");s=s.replace("if rec['exit_code']:write(R/'FAILED_STAGE.json',{'module':mod,'stage':'normal','record':rec});raise SystemExit(rec['exit_code'])","if rec['exit_code']:\n  write(R/(short+'-FAILED_STAGE.json'),{'module':mod,'stage':'normal','record':rec});pending.append(mod);continue");s=s.replace("baseline=snap(mod);assert len(baseline)==6;baselines[mod]=baseline;write(R/(short+'-AFTER_NORMAL.json'),baseline)","saved=R/(short+'-AFTER_NORMAL.json');baseline=json.loads(saved.read_text()) if saved.exists() else snap(mod);assert len(baseline)==6 and snap(mod)==baseline;baselines[mod]=baseline\n if not saved.exists():write(saved,baseline)");s=s.replace("assert snap(mod)==baseline;write(R/(short+'-AFTER_KERNEL.json'),snap(mod))","assert snap(mod)==baseline\n savedkernel=R/(short+'-AFTER_KERNEL.json')\n if savedkernel.exists():assert json.loads(savedkernel.read_text())==baseline\n else:write(savedkernel,baseline)");s=s.replace("rec=run('all-public-types-axioms'", "if pending:\n write(R/'PENDING_REPAIRS.json',pending);print('PENDING_REPAIRS',pending,flush=True);raise SystemExit(1)\nrec=run('all-public-types-axioms'");(R/'run_validation.py').write_text(s)
a=Path('/workspace/blue-member-repair-batch3/PublicAudit.lean').read_text();body=a[a.index('  let selected :='):];prefix='\n'.join('import '+m for m in rows)+'\nimport Lean\nset_option pp.all true\nset_option pp.universes true\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let moduleNames := env.header.moduleNames\n  let targets : Array Name := #['+', '.join('`'+m for m in rows)+']\n';(R/'PublicAudit.lean').write_text(prefix+body)
src=Path(cfg['failure_log']);raw=src.read_bytes();slices={}
for mod in rows:
 item=next(x for x in cfg['items'] if x['module']==mod)
 if item.get('authorized_engineering_reuse_without_actual_failure'):
  slices[mod]={'status':'AUTHORIZED_ENGINEERING_REUSE_NO_PREVIOUS_SOURCE_FAILURE','actual_failure_claimed':False,'source_only_evidence':item['engineering_reuse_evidence']};continue
 i=raw.index(('Building '+mod+' ').encode());start=raw.rfind(b'\n',0,i)+1;exit_match=re.search(rb'(?m)^error: Lean exited with code ([0-9]+)\r?$',raw[i:]);assert exit_match,('missing_actual_lean_exit',mod);end=i+exit_match.end();end+=int(raw[end:end+1]==b'\n');piece=raw[start:end];z=R/mod.split('.')[-1];(z/'before-build.log').write_bytes(piece);slices[mod]={'original_running_log':str(src),'raw_byte_start':start,'raw_byte_end_exclusive':end,'raw_sha256':sha(piece),'slice':str((z/'before-build.log').relative_to(R)),'verbatim_raw_bytes':True}
(R/'BEFORE_LOG_SLICES.json').write_text(json.dumps(slices,indent=2)+'\n')
