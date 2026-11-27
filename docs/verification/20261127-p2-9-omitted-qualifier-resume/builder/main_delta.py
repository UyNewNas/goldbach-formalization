"""Literal main-only continuation from exact v5; not an executable controller."""
import base64
import hashlib
import json
import zlib


def make_changes(context):
    source=context['source'];changes=[]
    def add(label,before,after):changes.append((label,before,after))
    def line(prefix):
        matches=[s+'\n' for s in source.splitlines() if s.startswith(prefix)]
        assert len(matches)==1,prefix
        return matches[0]
    def block(start,end):
        a=source.index(start);return source[a:source.index(end,a)]
    def pin(b):return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
    receipt_raw=json.dumps({name:{**pin(b),'base64':base64.b64encode(b).decode()} for name,b in context['receipts'].items()},sort_keys=True,separators=(',',':')).encode()
    receipts=base64.b64encode(zlib.compress(receipt_raw,9)).decode()
    amendment_raw=(json.dumps(context['amendment'],indent=2)+'\n').encode()
    amendment=base64.b64encode(amendment_raw).decode()

    add('new_v6_owned_output_and_v5_anchor',line(" base=P(contract['receiver_root']);root=")," base=P(contract['receiver_root']);root=base/'project';first_out=base/'verification';previous_out=base/'verification-import-order-resume-v3';v4_out=base/'verification-mathlib-path-resume-v4';v5_out=base/'verification-standard-package-resume-v5';out=base/'verification-finset-prod-resume-v6'\n")
    add('existing_Batteries_view_required'," assert not v5_view.exists() and not v5_view.is_symlink()\n"," assert v5_view.is_dir() and not v5_view.is_symlink() and batteries_lib.is_dir() and not batteries_lib.is_symlink()\n")
    before=line(' v5_probe_raw=fixed_bytes(')
    preflight=""" assert v5_out.is_dir() and not v5_out.is_symlink()
 v6_probe_text=globals()['V5_PROBE_TEXT'];assert isinstance(v6_probe_text,str)
 v6_probe_raw=fixed_bytes(v6_probe_text.encode(),@@PROBE_PIN@@);v6_probe=json.loads(v6_probe_raw)
 assert v6_probe['schema']=='p29_v5_completed_failure_readonly_probe_v1' and v6_probe['v5_job_id']=='1aadf7911aac4b80ab0a049f967aa3ba' and v6_probe['root']==str(v5_out)
 assert v6_probe['new_Lean_calls']==v6_probe['writes_to_remote_workspace']==v6_probe['new_formal_credit']==0
 v6_data={};v6_file_stats={}
 for name,row in v6_probe['files'].items():
  p=v5_out/name;assert row['exists']is True and row['path']==str(p) and p.is_file() and not p.is_symlink()
  before=stamp(p);assert before==row['stat'] and before[2]<=67108864
  data=fixed_bytes(p.read_bytes(),row);assert stamp(p)==before
  if 'base64'in row:assert data==base64.b64decode(row['base64'])
  v6_data[name]=data;v6_file_stats[str(p)]=before
 assert len(v6_data)==21 and hashlib.sha256(v6_data['driver.py']).hexdigest()=='76a2bf4b3e12e4dacb05bfe9cf138012271ef8a47947ef42cf35aefb0e77483f'
 assert v6_data['INPUT_CONTRACT.json']==raw.encode()
 v5_inventory=v6_probe['all_v5_regular_file_inventory']
 assert {p.relative_to(v5_out).as_posix()for p in v5_out.rglob('*')if p.is_file()}==set(v5_inventory)
 for name,row in v5_inventory.items():
  p=v5_out/name;assert p.is_file() and not p.is_symlink() and stamp(p)==row['stat'] and p.stat().st_size==row['bytes']
 old_source_row=v6_probe['old_target_source'];old_source_path=root/(target.replace('.','/')+'.lean')
 assert old_source_row['path']==str(old_source_path) and old_source_path.is_file() and not old_source_path.is_symlink() and stamp(old_source_path)==old_source_row['stat']
 failed_v5_source=fixed_bytes(old_source_path.read_bytes(),old_source_row);assert failed_v5_source==base64.b64decode(old_source_row['base64']) and stamp(old_source_path)==old_source_row['stat']
 assert len(failed_v5_source)==7887 and hashlib.sha256(failed_v5_source).hexdigest()==source_sha
 v6_amendment_raw=fixed_bytes(base64.b64decode(@@AMENDMENT@@),@@AMENDMENT_PIN@@);v6_amendment=json.loads(v6_amendment_raw)
 repaired_source=fixed_bytes(base64.b64decode(v6_amendment['repaired_source']['base64']),v6_amendment['repaired_source'])
 assert v6_amendment['historical_dependency_contract_sha256']==CONTRACT_SHA256 and v6_amendment['original_failed_job']=='1aadf7911aac4b80ab0a049f967aa3ba'
 fixed_bytes(failed_v5_source,v6_amendment['original_source'])
 old_lines=failed_v5_source.splitlines(keepends=True);assert old_lines[139]==b'          apply prod_le_prod\\n'
 new_lines=list(old_lines);new_lines[139]=b'          apply Finset.prod_le_prod\\n';assert b''.join(new_lines)==repaired_source and len(repaired_source)==7894
 assert re.findall(r'^import\\s+(\\S+)',failed_v5_source.decode(),re.M)==re.findall(r'^import\\s+(\\S+)',repaired_source.decode(),re.M)==contract['target']['direct_imports']
 assert v6_amendment['repaired_source']['sha256']=='559c7c09e8b38e69f4b076ea8371a48a55b7611ca51482c62686c18db2ef5353' and v6_amendment['repaired_source']['git_blob']=='8b64194e1381c1dedb59b8d13c715aad0dd94e94'
 for suffix,row in v6_probe['target_outputs'].items():
  p=root/'.lake/build/lib/lean'/(target.replace('.','/')+suffix);assert row=={'path':str(p),'exists':False,'is_symlink':False} and not p.exists() and not p.is_symlink()
 assert set(v6_probe['target_outputs'])=={'.olean','.ilean','.trace','.setup.json'}
 v6_submission_raw=fixed_bytes(__import__('zlib').decompress(base64.b64decode(@@RECEIPTS@@)),@@RECEIPTS_PIN@@)
 v6_submission_pins=json.loads(v6_submission_raw);v6_submission_bytes={name:fixed_bytes(base64.b64decode(row['base64']),row)for name,row in v6_submission_pins.items()}
 v6_request=json.loads(v6_submission_bytes['ACTUAL_REQUEST.json']);v6_task=json.loads(v6_submission_bytes['ACTUAL_TERMINAL_TASK.json']);v6_join=json.loads(v6_submission_bytes['ACTUAL_TASK_JOIN.json'])
 v6_stdout=v6_submission_bytes['ACTUAL_STDOUT.log'];v5_failure=json.loads(v6_data['FAILURE.json'])
 assert v6_task['job_id']==v6_task['task_id']==v6_join['job_id']=='1aadf7911aac4b80ab0a049f967aa3ba' and v6_task['status']=='failed' and v6_task['exit_code']==1
 assert v6_task['log_bytes']==len(v6_stdout)==2467 and v6_task['log_truncated']is False and v6_task['log_discarded_bytes']==0
 assert [json.loads(l[len(b'P29_FAILURE '):])for l in v6_stdout.splitlines()if l.startswith(b'P29_FAILURE ')]==[v5_failure]
 assert v5_failure['error']=='Gate failed: normal-build' and v5_failure['completed_stages']==['batteries-composed-view-observation','omitted-direct-imports','normal-build'] and v5_failure['supplier_source_kernel_owned_replays']==0
 assert v5_failure['partial_target_outputs_preserved']=={str(old_source_path):{'bytes':7887,'sha256':source_sha}}
 v6_limits={'cwd':'/workspace','memory_mb':12800,'cpu_threads':2,'timeout_seconds':3600}
 assert {k:v6_request[k]for k in v6_limits}=={k:v6_task[k]for k in v6_limits}==v6_join['actual_limits']==v6_limits
 assert v6_data['SERVICE_OBSERVATION.json']==v6_submission_bytes['FRESH_SERVICE_OBSERVATION.json'] and hashlib.sha256(v6_data['SERVICE_OBSERVATION.json']).hexdigest()==v6_join['observation_sha256']
 v6_observation=json.loads(v6_data['SERVICE_OBSERVATION.json']);v6_after=datetime.datetime.strptime(v6_observation['clock_after']['current_time'],'%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=timezone.utc).timestamp()
 assert v6_observation['requested_MCP_limits']==contract['MCP_limits'] and v6_observation['submission_observation_max_age_seconds']==300
 assert v6_task['submitted_at']==v6_join['actual_submitted_at'] and 0<=v6_task['submitted_at']-v6_after==v6_join['submission_seconds_after_observation']<=v6_join['submission_window_max_seconds']==300
 prior_current_metadata=v6_probe['actual_used_part_current_metadata']
 assert prior_current_metadata['module_count']==6342 and prior_current_metadata['parts']==prior_current_metadata['part_count']==31074 and prior_current_metadata['mismatches']==[] and prior_current_metadata['fresh_part_hashes_claimed']is False
 assert prior_current_metadata['roots']==contract['target']['direct_imports']
 assert v6_probe['Batteries_view']=={'path':str(batteries_lib),'symlink_count':960}
 for name,count in [('COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json',569),('COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json',960)]:
  assert v6_probe['current_namespace_links'][name]=={'facets_checked':count,'mismatches':[]}
  for row in json.loads(v6_data[name])['facets']:
   p=P(row['requested_path']);assert p.is_symlink() and os.readlink(p)==row['selected_path'] and p.resolve(strict=True)==P(row['selected_path']).resolve(strict=True)
 v5_package_receipt=json.loads(v6_data['REUSED_V4_PACKAGE_VIEW.json']);v6_package_view=v6_probe['package_view']
 assert v6_package_view['link']==str(root/'.lake/packages') and v6_package_view['link_target']==str(base/'packages-mathlib-resume-v4') and v6_package_view['entries']==v5_package_receipt['selected_package_paths'] and v6_package_view['matches_saved_selected_package_paths']is True
"""
    preflight=preflight.replace('@@PROBE_PIN@@',repr(pin(context['probe_raw']))).replace('@@AMENDMENT@@',repr(amendment)).replace('@@AMENDMENT_PIN@@',repr(pin(amendment_raw))).replace('@@RECEIPTS@@',repr(receipts)).replace('@@RECEIPTS_PIN@@',repr(pin(receipt_raw)))
    add('authenticate_actual_v5_failure_source_amendment_and_unchanged_views',before,preflight+before)

    old=block(" live_row=v5_probe['live_guard_log'];assert live_row['path']==prior_state['log']\n"," assert original_guard_prefix==v4_data['original-v3-runtime-stage-evidence/runtime-evidence/compiler-commands.jsonl']\n")
    add('read_original_v4_prefix_from_frozen_v5_snapshot',old,""" live_row=v5_probe['live_guard_log'];assert live_row['path']==prior_state['log']
 v4_guard_prefix=fixed_bytes(v6_data['ORIGINAL_V3_V4_GUARD_PREFIX.jsonl'],live_row)
 assert v4_guard_prefix==base64.b64decode(live_row['base64']) and v4_guard_prefix.startswith(original_guard_prefix)
 resume_guard_prefix=v4_guard_prefix
""")
    before=" assert v4_processes['omitted-direct-imports']['stdin_sha256']==hashlib.sha256(compile_audit_text(contract['target']['direct_imports'])).hexdigest()\n"
    add('authenticate_exact_v5_three_stage_extension_and_one_failed_source',before,before+""" assert v6_data['runtime-evidence/state.json']==original_runtime_bytes['runtime-evidence/state.json']
 v6_live_row=v6_probe['live_guard_log'];assert v6_live_row['path']==prior_state['log']
 v6_live_path=P(v6_live_row['path']);assert v6_live_path.is_file() and not v6_live_path.is_symlink() and stamp(v6_live_path)==v6_live_row['stat']
 v5_guard_prefix=fixed_bytes(v6_live_path.read_bytes(),v6_live_row);assert stamp(v6_live_path)==v6_live_row['stat'] and v5_guard_prefix==base64.b64decode(v6_live_row['base64']) and v5_guard_prefix.startswith(v4_guard_prefix)
 v5_path_record=json.loads(v6_data['ACTUAL_FIRST_NAMESPACE_PATHS.json']);v5_composed_observation=json.loads(v6_data['batteries-composed-view-observation.log'])
 assert v5_composed_observation=={'cwd':str(root),'LEAN_PATH':os.pathsep.join(v5_path_record['actual_LEAN_PATH'])}
 v5_expected_prefix=['python3',str(base/'original-tools/run_guarded.py'),'--state',str(v5_out/'runtime-evidence/state.json'),'lake','env','env','LEAN_PATH='+v5_composed_observation['LEAN_PATH']]
 v5_expected_commands={'batteries-composed-view-observation':v5_expected_prefix+['python3','-c','import json,os; print(json.dumps({"cwd":os.getcwd(),"LEAN_PATH":os.environ["LEAN_PATH"]}))'],'omitted-direct-imports':v5_expected_prefix+['lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin'],'normal-build':v5_expected_prefix+['lean','-DwarningAsError=true','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','-o',str(root/'.lake/build/lib/lean'/(target.replace('.','/')+'.olean')),'-i',str(root/'.lake/build/lib/lean'/(target.replace('.','/')+'.ilean')),str(old_source_path)]}
 v5_processes={};position=len(v4_guard_prefix)
 for label,command in v5_expected_commands.items():
  rec=json.loads(v6_data[label+'-process.json']);v5_processes[label]=rec
  assert rec['stage']==label and rec['command']==command and rec['cwd']==str(root) and rec['log_path']==str(v5_out/(label+'.log'))
  assert rec['exit_code']==(1 if label=='normal-build'else 0) and rec['forbidden_source_calls']==[] and rec['log_sha256']==hashlib.sha256(v6_data[label+'.log']).hexdigest()
  a,b=rec['guard_log_start'],rec['guard_log_end'];assert a==position and a<=b<=len(v5_guard_prefix)
  assert [json.loads(l)for l in v5_guard_prefix[a:b].splitlines()if l]==rec['guarded_commands'];position=b
 assert position==len(v5_guard_prefix)==8614
 assert v6_data['omitted-direct-imports.lean']==compile_audit_text(contract['target']['direct_imports']) and v5_processes['omitted-direct-imports']['stdin_sha256']==hashlib.sha256(v6_data['omitted-direct-imports.lean']).hexdigest()
 failed_v5_source_rows=[r for r in v5_processes['normal-build']['guarded_commands']if r.get('tool')=='lean'and any(str(a).endswith('.lean')for a in r.get('input_args',[]))]
 assert len(failed_v5_source_rows)==1 and [a for a in failed_v5_source_rows[0]['input_args']if str(a).endswith('.lean')]==[str(old_source_path)]
 assert [r for r in (json.loads(l)for l in v5_guard_prefix.splitlines()if l)if r.get('tool')=='lean'and any(str(a).endswith('.lean')for a in r.get('input_args',[]))]==failed_v5_source_rows
 resume_guard_prefix=v5_guard_prefix
""")
    before=" protected={};cache_before={};runs=[]\n"
    add('preserve_v5_evidence_and_both_target_source_versions',before,before+""" for name,row in v6_probe['files'].items():
  p=v5_out/name;assert stamp(p)==v6_file_stats[str(p)];preserve(p,row['sha256'])
 for name,data in v6_submission_bytes.items():
  dest=out/'original-v5-submission'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);preserve(dest,hashlib.sha256(data).hexdigest())
 for name,data in [('V5_REUSE_PROBE.json',v6_probe_raw),('ORIGINAL_V3_V4_V5_GUARD_PREFIX.jsonl',v5_guard_prefix),('FAILED_V5_TARGET_SOURCE.lean',failed_v5_source),('TARGET_SOURCE_AMENDMENT.json',v6_amendment_raw),('omitted-direct-imports-bindings.json',v6_data['omitted-direct-imports-bindings.json']),('REUSED_V5_CURRENT_INPUT_ORIGIN_BINDING.json',v6_data['CURRENT_INPUT_ORIGIN_BINDING.json'])]:
  dest=out/name;dest.write_bytes(data);preserve(dest,hashlib.sha256(data).hexdigest())
 save(out/'REUSED_V5_SUCCESSFUL_STAGES_AND_FAILED_NORMAL.json',{'schema':'p29_v6_original_actual_import_and_failed_normal_reuse_v1','original_task':'1aadf7911aac4b80ab0a049f967aa3ba','original_failure':v5_failure,'original_processes':v5_processes,'original_file_pins':{name:{k:row[k]for k in ['path','bytes','sha256','stat']}for name,row in v6_probe['files'].items()},'successful_stages_reused':['batteries-composed-view-observation','omitted-direct-imports'],'successful_stage_reinvocations':0,'failed_target_normal_invocations_preserved':1,'failed_source_snapshot':'FAILED_V5_TARGET_SOURCE.lean','failed_source_pin':v6_amendment['original_source'],'failed_source_guard_rows':failed_v5_source_rows,'actual_import_binding_reused_not_recaptured':True,'supplier_replays':0,'new_formal_credit':0})
""")
    before=line(" combined_snapshot=out/'ORIGINAL_V3_V4_GUARD_PREFIX.jsonl'")
    add('keep_v4_snapshot_label_and_bytes_exact',before,before.replace('resume_guard_prefix','v4_guard_prefix'))
    before=" preserve(combined_snapshot,hashlib.sha256(resume_guard_prefix).hexdigest())\n"
    add('bind_frozen_v4_snapshot_preserve_hash_to_its_written_bytes',before,before.replace('resume_guard_prefix','v4_guard_prefix'))
    before=line(" save(out/'ORIGINAL_STANDARD_PACKAGE_FAILURE_REUSE.json'")
    add('keep_original_v4_reuse_receipt_semantics',before,before.replace('len(resume_guard_prefix)','len(v4_guard_prefix)').replace('hashlib.sha256(resume_guard_prefix)','hashlib.sha256(v4_guard_prefix)'))
    add('reuse_existing_Batteries_view_no_creation'," assert not v5_view.exists() and not v5_view.is_symlink();v5_view.mkdir();batteries_lib.mkdir()\n"," # Reuse the existing v5 view after exact authority joins; do not recreate it.\n assert v5_view.is_dir() and not v5_view.is_symlink() and batteries_lib.is_dir() and not batteries_lib.is_symlink()\n")
    before="  dest=batteries_lib/(mod.replace('.','/')+facet);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists() and not dest.is_symlink();dest.symlink_to(current)\n"
    add('reuse_each_exact_Batteries_symlink',before,"  dest=batteries_lib/(mod.replace('.','/')+facet);assert dest.is_symlink() and os.readlink(dest)==str(current)\n")
    before=line(" save(out/'COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json'")
    add('label_reused_Batteries_view_as_historical_qualification',before,before.replace("'metadata_only_before_actual_import':True,'fresh_actual_headers_and_full_used_facet_hashes_still_required':True","'existing_view_reused':True,'original_actual_import_qualification_reused_from_v5':True,'fresh_consumer_after_normal_still_required':True"))
    before=line(" save(out/'REUSED_ORIGINAL_QUALIFICATIONS.json'")
    add('label_original_actual_import_as_already_qualified',before,before.replace("'current_actual_header_facet_union_not_yet_run':True","'original_v5_actual_header_facet_union_reused':True,'successful_import_reinvocations':0"))
    before=line(" save(out/'REUSED_V4_SUCCESSFUL_PATH_STAGE.json'")
    add('do_not_promise_rerun_of_composed_path_observation',before,before.replace("'new_composed_view_observation_follows':True","'original_v5_composed_view_observation_reused':True"))
    before=" stage('batteries-composed-view-observation',viewprefix+['python3','-c','import json,os; print(json.dumps({\"cwd\":os.getcwd(),\"LEAN_PATH\":os.environ[\"LEAN_PATH\"]}))'])\n composed_observation=json.loads((out/'batteries-composed-view-observation.log').read_text())\n"
    add('reuse_successful_v5_composed_path_without_stage_call',before," composed_observation=v5_composed_observation\n assert viewprefix[:3]==v5_expected_prefix[:3] and viewprefix[4:]==v5_expected_prefix[4:] and viewprefix[3]==str(state_path)\n")
    before=line(" save(out/'ACTUAL_FIRST_NAMESPACE_PATHS.json'")
    add('label_current_path_check_as_filesystem_revalidation',before,before.replace("'schema':'p29_fresh_explicit_composed_view_first_namespace_paths_v1'","'schema':'p29_historical_v5_composed_view_filesystem_revalidation_v1'").replace("'fresh_composed_view_observation':True","'fresh_composed_view_observation':False,'original_composed_view_task':'1aadf7911aac4b80ab0a049f967aa3ba','original_composed_view_process_sha256':hashlib.sha256(v6_data['batteries-composed-view-observation-process.json']).hexdigest(),'unchanged_view_filesystem_revalidation':True"))
    before=" before=actual_inputs('omitted-direct-imports',source_imports)\n bound_before=assert_expected_current_map(before)\n"
    add('reuse_exact_successful_actual_binding_and_revalidate_current_metadata',before,""" assert borrows==json.loads(v6_data['BORROWED_OBJECTS.json'])
 before=json.loads(v6_data['omitted-direct-imports-bindings.json']);prior_origin=json.loads(v6_data['CURRENT_INPUT_ORIGIN_BINDING.json'])
 assert before['schema']=='p29_unit_tail_actual_input_parts_v1' and before['roots']==source_imports and before['module_count']==6342 and before['part_count']==31074
 assert len(before['actual_modules'])==before['module_count'] and len(before['parts'])==before['part_count']
 assert target not in {r['module']for r in before['actual_modules']} and target not in {r['module']for r in before['parts']}
 assert prior_origin['status']=='PASS_CURRENT_HEADER_FACET_IMPORT_UNION' and prior_origin['actual_bindings_sha256']==sha(out/'omitted-direct-imports-bindings.json') and prior_origin['module_count']==before['module_count'] and prior_origin['part_count']==before['part_count']
 assert prior_origin['formal_credit']==prior_origin['supplier_source_kernel_owned_replays']==0 and prior_origin['approved_byte_origin_table_size']==len(expected_origins)
 assert set(prior_origin['project_modules'])==set(borrows) and len(borrows)==58
 assert [json.loads(l[len('P29_ACTUAL_IMPORT '):])for l in v6_data['omitted-direct-imports.log'].decode().splitlines()if l.startswith('P29_ACTUAL_IMPORT ')]==before['actual_modules']
 seen_parts=set();reused_origin_counts={}
 for part in before['parts']:
  key=(part['module'],part['facet']);assert key not in seen_parts and key in expected_origins;seen_parts.add(key)
  accepted_pin=expected_origins[key];identity=part['identity'];p=P(identity['path']);requested=P(part['requested_path'])
  assert identity=={'path':str(P(accepted_pin['path']).resolve(strict=True)),'bytes':accepted_pin['bytes'],'sha256':accepted_pin['sha256']}
  assert p.is_file() and p.resolve(strict=True)==p and stamp(p)==part['stat_snapshot'] and p.stat().st_size==identity['bytes']
  assert requested.resolve(strict=True)==p
  if str(p)in cache_before:assert cache_before[str(p)]==part['stat_snapshot']
  if str(requested)in cache_before:assert cache_before[str(requested)]==part['stat_snapshot']
  cache_before[str(p)]=part['stat_snapshot'];cache_before[str(requested)]=part['stat_snapshot']
  reused_origin_counts[accepted_pin['origin']]=reused_origin_counts.get(accepted_pin['origin'],0)+1
 assert reused_origin_counts==prior_origin['origin_counts'] and len(seen_parts)==before['part_count']
 bound_before=len(seen_parts)
 save(out/'CURRENT_INPUT_QUALIFICATION_REUSED.json',{'schema':'p29_v5_qualified_actual_import_binding_reuse_v1','original_task':'1aadf7911aac4b80ab0a049f967aa3ba','original_process_sha256':hashlib.sha256(v6_data['omitted-direct-imports-process.json']).hexdigest(),'original_log_sha256':hashlib.sha256(v6_data['omitted-direct-imports.log']).hexdigest(),'original_bindings_sha256':sha(out/'omitted-direct-imports-bindings.json'),'original_origin_report_sha256':hashlib.sha256(v6_data['CURRENT_INPUT_ORIGIN_BINDING.json']).hexdigest(),'modules':6342,'parts':31074,'original_compiled_header_and_full_facet_qualification_reused':True,'current_physical_paths_sizes_and_stats_revalidated':True,'fresh_hash_or_Lean_import_replay_claim':False,'successful_stage_reinvocations':0,'supplier_replays':0,'new_formal_credit':0})
""")
    before=line(" normal_cmd=viewprefix+['lean'")
    add('preserve_old_source_then_apply_exact_seven_byte_name_amendment',before,""" assert src==old_source_path and src.is_file() and not src.is_symlink() and src.read_bytes()==failed_v5_source and stamp(src)==old_source_row['stat']
 assert str(src)not in protected and cache_before[str(src)]==old_source_row['stat']
 assert (out/'FAILED_V5_TARGET_SOURCE.lean').read_bytes()==failed_v5_source and sha(out/'FAILED_V5_TARGET_SOURCE.lean')==v6_amendment['original_source']['sha256']
 replacement=out/'TARGET_SOURCE_REPLACEMENT.lean'
 with replacement.open('xb')as f:f.write(repaired_source)
 fixed_bytes(replacement.read_bytes(),v6_amendment['repaired_source']);os.replace(replacement,src)
 source=repaired_source;source_blob=v6_amendment['repaired_source']['git_blob'];source_sha=v6_amendment['repaired_source']['sha256']
 new_source_stat=stamp(src);fixed_bytes(src.read_bytes(),v6_amendment['repaired_source']);assert stamp(src)==new_source_stat
 cache_before[str(src)]=new_source_stat
 assert re.findall(r'^import\\s+(\\S+)',source.decode(),re.M)==source_imports
 save(out/'TARGET_SOURCE_AMENDMENT_APPLIED.json',{'schema':'p29_exact_failed_target_source_amendment_applied_v1','original_failed_source_snapshot':'FAILED_V5_TARGET_SOURCE.lean','original_failed_source':v6_amendment['original_source'],'current_source':{k:v6_amendment['repaired_source'][k]for k in ['bytes','sha256','git_blob']},'amendment_sha256':sha(out/'TARGET_SOURCE_AMENDMENT.json'),'original_dependency_contract_sha256':CONTRACT_SHA256,'one_exact_name_qualification_only':True,'current_source_stat':stamp(src),'new_normal_not_yet_run':True,'new_formal_credit':0})
 stable()
"""+before)
    before=" assert lean_sources==[str(src)],lean_sources\n"
    add('honest_failed_v5_and_repaired_v6_source_invocation_accounting',before,""" assert lean_sources==[str(src),str(src)],lean_sources
 new_guard_rows=[json.loads(l)for l in guardlog.read_bytes()[len(v5_guard_prefix):].splitlines()if l]
 new_source_rows=[r for r in new_guard_rows if r.get('tool')=='lean'and any(str(a).endswith('.lean')for a in r.get('input_args',[]))]
 assert len(new_source_rows)==1 and [a for a in new_source_rows[0]['input_args']if str(a).endswith('.lean')]==[str(src)]
 assert [r for r in commands if r.get('tool')=='lean'and any(str(a).endswith('.lean')for a in r.get('input_args',[]))]==failed_v5_source_rows+new_source_rows
 save(out/'EXACT_TWO_TARGET_NORMAL_INVOCATIONS.json',{'schema':'p29_failed_and_repaired_target_normal_invocations_v1','historical_failed_v5':{'job':'1aadf7911aac4b80ab0a049f967aa3ba','source':v6_amendment['original_source'],'source_snapshot':'FAILED_V5_TARGET_SOURCE.lean','process':v5_processes['normal-build'],'guard_rows':failed_v5_source_rows},'current_repaired_normal':{'source':{k:v6_amendment['repaired_source'][k]for k in ['bytes','sha256','git_blob']},'process':normal,'guard_rows':new_source_rows},'historical_failed_source_invocations':1,'current_successful_source_invocations':1,'supplier_source_replays':0})
""")
    before=line(" save(out/'VALIDATION_RESULTS.json'")
    add('record_amended_source_and_historical_failure_in_final_result',before," result.update(target_source_amendment_sha256=sha(out/'TARGET_SOURCE_AMENDMENT.json'),historical_failed_target_normal_invocations=1,current_repaired_target_normal_invocations=1,reused_v5_actual_import_task='1aadf7911aac4b80ab0a049f967aa3ba',reused_successful_v5_stage_reinvocations=0,original_dependency_contract_unchanged=True)\n"+before)
    before=" assert (out/'ORIGINAL_V3_V4_GUARD_PREFIX.jsonl').read_bytes()==resume_guard_prefix\n"
    add('archive_complete_v5_attempt_and_preserved_failed_source',before,""" assert (out/'ORIGINAL_V3_V4_GUARD_PREFIX.jsonl').read_bytes()==v4_guard_prefix
 assert (out/'ORIGINAL_V3_V4_V5_GUARD_PREFIX.jsonl').read_bytes()==resume_guard_prefix==v5_guard_prefix
 assert (out/'FAILED_V5_TARGET_SOURCE.lean').read_bytes()==failed_v5_source
 assert {p.relative_to(v5_out).as_posix()for p in v5_out.rglob('*')if p.is_file()}==set(v5_inventory)
 for name,row in v5_inventory.items():
  p=v5_out/name;assert p.is_file() and not p.is_symlink() and stamp(p)==row['stat'];members['original-standard-package-attempt-v5/'+name]=p
""")
    return changes
