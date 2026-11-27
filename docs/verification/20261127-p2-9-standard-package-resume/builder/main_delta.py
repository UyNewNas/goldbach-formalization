"""Literal main and exactly three reviewed prefix changes; never runs a controller."""
import base64
import hashlib
import json
import zlib


def make_changes(context):
    source = context["source"]
    changes = []

    def line(prefix):
        matches = [value + "\n" for value in source.splitlines() if value.startswith(prefix)]
        if len(matches) != 1:
            raise ValueError("baseline line is not unique: " + prefix)
        return matches[0]

    def add(label, before, after):
        changes.append((label, before, after))

    def pin(raw):
        return {"bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()}

    probe_raw = context["probe_raw"]
    receipt_bundle = json.dumps({name: {**pin(raw), "base64": base64.b64encode(raw).decode()} for name, raw in context["receipts"].items()}, sort_keys=True, separators=(",", ":")).encode()
    probe_payload = base64.b64encode(zlib.compress(probe_raw, 9)).decode()
    receipt_payload = base64.b64encode(zlib.compress(receipt_bundle, 9)).decode()
    cache_raw = context["cache_probe_raw"]

    for name, before, after in [
        ("named_kernel", "rec=stage(label,runprefix+['lake','env','leanchecker'", "rec=stage(label,viewprefix+['leanchecker'"),
        ("full_owned", "rec=stage(label,runprefix+['lake','env','lean'", "rec=stage(label,viewprefix+['lean'"),
        ("actual_inputs", "process=stage(label,runprefix+['lake','env','lean'", "process=stage(label,viewprefix+['lean'"),
    ]:
        add("reviewed_explicit_prefix_" + name, before, after)
    add("main_explicit_composed_prefix_global", line(" global contract,CONTRACT_SHA256"), line(" global contract,CONTRACT_SHA256").rstrip("\n") + ",viewprefix\n")
    add("normal_uses_explicit_composed_prefix", "normal_cmd=runprefix+['lake','env','lean'", "normal_cmd=viewprefix+['lean'")

    add("new_owned_output_and_separate_v4_anchor", line(" base=P(contract['receiver_root']);root="),
        " base=P(contract['receiver_root']);root=base/'project';first_out=base/'verification';previous_out=base/'verification-import-order-resume-v3';v4_out=base/'verification-mathlib-path-resume-v4';out=base/'verification-standard-package-resume-v5'\n")
    add("read_only_no_clobber_and_actual_v4_evidence", " assert base.is_dir() and root.is_dir() and previous_out.is_dir()\n assert not out.exists(),'This exact resume already has evidence; do not repeat it.'\n", """ assert base.is_dir() and root.is_dir() and previous_out.is_dir() and v4_out.is_dir()
 assert not out.exists() and not out.is_symlink(),'This exact resume already has evidence; do not repeat it.'
 v5_view=base/'batteries-native-cache-view-v5';batteries_lib=v5_view/'lib'
 assert not v5_view.exists() and not v5_view.is_symlink()
 for extension in ['.olean','.ilean','.trace','.setup.json']:
  p=root/'.lake/build/lib/lean'/(target.replace('.','/')+extension)
  assert not p.exists() and not p.is_symlink(),('Unrecorded target output exists; no replay is authorized',str(p))
 for name in ['FILE_MANIFEST.json','ARCHIVE_TRANSPORT.json','qualified-omitted-prime-wall.tar.xz']:
  p=base/name;assert not p.exists() and not p.is_symlink(),('Final evidence already exists; do not overwrite it',str(p))
 v5_probe_raw=fixed_bytes(__import__('zlib').decompress(base64.b64decode(@@PROBE_PAYLOAD@@)),@@PROBE_PIN@@)
 v5_probe=json.loads(v5_probe_raw)
 assert v5_probe['schema']=='p29_all_standard_package_readonly_probe_v1' and v5_probe['Lean_invocations']==v5_probe['filesystem_writes']==0
 v5_cache_text=globals()['CACHE_PROBE_TEXT'];assert isinstance(v5_cache_text,str)
 v5_cache_raw=fixed_bytes(v5_cache_text.encode(),@@CACHE_PIN@@)
 v5_cache=json.loads(v5_cache_raw)
 assert v5_cache['schema']=='p29_frozen_batteries_original_cache_readonly_probe_v1' and v5_cache['Lean_invocations']==v5_cache['filesystem_writes']==v5_cache['new_formal_credit']==0
 batteries_rows=sorted((row for row in v5_cache['accepted_cached_standard_facets']if row['original']['module']=='Batteries'or row['original']['module'].startswith('Batteries.')),key=lambda row:(row['original']['module'],row['original']['facet']))
 batteries_keys={(row['original']['module'],row['original']['facet'])for row in batteries_rows}
 assert len(batteries_rows)==len(batteries_keys)==960 and len({m for m,f in batteries_keys})==192
 assert all({f for n,f in batteries_keys if n==m}=={'.olean','.olean.server','.olean.private','.ir.sig','.ir'}for m in {m for m,f in batteries_keys})
 assert v5_cache['active_namespace_groups']['Batteries']=={'facets':960,'modules':192,'present':960,'missing':[],'size_mismatches':[]}
 batteries_cache=P('/workspace/p2-private-20261124/.lake/p2-private/native-cache/staged-45362510169/active/lib')
 cache_record_bytes={name:fixed_bytes(base64.b64decode(row['base64']),row)for name,row in v5_cache['records'].items()if 'base64'in row}
 batteries_receipt=json.loads(cache_record_bytes['batteries_receipt']);batteries_request=json.loads(cache_record_bytes['REQUEST.json'])
 assert batteries_receipt['schema']=='p2-winner9-batteries-overlay-v1' and batteries_receipt['status']=='EXACT_ORIGINAL_INPUT_BYTES_RESTORED_NOT_QUALIFICATION'
 assert batteries_receipt['source_compiler_invocations']==0 and batteries_receipt['compile_credit']is False and batteries_receipt['kernel_credit']is False
 assert batteries_receipt['baseline_modified']is False and batteries_receipt['donor_modified']is False
 assert batteries_receipt['active_root']==str(batteries_cache) and batteries_receipt['module_count']==192 and batteries_receipt['facet_count']==len(batteries_receipt['facets'])==960
 assert batteries_receipt['source_pin']==batteries_request['locked_packages']['batteries']['rev']=='41bd267b3f6b7252f6676af46d4ffc6783b64de9'
 assert batteries_receipt['checkpoint_sha256']==v5_cache['records']['CHECKPOINT.json']['sha256'] and batteries_receipt['request_sha256']==v5_cache['records']['REQUEST.json']['sha256']
 assert batteries_receipt['producer_script']==v5_cache['records']['producer_script']['path'] and batteries_receipt['producer_script_sha256']==v5_cache['records']['producer_script']['sha256']
 for name,observed in v5_cache['source_roots'].items():
  assert observed['path']==batteries_receipt[name] and observed['is_dir']is True
  assert observed['git']['HEAD']['exit_code']==observed['git']['toplevel']['exit_code']==observed['git']['tracked_diff']['exit_code']==0
  assert observed['git']['HEAD']['stdout']==batteries_receipt['source_pin'] and observed['git']['toplevel']['stdout']==observed['resolved'] and observed['git']['tracked_diff']['stdout']==''
 for row in batteries_rows:
  original=row['original'];current=row['current'];mod=original['module'];facet=original['facet'];pin=original['identity'];relative=mod.replace('.','/')+facet;p=P(pin['path'])
  assert original['original_snapshot_sha256']==contract['external_snapshot_sha256'] and p==batteries_cache/relative
  assert current['exists']is True and current['is_symlink']is False and current['resolved_path']==str(p) and current['stat'][2]==pin['bytes']
  assert p.is_file() and not p.is_symlink() and p.resolve(strict=True)==p and stamp(p)==current['stat']
  receipt_facet=batteries_receipt['facets'][relative]
  assert receipt_facet['module']==mod and receipt_facet['target']==str(p) and receipt_facet['bytes']==pin['bytes'] and receipt_facet['sha256']==pin['sha256']
  if mod=='Batteries.Tactic.Lemma':
   full=row['current_exact_file'];assert full['path']==str(p) and full['bytes']==pin['bytes'] and full['sha256']==pin['sha256'] and full['stat']==current['stat']
   fixed_bytes(p.read_bytes(),pin);assert stamp(p)==current['stat']
  else:assert 'current_exact_file'not in row
 for name in ['Batteries','Batteries.olean','Batteries.olean.server','Batteries.olean.private','Batteries.ir','Batteries.ir.sig']:
  p=root/'.lake/build/lib/lean'/name;assert not p.exists() and not p.is_symlink(),('Unregistered earlier Batteries namespace',str(p))
 v5_receipt_raw=fixed_bytes(__import__('zlib').decompress(base64.b64decode(@@RECEIPT_PAYLOAD@@)),@@RECEIPT_PIN@@)
 v4_submission_pins=json.loads(v5_receipt_raw)
 v4_submission_bytes={name:fixed_bytes(base64.b64decode(row['base64']),row)for name,row in v4_submission_pins.items()}
 v4_data={};v4_runtime_stats={}
 for name,row in v5_probe['files'].items():
  p=v4_out/name;assert row['path']==str(p) and p.is_file() and not p.is_symlink()
  before=stamp(p);assert before==row['stat'] and before[2]<=1000000
  data=fixed_bytes(p.read_bytes(),row);assert stamp(p)==before
  if 'base64'in row:assert data==base64.b64decode(row['base64'])
  v4_data[name]=data;v4_runtime_stats[str(p)]=before
 assert hashlib.sha256(v4_data['driver.py']).hexdigest()=='80e8b906621f4aae6b0677c09594618984eb005a236fe8c2432d5fd95757426d'
 assert v4_data['INPUT_CONTRACT.json']==raw.encode()
 v4_request=json.loads(v4_submission_bytes['ACTUAL_REQUEST.json']);v4_task=json.loads(v4_submission_bytes['V4_TERMINAL_TASK.json']);v4_join=json.loads(v4_submission_bytes['ACTUAL_TASK_JOIN.json'])
 v4_stdout=v4_submission_bytes['V4_STDOUT.log'];v4_output=json.loads(v4_submission_bytes['V4_COMPLETE_OUTPUT_RESPONSE.json'])
 assert v4_task['job_id']==v4_task['task_id']==v4_join['job_id']=='a691a4c888044726ad49f92170e3c8f5'
 assert v4_task['status']=='failed' and v4_task['exit_code']==1 and v4_task['log_bytes']==len(v4_stdout)==2116
 assert v4_task['log_truncated']is False and v4_task['log_discarded_bytes']==0
 assert v4_output['output'].encode()==base64.b64decode(v4_output['output_base64'])==v4_stdout
 assert v4_output['eof']is True and v4_output['next_offset']==2116 and v4_output['log_truncated']is False and v4_output['discarded_bytes']==0
 v4_limits={'cwd':'/workspace','memory_mb':12800,'cpu_threads':2,'timeout_seconds':3600}
 assert {k:v4_request[k]for k in v4_limits}=={k:v4_task[k]for k in v4_limits}==v4_join['actual_limits']==v4_limits
 assert v4_task['submitted_at']==v4_join['actual_submitted_at'] and v4_join['actual_requested_limits_equal']is True
 assert v4_data['SERVICE_OBSERVATION.json']==v4_submission_bytes['FRESH_SERVICE_OBSERVATION.json']
 assert hashlib.sha256(v4_data['SERVICE_OBSERVATION.json']).hexdigest()==v4_join['observation_sha256']
 v4_observation=json.loads(v4_data['SERVICE_OBSERVATION.json'])
 assert v4_observation['requested_MCP_limits']==contract['MCP_limits'] and v4_observation['submission_observation_max_age_seconds']==300
 v4_after=datetime.datetime.strptime(v4_observation['clock_after']['current_time'],'%Y-%m-%d %H:%M:%S UTC').replace(tzinfo=timezone.utc).timestamp()
 assert 0<=v4_task['submitted_at']-v4_after==v4_join['submission_seconds_after_observation']<=v4_join['submission_window_max_seconds']==300
 v4_failure=json.loads(v4_data['FAILURE.json'])
 assert [json.loads(line[len(b'P29_FAILURE '):])for line in v4_stdout.splitlines()if line.startswith(b'P29_FAILURE ')]==[v4_failure]
 assert v4_failure['error']=='Gate failed: omitted-direct-imports' and v4_failure['completed_stages']==['mathlib-package-view-lean-path','omitted-direct-imports']
 assert v4_failure['partial_target_outputs_preserved']=={str(root/(target.replace('.','/')+'.lean')):{'bytes':7887,'sha256':source_sha}} and v4_failure['supplier_source_kernel_owned_replays']==0
 assert v4_data['omitted-direct-imports.log']==b"<stdin>:29:0: error: object file '/workspace/goldbach-p2/.lake/packages/batteries/.lake/build/lib/lean/Batteries/Tactic/Lemma.olean' of module Batteries.Tactic.Lemma does not exist\\n"
 v4_package_repair=json.loads(v4_data['PACKAGE_VIEW_REPAIR.json']);v4_package_paths=v4_package_repair['selected_package_paths']
 v5_selected_package_paths=@@SELECTED_PATHS@@
 v5_package_rows=json.loads(base64.b64decode(contract['configuration']['lake-manifest.json']['postimage_base64']))['packages']
 assert len(v5_package_rows)==10 and v4_package_paths==v5_selected_package_paths and set(v4_package_paths)=={r['name']for r in v5_package_rows}
 assert v4_package_repair['new_view']==str(base/'packages-mathlib-resume-v4')
 assert v5_probe['package_view_link']=={'path':str(root/'.lake/packages'),'is_symlink':True,'target':str(base/'packages-mathlib-resume-v4')}
 packages=root/'.lake/packages';assert packages.is_symlink() and os.readlink(packages)==str(base/'packages-mathlib-resume-v4')
 assert (base/'packages-mathlib-resume-v4').is_dir() and not (base/'packages-mathlib-resume-v4').is_symlink()
 for name,path in v4_package_paths.items():
  p=base/'packages-mathlib-resume-v4'/name;assert p.is_symlink() and os.readlink(p)==path
 assert v5_selected_package_paths['mathlib']==v4_package_paths['mathlib']=='/workspace/compile-deps/mathlib'
 assert v5_selected_package_paths['LeanArchitect']==v4_package_paths['LeanArchitect']=='/workspace/goldbach-p2/.lake/packages/LeanArchitect'
 table=v5_probe['original_derived_facet_table']
 assert table['path']==str(previous_out/'original-external-derived/P2_DECLARED_FACETS.jsonl') and table['bytes']==23833463 and table['sha256']=='e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636'
 assert {k:v5_cache['original_derived_table'][k]for k in ['path','bytes','sha256']}=={k:table[k]for k in ['path','bytes','sha256']}
 v5_selected_provider_records={}
 for package in v5_package_rows:
  name=package['name'];info=v5_probe['packages'][name];assert info['manifest_revision']==package['rev']
  if name=='LeanArchitect' or info['historical_facet_count']==0:
   assert v5_selected_package_paths[name]==v4_package_paths[name]
   continue
  assert info['historical_roots']==[v5_selected_package_paths[name]]
  candidates=[row for row in info['candidates']if row['path']==v5_selected_package_paths[name]];assert len(candidates)==1
  row=candidates[0];p=P(row['path']);assert row['exists']is True and row['lib_exists']is True and p.is_dir() and (p/'.lake/build/lib/lean').is_dir()
  assert str(p.resolve(strict=True))==row['resolved'] and P(row['resolved']).name==name
  assert row['git']['toplevel']['exit_code']==row['git']['HEAD']['exit_code']==0 and row['git']['toplevel']['stdout']==row['resolved'] and row['git']['HEAD']['stdout']==package['rev']
  assert row['historical_facets_present_by_metadata']==info['historical_facet_count'] and row['historical_facets_missing_by_metadata']==0
  assert P(subprocess.check_output(['git','-C',str(p),'rev-parse','--show-toplevel'],text=True).strip()).resolve()==p.resolve()
  assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==package['rev']
  v5_selected_provider_records[name]={'path':str(p),'resolved':str(p.resolve()),'manifest_revision':package['rev'],'historical_facet_count':info['historical_facet_count'],'metadata_inventory_only_not_actual_import_qualification':True}
 assert v5_probe['packages']['batteries']['historical_facet_count']==0 and v5_probe['packages']['batteries']['historical_roots']==[]
 assert {row['facet']:row['identity']for row in v5_probe['Batteries_Tactic_Lemma_original_rows']}=={row['original']['facet']:row['original']['identity']for row in batteries_rows if row['original']['module']=='Batteries.Tactic.Lemma'}
 v4_path_record=json.loads(v4_data['ACTUAL_FIRST_NAMESPACE_PATHS.json'])
 v4_lean_path=v4_data['mathlib-package-view-lean-path.log'].decode().strip().split(os.pathsep)
 assert v4_lean_path==v4_path_record['actual_LEAN_PATH'] and v4_path_record['relative_path_stage_cwd']==str(root)
 assert [str(P(p)if P(p).is_absolute()else root/P(p))for p in v4_lean_path]==v4_path_record['interpreted_absolute_search_paths']
 for text in v4_lean_path:
  p=PurePosixPath(text);assert text and '\\x00'not in text and '..'not in p.parts and not text.startswith('//')
""".replace("@@PROBE_PAYLOAD@@", repr(probe_payload)).replace("@@PROBE_PIN@@", repr(pin(probe_raw))).replace("@@CACHE_PIN@@", repr(pin(cache_raw))).replace("@@RECEIPT_PAYLOAD@@", repr(receipt_payload)).replace("@@RECEIPT_PIN@@", repr(pin(receipt_bundle))).replace("@@SELECTED_PATHS@@", repr(context["selected_paths"])))

    add("frozen_v3_log_source_map", " original_runtime_bytes={};original_runtime_stats={}\n for name in original_runtime_names:\n  p=previous_out/name;assert p.is_file()and not p.is_symlink()\n", " original_runtime_bytes={};original_runtime_stats={};original_runtime_paths={}\n for name in original_runtime_names:\n  p=(v4_out/'original-v3-runtime-stage-evidence'/name)if name=='runtime-evidence/compiler-commands.jsonl'else previous_out/name\n  original_runtime_paths[name]=p;assert p.is_file()and not p.is_symlink()\n")

    guard_join = """ assert v4_data['runtime-evidence/state.json']==original_runtime_bytes['runtime-evidence/state.json']
 v4_state=json.loads(v4_data['runtime-evidence/state.json']);assert v4_state==prior_state
 live_row=v5_probe['live_guard_log'];assert live_row['path']==prior_state['log']
 live_path=P(live_row['path']);assert live_path.is_file() and not live_path.is_symlink()
 live_before=stamp(live_path);assert live_before==live_row['stat'] and live_before[2]<=1000000
 resume_guard_prefix=fixed_bytes(live_path.read_bytes(),live_row);assert stamp(live_path)==live_before
 assert resume_guard_prefix==base64.b64decode(live_row['base64']) and resume_guard_prefix.startswith(original_guard_prefix)
 assert original_guard_prefix==v4_data['original-v3-runtime-stage-evidence/runtime-evidence/compiler-commands.jsonl']
 assert original_guard_prefix.endswith(b'\\n') and resume_guard_prefix.endswith(b'\\n')
 assert all(not any(str(a).endswith('.lean')for a in row['input_args'])for row in (json.loads(line)for line in resume_guard_prefix.splitlines()if line))
 v4_runprefix=['python3',str(base/'original-tools/run_guarded.py'),'--state',str(v4_out/'runtime-evidence/state.json')]
 v4_expected_commands={'mathlib-package-view-lean-path':v4_runprefix+['lake','env','python3','-c','import os; print(os.environ["LEAN_PATH"])'],'omitted-direct-imports':v4_runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin']}
 v4_processes={};position=len(original_guard_prefix)
 for label,command in v4_expected_commands.items():
  rec=json.loads(v4_data[label+'-process.json']);v4_processes[label]=rec
  assert rec['stage']==label and rec['command']==command and rec['cwd']==str(root)
  assert rec['exit_code']==(0 if label=='mathlib-package-view-lean-path'else 1) and rec['forbidden_source_calls']==[]
  assert rec['log_path']==str(v4_out/(label+'.log')) and rec['log_sha256']==hashlib.sha256(v4_data[label+'.log']).hexdigest()
  a,b=rec['guard_log_start'],rec['guard_log_end'];assert a==position and a<=b<=len(resume_guard_prefix)
  assert [json.loads(line)for line in resume_guard_prefix[a:b].splitlines()if line]==rec['guarded_commands'];position=b
 assert position==len(resume_guard_prefix)
 assert v4_processes['omitted-direct-imports']['stdin_sha256']==hashlib.sha256(compile_audit_text(contract['target']['direct_imports'])).hexdigest()
"""
    before = " assert globals().get('SOURCE_TEXT') and hashlib.sha256(SOURCE_TEXT.encode()).hexdigest()==globals()['SOURCE_SHA256']\n"
    add("authenticate_actual_v4_guard_extension_before_writes", before, guard_join + before)

    before = " protected={};cache_before={};runs=[]\n"
    add("preserve_v4_evidence_without_freezing_live_log", before, before + """ for name,row in v5_probe['files'].items():
  p=v4_out/name;assert stamp(p)==v4_runtime_stats[str(p)];preserve(p,row['sha256'])
 for row in batteries_rows:
  original=row['original'];p=P(original['identity']['path']);assert stamp(p)==row['current']['stat'];cache_before[str(p)]=row['current']['stat']
  if original['module']=='Batteries.Tactic.Lemma':preserve(p,original['identity']['sha256'])
 (out/'READ_ONLY_PACKAGE_PROBE.json').write_bytes(v5_probe_raw)
 preserve(out/'READ_ONLY_PACKAGE_PROBE.json',hashlib.sha256(v5_probe_raw).hexdigest())
 (out/'READ_ONLY_CACHE_PROBE.json').write_bytes(v5_cache_raw)
 preserve(out/'READ_ONLY_CACHE_PROBE.json',hashlib.sha256(v5_cache_raw).hexdigest())
 for name,data in cache_record_bytes.items():
  dest=out/'observed-cache-provenance'/(name if name.endswith('.json')else name+'.json');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);preserve(dest,hashlib.sha256(data).hexdigest())
 save(out/'BATTERIES_CACHE_PROVENANCE.json',{'schema':'p29_original_Batteries_facet_authority_with_auxiliary_cache_provenance_v1','byte_authority':'Unchanged accepted P2_DECLARED_FACETS.jsonl e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636; every selected module/facet/physical-path/size/SHA256 rejoined before view links','probe_sha256':hashlib.sha256(v5_cache_raw).hexdigest(),'observed_records':{name:{k:v for k,v in row.items()if k!='base64'}for name,row in v5_cache['records'].items()},'receipt_status':batteries_receipt['status'],'receipt_is_auxiliary_observed_provenance_not_qualification_authority':True,'raw_snapshot_receipt_file_entry_binding_observed':bool(v5_cache['original_snapshot_file_entries']),'original_snapshot_file_entries':v5_cache['original_snapshot_file_entries'],'all960_current_facets_metadata_verified':True,'metadata_only_facets_in_probe':955,'full_current_hash_facets_in_probe':5,'current_full_hashes_in_probe_modules':['Batteries.Tactic.Lemma'],'every_used_facet_full_current_hash_and_header_still_required':True,'source_recompilation_or_cache_restoration':False,'new_formal_credit':0})
 combined_snapshot=out/'ORIGINAL_V3_V4_GUARD_PREFIX.jsonl';combined_snapshot.write_bytes(resume_guard_prefix)
 preserve(combined_snapshot,hashlib.sha256(resume_guard_prefix).hexdigest())
 for name,data in v4_submission_bytes.items():
  dest=out/'original-v4-submission'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data);preserve(dest,hashlib.sha256(data).hexdigest())
 save(out/'ORIGINAL_STANDARD_PACKAGE_FAILURE_REUSE.json',{'schema':'p29_same_runtime_standard_package_view_resume_v1','original_v4_task':'a691a4c888044726ad49f92170e3c8f5','original_v4_evidence':str(v4_out),'original_v4_file_pins':{name:{k:row[k]for k in ['bytes','sha256','stat']}for name,row in v5_probe['files'].items()},'original_v4_failure':v4_failure,'original_v3_guard_prefix_bytes':len(original_guard_prefix),'original_v3_guard_prefix_sha256':hashlib.sha256(original_guard_prefix).hexdigest(),'combined_v3_v4_guard_prefix_bytes':len(resume_guard_prefix),'combined_v3_v4_guard_prefix_sha256':hashlib.sha256(resume_guard_prefix).hexdigest(),'reused_successful_stages':['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','mathlib-package-view-lean-path'],'old_successful_stage_reinvocations':0,'original_guard_setup_reinvocations':0,'supplier_source_kernel_owned_replays':0,'actual_current_header_facet_union_still_required':True})
""")
    add("preserve_original_runtime_by_explicit_logical_name", " for p,before in original_runtime_stats.items():\n  assert stamp(p)==before\n  if p!=prior_state['log']:preserve(p,hashlib.sha256(original_runtime_bytes[str(P(p).relative_to(previous_out))]).hexdigest())\n", " for name,p in original_runtime_paths.items():\n  assert stamp(p)==original_runtime_stats[str(p)]\n  assert str(p)!=prior_state['log']\n  preserve(p,hashlib.sha256(original_runtime_bytes[name]).hexdigest())\n")

    before = line(" save(out/'COMPLETE_SELECTED_NATIVE_NAMESPACE_VIEW.json'")
    add("separate_Batteries_only_view_from_exact_original_facet_table", before, before + """ # Batteries is a separate accepted standard namespace, not research qualification.
 assert not ({m for m,f in batteries_keys}&qualified_research)
 assert batteries_keys=={(m,f)for m,f in expected_origins if m=='Batteries'or m.startswith('Batteries.')}
 assert not v5_view.exists() and not v5_view.is_symlink();v5_view.mkdir();batteries_lib.mkdir()
 batteries_links=[]
 for observed in batteries_rows:
  original=observed['original'];mod=original['module'];facet=original['facet'];key=(mod,facet)
  pin=expected_origins[key];assert key not in old_by_part and original['identity']=={k:pin[k]for k in ['path','bytes','sha256']}
  current=P(pin['path']);resolved=current.resolve(strict=True);st=stamp(current)
  assert current.is_file() and not current.is_symlink() and current==resolved and st==observed['current']['stat']==cache_before[str(current)] and st[2]==pin['bytes']
  dest=batteries_lib/(mod.replace('.','/')+facet);dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists() and not dest.is_symlink();dest.symlink_to(current)
  assert dest.resolve(strict=True)==resolved;cache_before[str(dest)]=st
  provider={'original_selected_path':str(current),'original_snapshot_sha256':contract['external_snapshot_sha256'],'original_derived_table_sha256':'e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636','observed_cache_probe_sha256':hashlib.sha256(v5_cache_raw).hexdigest(),'observed_overlay_receipt_sha256':v5_cache['records']['batteries_receipt']['sha256'],'overlay_receipt_is_auxiliary_provenance_not_qualification':True}
  old_by_part[key]={'module':mod,'facet':facet,'identity':{'path':str(resolved),'bytes':pin['bytes'],'sha256':pin['sha256']},'stat_snapshot':st,'authority':'original_accepted_Batteries_native_cache','provider':provider}
  batteries_links.append({'module':mod,'facet':facet,'requested_path':str(dest),'selected_path':str(current),'bytes':pin['bytes'],'sha256':pin['sha256']})
 assert {m for m,f in old_by_part}==qualified_research|{m for m,f in batteries_keys} and len(qualified_research)==529
 assert {p.relative_to(batteries_lib).as_posix()for p in batteries_lib.rglob('*')if p.is_symlink()}=={m.replace('.','/')+f for m,f in batteries_keys}
 assert all(p.is_dir()and not p.is_symlink()or p.is_symlink()and p.is_file()for p in batteries_lib.rglob('*'))
 save(out/'COMPLETE_SELECTED_BATTERIES_NAMESPACE_VIEW.json',{'schema':'p29_exact_original_Batteries_only_symlink_view_v1','modules':192,'facets':batteries_links,'owned_view':str(batteries_lib),'selected_cache_root':str(batteries_cache),'byte_authority_table_sha256':'e9edf9226c45934541d576c76ca7f3041bf3c73c703e51b3162dd69dcbe68636','research_modules_remain':529,'other_native_cache_namespaces_exposed':False,'metadata_only_before_actual_import':True,'fresh_actual_headers_and_full_used_facet_hashes_still_required':True,'restoration_replays':0,'source_compilations':0,'new_formal_credit':0})
""")
    start = source.index(" packages=root/'.lake/packages';assert packages.is_symlink()")
    end = source.index(" cfg=tomllib.loads((root/'lakefile.toml').read_text())", start)
    add("retain_existing_v4_package_view_without_replacement", source[start:end], """ packages=root/'.lake/packages';package_view=base/'packages-mathlib-resume-v4'
 assert packages.is_symlink() and os.readlink(packages)==str(package_view)
 assert not root.is_symlink() and not (root/'.lake').is_symlink() and package_view.is_dir() and not package_view.is_symlink()
 package_rows=json.loads((root/'lake-manifest.json').read_text())['packages']
 assert len(package_rows)==10 and len({r['name']for r in package_rows})==10
 package_paths={name:P(path)for name,path in v4_package_paths.items()}
 assert set(package_paths)=={r['name']for r in package_rows} and {p.name for p in package_view.iterdir()}==set(package_paths)
 for name,path in package_paths.items():
  link=package_view/name;assert link.is_symlink() and os.readlink(link)==str(path)
 assert package_paths['LeanArchitect']==P('/workspace/goldbach-p2/.lake/packages/LeanArchitect')
 mathlib=package_paths['mathlib'];assert mathlib==P('/workspace/compile-deps/mathlib') and mathlib.is_dir()
 assert P(subprocess.check_output(['git','-C',str(mathlib),'rev-parse','--show-toplevel'],text=True).strip()).resolve()==mathlib.resolve()
 assert subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()==next(r['rev']for r in package_rows if r['name']=='mathlib')=='e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'
 save(out/'REUSED_V4_PACKAGE_VIEW.json',{'schema':'p29_unchanged_v4_ten_package_view_reuse_v1','view':str(package_view),'package_link':str(packages),'link_target':os.readlink(packages),'selected_package_paths':v4_package_paths,'changed_package_providers':[],'original_v4_repair_sha256':hashlib.sha256(v4_data['PACKAGE_VIEW_REPAIR.json']).hexdigest(),'config_bytes_and_all_ten_manifest_pins_unchanged':True,'LeanArchitect_path_and_pin_retained_without_claim_of_new_checkout_qualification':True,'Batteries_native_cache_selected_only_in_separate_owned_namespace_view':str(batteries_lib),'metadata_probe_is_not_actual_import_qualification':True,'all_current_input_bytes_headers_and_facets_still_required':True})
""")
    add("guard_resume_uses_complete_v3_v4_prefix", " assert guardlog.read_bytes()==original_guard_prefix\n", " assert guardlog.read_bytes()==resume_guard_prefix\n")

    add("historical_v4_path_reuse_and_fresh_composed_view_observation", " stage('mathlib-package-view-lean-path',runprefix+['lake','env','python3','-c','import os; print(os.environ[\"LEAN_PATH\"])'])\n actual_lean_path=(out/'mathlib-package-view-lean-path.log').read_text().strip().split(os.pathsep)\n", """ (out/'REUSED_V4_MATHLIB_LEAN_PATH.log').write_bytes(v4_data['mathlib-package-view-lean-path.log'])
 save(out/'REUSED_V4_SUCCESSFUL_PATH_STAGE.json',{'schema':'p29_historical_successful_path_stage_preserved_v1','original_task':'a691a4c888044726ad49f92170e3c8f5','original_process':v4_processes['mathlib-package-view-lean-path'],'original_process_sha256':hashlib.sha256(v4_data['mathlib-package-view-lean-path-process.json']).hexdigest(),'original_log_sha256':hashlib.sha256(v4_data['mathlib-package-view-lean-path.log']).hexdigest(),'original_stage_reinvocations':0,'fresh_Lake_env_observation':False,'historical_record_not_relabelled_current':True,'new_composed_view_observation_follows':True})
 composed_path=os.pathsep.join([str(lib),str(batteries_lib),*v4_lean_path])
 assert not any(os.pathsep in p for p in [str(lib),str(batteries_lib)])
 viewprefix=runprefix+['lake','env','env','LEAN_PATH='+composed_path]
 stage('batteries-composed-view-observation',viewprefix+['python3','-c','import json,os; print(json.dumps({"cwd":os.getcwd(),"LEAN_PATH":os.environ["LEAN_PATH"]}))'])
 composed_observation=json.loads((out/'batteries-composed-view-observation.log').read_text())
 assert composed_observation=={'cwd':str(root),'LEAN_PATH':composed_path}
 actual_lean_path=composed_observation['LEAN_PATH'].split(os.pathsep)
 assert actual_lean_path[:2]==[str(lib),str(batteries_lib)] and actual_lean_path[2:]==v4_lean_path
""")
    add("Batteries_first_namespace_assertion", " for prefix in sorted({'Mathlib','ImbalancedChen'}|{m.split('.')[0]for m in qualified_research}):\n", " for prefix in sorted({'Mathlib','ImbalancedChen','Batteries'}|{m.split('.')[0]for m in qualified_research}):\n")
    add("exact_Batteries_first_namespace_root", "  expected=(P('/workspace/compile-deps/mathlib/.lake/build/lib/lean')if prefix=='Mathlib'else lib)\n", "  expected=(P('/workspace/compile-deps/mathlib/.lake/build/lib/lean')if prefix=='Mathlib'else batteries_lib if prefix=='Batteries'else lib)\n")
    add("label_new_composed_path_observation_honestly", line(" save(out/'ACTUAL_FIRST_NAMESPACE_PATHS.json'"), " save(out/'ACTUAL_FIRST_NAMESPACE_PATHS.json',{'schema':'p29_fresh_explicit_composed_view_first_namespace_paths_v1','original_tail_task':'a691a4c888044726ad49f92170e3c8f5','original_tail_process_sha256':hashlib.sha256(v4_data['mathlib-package-view-lean-path-process.json']).hexdigest(),'original_raw_LEAN_PATH_tail':v4_lean_path,'actual_LEAN_PATH':actual_lean_path,'relative_path_stage_cwd':str(root),'interpreted_absolute_search_paths':[str(p)for p in actual_search_paths],'selected_first_namespace_roots':prefix_selections,'fresh_composed_view_observation':True,'fresh_reobservation_of_unmodified_Lake_baseline_path':False,'original_stage_reinvocations':0,'explicit_prefix':viewprefix,'original_runtime_audit_runprefix':runprefix,'compiled_header_full_facet_probe_still_required':True})\n")
    add("final_append_only_check_covers_both_prior_attempts", " with guardlog.open('rb')as f:assert f.read(len(original_guard_prefix))==original_guard_prefix\n", " with guardlog.open('rb')as f:assert f.read(len(resume_guard_prefix))==resume_guard_prefix\n assert resume_guard_prefix[:len(original_guard_prefix)]==original_guard_prefix\n")
    before = " for name in contract['action_script_sha256']:members['original-action-scripts/'+name]=action/'scripts'/name\n"
    add("include_original_v4_attempt_in_complete_archive", before, """ for p in v4_out.rglob('*'):
  if p.is_file()and p!=guardlog:
   assert not p.is_symlink();members['original-mathlib-attempt-v4/'+str(p.relative_to(v4_out))]=p
 for name,data in v4_submission_bytes.items():assert (out/'original-v4-submission'/name).read_bytes()==data
 assert (out/'ORIGINAL_V3_V4_GUARD_PREFIX.jsonl').read_bytes()==resume_guard_prefix
""" + before)
    return changes
