import ast,base64,difflib,hashlib,json,pathlib,zlib

D=pathlib.Path('/dev/shm/p29-omitted-controller-1126')
old=(D/'omitted-prime-wall-P2-import-order-resume-v3-postimage.py').read_text()
assert hashlib.sha256(old.encode()).hexdigest()=='4cf893cb8afac435e9a5286fc101db03e55991fe93e38ef1afadac400c84be77'
def sha(b):return hashlib.sha256(b).hexdigest()
def oid(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
originals={}
for name in ['OMITTED_P2_V3_ACTUAL_REQUEST.json','OMITTED_P2_V3_ACTUAL_TASK_JOIN.json','OMITTED_P2_V3_FRESH_SERVICE_OBSERVATION.json','OMITTED_P2_V3_TERMINAL_TASK.json','OMITTED_P2_V3_ORIGINAL_STDOUT.log']:
 b=(D/name).read_bytes();originals[name]={'bytes':len(b),'sha256':sha(b),'git_blob':oid(b),'base64':base64.b64encode(b).decode()}
changes=[]
def replace(a,b):
 global old
 assert old.count(a)==1,(a[:120],old.count(a))
 changes.append((a,b));old=old.replace(a,b)

replace("FIXED_CONTRACT_SHA256='1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf'\n", "FIXED_CONTRACT_SHA256='1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf'\nPRIOR_ATTEMPT_ORIGINALS="+repr(originals)+"\n")
replace("base=P(contract['receiver_root']);root=base/'project';previous_out=base/'verification';out=base/'verification-import-order-resume-v3'", "base=P(contract['receiver_root']);root=base/'project';first_out=base/'verification';previous_out=base/'verification-import-order-resume-v3';out=base/'verification-mathlib-path-resume-v4'")
replace("previous_pins={'driver.py':'945a19ceecfd707c5fa801ca9ce4f170755c9bbe363079293198e40bacc09970','INPUT_CONTRACT.json':'1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf','FAILURE.json':'2c0e2b27ce353d0da8d4a268b11a7edc03e7e017fdd7c3c70adf40c13e74942d'}", "previous_pins={'driver.py':'4cf893cb8afac435e9a5286fc101db03e55991fe93e38ef1afadac400c84be77','INPUT_CONTRACT.json':'1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf','FAILURE.json':'f0bc1c4e8606c33f2b6ac1573fda2df81da400f5d70cd4da8fb5707317190deb'}\n first_pins={'driver.py':'945a19ceecfd707c5fa801ca9ce4f170755c9bbe363079293198e40bacc09970','INPUT_CONTRACT.json':'1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf','FAILURE.json':'2c0e2b27ce353d0da8d4a268b11a7edc03e7e017fdd7c3c70adf40c13e74942d'}\n for name,pin in first_pins.items():assert sha(first_out/name)==pin")
replace("assert previous_failure['completed_stages']==[] and previous_failure['supplier_source_kernel_owned_replays']==0", "assert previous_failure['completed_stages']==['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','omitted-direct-imports'] and previous_failure['supplier_source_kernel_owned_replays']==0\n assert previous_failure['error']=='Gate failed: omitted-direct-imports'")
anchor=" assert globals().get('SOURCE_TEXT') and hashlib.sha256(SOURCE_TEXT.encode()).hexdigest()==globals()['SOURCE_SHA256']\n"
validation=''' # Authenticate the original request/result and all prior runtime evidence
 # before any new write or package-view change. Nothing here invokes Lean.
 original_attempt_inputs={name:fixed_bytes(base64.b64decode(row['base64']),row)for name,row in PRIOR_ATTEMPT_ORIGINALS.items()}
 previous_request=json.loads(original_attempt_inputs['OMITTED_P2_V3_ACTUAL_REQUEST.json'])
 previous_task=json.loads(original_attempt_inputs['OMITTED_P2_V3_TERMINAL_TASK.json'])
 previous_join=json.loads(original_attempt_inputs['OMITTED_P2_V3_ACTUAL_TASK_JOIN.json'])
 previous_stdout=original_attempt_inputs['OMITTED_P2_V3_ORIGINAL_STDOUT.log'].decode()
 assert {k:previous_request[k]for k in ['cwd','memory_mb','cpu_threads','timeout_seconds']}=={'cwd':'/workspace','memory_mb':12800,'cpu_threads':2,'timeout_seconds':3600}
 assert hashlib.sha256(previous_request['command'].encode()).hexdigest()=='d1ad854c5d218ba85f092d4dc80fcb2e68251ff41fa6c20a16410c2042a1fdb9'
 assert previous_task['task_id']==previous_task['job_id']==previous_join['job_id']=='8e56fa2b36794145bc6e2549bfee9b68'
 assert previous_task['status']=='failed' and previous_task['exit_code']==1 and previous_task['log_bytes']==len(previous_stdout.encode())==2564
 assert previous_task['log_discarded_bytes']==0 and previous_task['log_truncated']is False
 assert previous_task['submitted_at']==previous_join['get_task_submitted_at'] and previous_join['actual_requested_limits_equal']is True
 assert previous_join['request_git_blob']==PRIOR_ATTEMPT_ORIGINALS['OMITTED_P2_V3_ACTUAL_REQUEST.json']['git_blob']=='f8d4caa16fc57b56fe99d0201110fe86d87b9581'
 assert 0<=previous_join['submission_seconds_after_fresh_observation']<=previous_join['submission_window_max_seconds']==300
 assert json.loads(next(line[len('P29_FAILURE '):]for line in previous_stdout.splitlines()if line.startswith('P29_FAILURE ')))==previous_failure
 assert (previous_out/'SERVICE_OBSERVATION.json').read_bytes()==original_attempt_inputs['OMITTED_P2_V3_FRESH_SERVICE_OBSERVATION.json']
 original_runtime_names=['runtime-setup-process.json','runtime-setup.log','runtime-evidence/state.json','runtime-evidence/audit.json','INITIAL_RUNTIME_REPORT_PRESERVED.json','runtime-evidence/compiler-commands.jsonl']
 for label in ['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix','omitted-direct-imports']:
  original_runtime_names.extend([label+'-process.json',label+'.log'])
 original_runtime_bytes={};original_runtime_stats={}
 for name in original_runtime_names:
  p=previous_out/name;assert p.is_file()and not p.is_symlink()
  before=stamp(p);assert before[2]<=1024*1024
  raw_prior=p.read_bytes();assert stamp(p)==before
  original_runtime_bytes[name]=raw_prior;original_runtime_stats[str(p)]=before
 assert sum(map(len,original_runtime_bytes.values()))<=8*1024*1024
 prior_state_path=previous_out/'runtime-evidence/state.json'
 prior_state=json.loads(original_runtime_bytes['runtime-evidence/state.json'])
 assert prior_state['schema']=='p0-ci-runtime-v1' and prior_state['root']==str(root)
 assert prior_state['policy']=='Lean -t0 -j2 -M12288; serial compiler slot; native compiler flags preserved; native checker LEAN_NUM_THREADS=2'
 assert prior_state['guard_sha256']==contract['original_tools_members']['original-tools/ci_runtime_guard.py']['sha256']
 assert prior_state['action_commit']==contract['action_commit']
 assert prior_state['environment']['P0_CI_GUARD_STATE']==str(prior_state_path)
 assert prior_state['log']==str(previous_out/'runtime-evidence/compiler-commands.jsonl')
 assert prior_state['realbin']==str(P('/workspace/toolchains/lean-4.33.0-rc1-linux/bin'))
 assert prior_state['shadow']==str(base/'runtime/p0-ci-shadow-toolchain')
 assert prior_state['input_sha256']=={str(root/name):pin['sha256']for name,pin in contract['configuration'].items()}
 assert prior_state['action_script_sha256']=={str(base/'lean-action/scripts'/name):pin for name,pin in contract['action_script_sha256'].items()}
 for mapping in ['runtime_sha256','input_sha256','action_script_sha256']:
  for p,pin in prior_state[mapping].items():assert sha(p)==pin
 original_guard_prefix=original_runtime_bytes['runtime-evidence/compiler-commands.jsonl']
 prior_guard_rows=[json.loads(line)for line in original_guard_prefix.splitlines()if line]
 assert prior_guard_rows and all(not any(str(a).endswith('.lean')for a in row['input_args'])for row in prior_guard_rows)
 original_setup=json.loads(original_runtime_bytes['runtime-setup-process.json'])
 assert original_setup['exit_code']==0 and original_setup['cwd']==str(root)
 assert original_setup['command']==['python3',str(base/'original-tools/ci_runtime_guard.py'),'setup','--evidence',str(previous_out/'runtime-evidence')]
 assert original_setup['log_sha256']==hashlib.sha256(original_runtime_bytes['runtime-setup.log']).hexdigest()
 prior_runprefix=['python3',str(base/'original-tools/run_guarded.py'),'--state',str(prior_state_path)]
 expected_previous_commands={
  'runtime-initial-audit':prior_runprefix+['python3',str(base/'original-tools/ci_runtime_guard.py'),'audit','--state',str(prior_state_path),'--probe'],
  'pinned-lean-version':prior_runprefix+['lake','env','lean','--version'],
  'pinned-lean-prefix':prior_runprefix+['lake','env','lean','--print-prefix'],
  'omitted-direct-imports':prior_runprefix+['lake','env','lean','-DmaxRecDepth=100000','-DmaxHeartbeats=4000000','--stdin']}
 previous_processes={}
 for label,command in expected_previous_commands.items():
  rec=json.loads(original_runtime_bytes[label+'-process.json']);previous_processes[label]=rec
  assert rec['stage']==label and rec['command']==command and rec['cwd']==str(root)
  assert rec['exit_code']==(1 if label=='omitted-direct-imports'else 0) and rec['forbidden_source_calls']==[]
  assert rec['log_path']==str(previous_out/(label+'.log')) and rec['log_sha256']==hashlib.sha256(original_runtime_bytes[label+'.log']).hexdigest()
  a,b=rec['guard_log_start'],rec['guard_log_end'];assert 0<=a<=b<=len(original_guard_prefix)
  assert [json.loads(line)for line in original_guard_prefix[a:b].splitlines()if line]==rec['guarded_commands']
 failed=previous_processes['omitted-direct-imports']
 assert failed['stdin_sha256']==hashlib.sha256(compile_audit_text(contract['target']['direct_imports'])).hexdigest()
 assert original_runtime_bytes['omitted-direct-imports.log']==b"<stdin>:29:0: error: object file '/workspace/goldbach-p2/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/NumberTheory/AlmostPrime.olean' of module Mathlib.NumberTheory.AlmostPrime does not exist\\n"
 prior_audit=json.loads(original_runtime_bytes['INITIAL_RUNTIME_REPORT_PRESERVED.json'])
 assert prior_audit==json.loads(original_runtime_bytes['runtime-evidence/audit.json'])
 assert prior_audit['status']=='PASS_RUNTIME_GUARD_ONLY' and prior_audit['source_commands']==0 and prior_audit['probe']is True
 assert prior_audit['state_sha256']==hashlib.sha256(original_runtime_bytes['runtime-evidence/state.json']).hexdigest()
 audited_prefix=b''.join(original_guard_prefix.splitlines(keepends=True)[:prior_audit['compiler_commands']])
 assert prior_audit['command_log_sha256']==hashlib.sha256(audited_prefix).hexdigest()
 assert 'version 4.33.0-rc1,'in original_runtime_bytes['pinned-lean-version.log'].decode() and 'commit 62eed1db4d67327ec8120be05f1a1b0847d74561,'in original_runtime_bytes['pinned-lean-version.log'].decode()
 assert original_runtime_bytes['pinned-lean-prefix.log'].decode().strip()==prior_state['shadow']
'''
replace(anchor,validation+anchor)
replace("save(out/'ORIGINAL_PRE_LEAN_FAILURE_REUSE.json',{'schema':'p29_omitted_same_root_pre_Lean_import_order_resume_v1','original_job_id':'1dfcb781103d4426b860b7ffe3ebc8cd','original_evidence':str(previous_out),'original_file_sha256':previous_pins,'original_failure':previous_failure,'cached_original_authorities_normal_records_target_source_reused':True,'old_Lean_stages_replayed':0,'original_failed_evidence_not_modified':True})", "save(out/'ORIGINAL_IMPORT_FAILURE_REUSE.json',{'schema':'p29_omitted_same_runtime_mathlib_package_view_resume_v1','original_job_id':'8e56fa2b36794145bc6e2549bfee9b68','original_evidence':str(previous_out),'original_file_sha256':previous_pins,'original_failure':previous_failure,'reused_successful_stages':['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix'],'cached_original_authorities_normal_records_target_source_reused':True,'old_successful_Lean_stages_replayed':0,'original_failed_evidence_not_modified_except_append_only_guard_log':True,'original_guard_prefix_bytes':len(original_guard_prefix),'original_guard_prefix_sha256':hashlib.sha256(original_guard_prefix).hexdigest()})\n for name,data in original_attempt_inputs.items():\n  dest=out/'original-v3-submission'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)\n for name,data in original_runtime_bytes.items():\n  dest=out/'original-v3-runtime-stage-evidence'/name;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(data)\n for name,pin in first_pins.items():preserve(first_out/name,pin)\n for p,before in original_runtime_stats.items():\n  assert stamp(p)==before\n  if p!=prior_state['log']:preserve(p,hashlib.sha256(original_runtime_bytes[str(P(p).relative_to(previous_out))]).hexdigest())")
replace("else:\n   assert not dest.exists();dest.symlink_to(P(object_path).resolve(strict=True))", "else:raise AssertionError('A previously materialized project symlink is missing: '+str(dest))")
replace(" external_archive=fixed_bytes(get_blob(contract['external_derived_archive']['git_blob']),contract['external_derived_archive'])\n derived=capture_members(external_archive,contract['external_derived_members'],out/'original-external-derived')", " derived={}\n for name,pin in contract['external_derived_members'].items():\n  p=previous_out/'original-external-derived'/name;assert p.is_file()and not p.is_symlink()\n  before=stamp(p);fixed_bytes(p.read_bytes(),pin);assert stamp(p)==before;preserve(p,pin['sha256']);derived[name]=p")
replace("dest=lib/(mod.replace('.','/')+facet);assert not dest.exists() and not dest.is_symlink()\n  dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(resolved)", "dest=lib/(mod.replace('.','/')+facet);assert dest.is_symlink() and dest.resolve(strict=True)==resolved")
replace("  (root/name).write_bytes(data)\n (root/'.lake/packages').symlink_to('/workspace/goldbach-p2/.lake/packages',target_is_directory=True)", "  assert (root/name).read_bytes()==data\n packages=root/'.lake/packages';assert packages.is_symlink() and os.readlink(packages)=='/workspace/goldbach-p2/.lake/packages'\n assert not root.is_symlink() and not (root/'.lake').is_symlink()\n package_view=base/'packages-mathlib-resume-v4';assert not package_view.exists() and not package_view.is_symlink()\n package_rows=json.loads((root/'lake-manifest.json').read_text())['packages']\n assert len(package_rows)==10 and len({r['name']for r in package_rows})==10\n package_paths={r['name']:(P('/workspace/compile-deps/mathlib')if r['name']=='mathlib'else P('/workspace/goldbach-p2/.lake/packages')/r['name'])for r in package_rows}\n assert package_paths['LeanArchitect']==P('/workspace/goldbach-p2/.lake/packages/LeanArchitect')\n mathlib=package_paths['mathlib'];assert mathlib.is_dir()\n assert P(subprocess.check_output(['git','-C',str(mathlib),'rev-parse','--show-toplevel'],text=True).strip()).resolve()==mathlib.resolve()\n assert subprocess.check_output(['git','-C',str(mathlib),'rev-parse','HEAD'],text=True).strip()==next(r['rev']for r in package_rows if r['name']=='mathlib')=='e4c91783ca8e6a7c693ae624ade32fd22d4e43c1'\n package_view.mkdir()\n for name,path in package_paths.items():(package_view/name).symlink_to(path,target_is_directory=True)\n old_package_link={'path':str(packages),'link_target':os.readlink(packages),'lstat':[packages.lstat().st_dev,packages.lstat().st_ino,packages.lstat().st_mtime_ns,packages.lstat().st_ctime_ns]}\n save(out/'PACKAGE_VIEW_REPAIR.json',{'schema':'p29_owned_last_component_package_symlink_repair_v1','original_link':old_package_link,'new_view':str(package_view),'selected_package_paths':{name:str(p)for name,p in package_paths.items()},'only_changed_package_provider':'mathlib','mathlib_original_accepted_snapshot_sha256':contract['external_snapshot_sha256'],'config_bytes_and_all_ten_manifest_pins_unchanged':True,'LeanArchitect_path_and_pin_retained_without_claim_of_new_checkout_qualification':True,'all_current_input_bytes_headers_and_facets_still_required':True})\n assert packages.is_symlink() and os.readlink(packages)==old_package_link['link_target']\n packages.unlink();packages.symlink_to(package_view,target_is_directory=True)")
start=" unit=next(a for a in receive['archives']if a['group']=='unit128')\n"
end=" runtime_parent=base/'runtime';runtime_parent.mkdir();base_env=os.environ.copy()\n"
a=old[old.index(start):old.index(end)+len(end)]
b=""" # The three original tools and genuine pinned action checkout already exist.
 tools_expected={}
 for member,pin in contract['original_tools_members'].items():
  p=base/member;assert p.is_file()and not p.is_symlink();preserve(p,pin['sha256']);tools_expected[str(p)]=pin['sha256']
 GUARD=base/'original-tools/ci_runtime_guard.py';RUNNER=base/'original-tools/run_guarded.py';OWNED=base/'original-tools/validate_member_roots_owned.py'
 action=base/'lean-action';assert action.is_dir()
 assert subprocess.check_output(['git','-C',str(action),'rev-parse','HEAD'],text=True).strip()==contract['action_commit']
 for name,h in contract['action_script_sha256'].items():preserve(action/'scripts'/name,h)
 preserve(previous_out/'ACTION_CHECKOUT_PROCESS.json')
 runtime_parent=base/'runtime';assert runtime_parent.is_dir();base_env=os.environ.copy()
"""
replace(a,b)
a=""" setup_cmd=['python3',str(GUARD),'setup','--evidence',str(out/'runtime-evidence')]
 with (out/'runtime-setup.log').open('xb')as f:res=subprocess.run(setup_cmd,cwd=root,env=base_env,stdout=f,stderr=subprocess.STDOUT,timeout=240)
 save(out/'runtime-setup-process.json',{'command':setup_cmd,'cwd':str(root),'exit_code':res.returncode,'log_sha256':sha(out/'runtime-setup.log')})
 assert res.returncode==0,'Original guard setup failed; inspect runtime-setup.log'
 state_path=out/'runtime-evidence/state.json';state=json.loads(state_path.read_text());state_sha=sha(state_path);guardlog=P(state['log'])
"""
b=""" # Copy only the original state bytes; do not rerun setup or regenerate wrappers.
 # The original environment/slot/log/shadow paths remain byte-identical.
 # Final audit writes beside this copied state, preserving the original audit.json.
 state_path=out/'runtime-evidence/state.json';state_path.parent.mkdir()
 state_path.write_bytes(original_runtime_bytes['runtime-evidence/state.json'])
 state=json.loads(state_path.read_text());state_sha=sha(state_path);guardlog=P(state['log'])
 assert state==prior_state and state_sha==prior_audit['state_sha256']
 assert guardlog.read_bytes()==original_guard_prefix
"""
replace(a,b)
a=""" stage('runtime-initial-audit',runprefix+['python3',str(GUARD),'audit','--state',str(state_path),'--probe'])
 save(out/'INITIAL_RUNTIME_REPORT_PRESERVED.json',json.loads((out/'runtime-evidence/audit.json').read_text()))
 stage('pinned-lean-version',runprefix+['lake','env','lean','--version'])
 version=(out/'pinned-lean-version.log').read_text();assert 'version 4.33.0-rc1,'in version and 'commit '+LEAN_COMMIT+','in version
 stage('pinned-lean-prefix',runprefix+['lake','env','lean','--print-prefix'])
 assert (out/'pinned-lean-prefix.log').read_text().strip()==state['shadow']
"""
b=""" save(out/'REUSED_THREE_SUCCESSFUL_RUNTIME_STAGES.json',{'schema':'p29_exact_existing_stage_process_log_reuse_v1','original_task':'8e56fa2b36794145bc6e2549bfee9b68','original_state_sha256':state_sha,'processes':{label:previous_processes[label]for label in ['runtime-initial-audit','pinned-lean-version','pinned-lean-prefix']},'raw_originals':'original-v3-runtime-stage-evidence','original_stage_reinvocations':0,'original_guard_setup_reinvocations':0})
"""
replace(a,b)
a=" before=actual_inputs('omitted-direct-imports',source_imports)\n"
b=""" stage('mathlib-package-view-lean-path',runprefix+['lake','env','python3','-c','import os; print(os.environ["LEAN_PATH"])'])
 actual_lean_path=(out/'mathlib-package-view-lean-path.log').read_text().strip().split(os.pathsep)
 assert actual_lean_path and all(actual_lean_path)
 prefix_selections={}
 for prefix in sorted({'Mathlib','ImbalancedChen'}|{m.split('.')[0]for m in qualified_research}):
  chosen=next((P(p)for p in actual_lean_path if (P(p)/prefix).is_dir()or(P(p)/(prefix+'.olean')).exists()),None)
  assert chosen is not None,('Missing actual namespace prefix',prefix)
  expected=(P('/workspace/compile-deps/mathlib/.lake/build/lib/lean')if prefix=='Mathlib'else lib)
  assert chosen.resolve()==expected.resolve(),('Unexpected first namespace root',prefix,str(chosen),str(expected))
  prefix_selections[prefix]={'first_path':str(chosen),'resolved_path':str(chosen.resolve())}
 save(out/'ACTUAL_FIRST_NAMESPACE_PATHS.json',{'schema':'p29_actual_lake_env_first_namespace_paths_v1','actual_LEAN_PATH':actual_lean_path,'selected_first_namespace_roots':prefix_selections,'compiled_header_full_facet_probe_still_required':True})
 before=actual_inputs('omitted-direct-imports',source_imports)
"""
replace(a,b)
replace(" stable();assert source_outputs()==produced and sha(src)==source_sha\n", " stable();assert source_outputs()==produced and sha(src)==source_sha\n with guardlog.open('rb')as f:assert f.read(len(original_guard_prefix))==original_guard_prefix\n assert sha(previous_out/'runtime-evidence/audit.json')==hashlib.sha256(original_runtime_bytes['runtime-evidence/audit.json']).hexdigest()\n (out/'runtime-evidence/compiler-commands-combined.jsonl').write_bytes(guardlog.read_bytes())\n assert sha(out/'runtime-evidence/compiler-commands-combined.jsonl')==json.loads((out/'runtime-evidence/audit.json').read_text())['command_log_sha256']\n")
replace(" for name in previous_pins:members['original-first-attempt/'+name]=previous_out/name", " for name in first_pins:members['original-first-attempt/'+name]=first_out/name\n for p in previous_out.rglob('*'):\n  if p.is_file()and p!=guardlog:\n   assert not p.is_symlink();members['original-import-attempt-v3/'+str(p.relative_to(previous_out))]=p")

source=old.encode();name='omitted-prime-wall-P2-mathlib-path-resume-v4-postimage.py'
(D/name).write_bytes(source)
baseline=(D/'omitted-prime-wall-P2-import-order-resume-v3-postimage.py').read_text()
patch=''.join(difflib.unified_diff(baseline.splitlines(True),old.splitlines(True),fromfile='original-v3.py',tofile=name))
(D/'OMITTED_P2_MATHLIB_PATH_RESUME_V3_TO_V4.patch').write_text(patch)
for a,b in reversed(changes):
 assert old.count(b)==1
 old=old.replace(b,a)
assert old==baseline
oldtree,newtree=ast.parse(baseline),ast.parse(source)
of={n.name:ast.dump(n,include_attributes=False)for n in oldtree.body if isinstance(n,ast.FunctionDef)}
nf={n.name:ast.dump(n,include_attributes=False)for n in newtree.body if isinstance(n,ast.FunctionDef)}
assert of.keys()==nf.keys() and [n for n in of if of[n]!=nf[n]]==['main']
oldassign={n.targets[0].id:ast.dump(n,include_attributes=False)for n in oldtree.body if isinstance(n,ast.Assign)and isinstance(n.targets[0],ast.Name)}
newassign={n.targets[0].id:ast.dump(n,include_attributes=False)for n in newtree.body if isinstance(n,ast.Assign)and isinstance(n.targets[0],ast.Name)}
assert all(oldassign[n]==newassign[n]for n in oldassign)
bootstrap="""import pathlib,hashlib,json
p=pathlib.Path('/workspace/p29-omitted-prime-wall-p2-20261126-ef40c77/verification-import-order-resume-v3')
source=(p/'driver.py').read_text()
assert hashlib.sha256(source.encode()).hexdigest()=='4cf893cb8afac435e9a5286fc101db03e55991fe93e38ef1afadac400c84be77'
changes=CHANGES_REPR
for before,after in changes:
 assert source.count(before)==1
 source=source.replace(before,after)
assert hashlib.sha256(source.encode()).hexdigest()=='POSTIMAGE_SHA'
contract=(p/'INPUT_CONTRACT.json').read_text()
assert hashlib.sha256(contract.encode()).hexdigest()=='1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf'
exec(compile(source,'omitted-prime-wall-P2-mathlib-path-resume-v4.py','exec'),{'__name__':'__main__','SOURCE_TEXT':source,'SOURCE_SHA256':'POSTIMAGE_SHA','INPUT_CONTRACT_TEXT':contract,'SERVICE_OBSERVATION_JSON':globals()['SERVICE_OBSERVATION_JSON'],'SERVICE_OBSERVATION_SHA256':globals()['SERVICE_OBSERVATION_SHA256']})
""".replace('CHANGES_REPR',repr(changes)).replace('POSTIMAGE_SHA',sha(source))
ast.parse(bootstrap)
(D/'omitted-prime-wall-P2-mathlib-path-resume-v4-bootstrap.py').write_text(bootstrap)
wrapper="""python3 - <<'PY'
import base64,zlib,hashlib
source=zlib.decompress(base64.b64decode('BOOTSTRAP_ZLIB'))
observation=zlib.decompress(base64.b64decode('__SERVICE_OBSERVATION_ZLIB_BASE64__'))
assert hashlib.sha256(source).hexdigest()=='BOOTSTRAP_SHA' and hashlib.sha256(observation).hexdigest()=='__SERVICE_OBSERVATION_SHA256__'
exec(compile(source,'omitted-prime-wall-P2-mathlib-path-resume-v4-bootstrap.py','exec'),{'__name__':'__main__','SERVICE_OBSERVATION_JSON':observation.decode(),'SERVICE_OBSERVATION_SHA256':'__SERVICE_OBSERVATION_SHA256__'})
PY
""".replace('BOOTSTRAP_ZLIB',base64.b64encode(zlib.compress(bootstrap.encode(),9)).decode()).replace('BOOTSTRAP_SHA',sha(bootstrap.encode()))
(D/'omitted-prime-wall-P2-mathlib-path-resume-v4-command-template.sh').write_text(wrapper)
request={'schema':'p29_omitted_mathlib_view_resume_request_template_v1','status':'STATIC_TEMPLATE_NOT_SUBMITTED','cwd':'/workspace','memory_mb':12800,'cpu_threads':2,'timeout_seconds':3600,'command_template':'omitted-prime-wall-P2-mathlib-path-resume-v4-command-template.sh','postimage_sha256':sha(source),'bootstrap_sha256':sha(bootstrap.encode()),'fresh_service_observation_must_be_injected':True,'one_new_attempt_no_automatic_retry':True,'old_successful_stage_replays':0}
(D/'OMITTED_P2_MATHLIB_PATH_RESUME_V4_REQUEST_TEMPLATE.json').write_text(json.dumps(request,indent=2)+'\n')
binding={'schema':'p29_omitted_mathlib_view_resume_static_binding_v1','baseline_sha256':sha(baseline.encode()),'fixed_contract_sha256':'1bad5b31281bf3439633c19e878b9a0bda575cf04961fbd018543e02737c3adf','literal_replacements':len(changes),'wholefile_inverse_exact':True,'unchanged_non_main_function_AST':sorted(n for n in of if n!='main'),'original_top_level_assignments_AST_unchanged':sorted(oldassign),'new_top_level_assignments':['PRIOR_ATTEMPT_ORIGINALS'],'prior_attempt_evidence':{n:{k:v for k,v in r.items()if k!='base64'}for n,r in originals.items()},'does_not_execute_old_successful_stages':True,'does_not_redownload_prior_authorities_external_derived_archive_or_Unit_archive':True,'does_not_modify_target_source_or_original_tools':True,'runtime_or_Lean_execution_performed_locally':False,'files':{}}
for f in [name,'OMITTED_P2_MATHLIB_PATH_RESUME_V3_TO_V4.patch','omitted-prime-wall-P2-mathlib-path-resume-v4-bootstrap.py','omitted-prime-wall-P2-mathlib-path-resume-v4-command-template.sh','OMITTED_P2_MATHLIB_PATH_RESUME_V4_REQUEST_TEMPLATE.json']:
 b=(D/f).read_bytes();binding['files'][f]={'bytes':len(b),'sha256':sha(b),'git_blob':oid(b)}
(D/'OMITTED_P2_MATHLIB_PATH_RESUME_V4_STATIC_BINDING.json').write_text(json.dumps(binding,indent=2)+'\n')
print(json.dumps(binding,indent=2))
