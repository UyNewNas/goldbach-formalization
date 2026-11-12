"""Root-driver-only final conjunction of reused strict Y18 proof/runtime gates.

This does not create a driver selection. A separately reviewed actual immutable
driver/workflow binding is mandatory; the static candidate is never an acceptance.
"""
from pathlib import Path
import hashlib,json,os,sys
from bind_compile_receipts_y18 import bind_completed,bind_wrappers
HERE=Path(__file__).resolve().parent
def read(p):return json.loads(p.read_text(encoding='utf-8'))
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def main():
 assert os.environ.get('GITHUB_ACTIONS')=='true'
 manifest=HERE/'Y18_MANIFEST.json';m=read(manifest);logs=Path(os.environ['LOGS']);project=Path(os.environ['PROJECT']);checkpoint=Path(os.environ['CHECKPOINT'])
 assert sha(manifest)==os.environ['EXPECTED_MANIFEST']
 # This receipt must be supplied by the later independently reviewed root
 # driver. A bundle field saying 'rootbound' is never sufficient.
 driver=read(logs/'DRIVER_BINDING.json')
 assert driver['status']=='PASS_ACTUAL_COMMITTED_ROOT_DRIVER_WORKFLOWS'
 assert driver['driver_commit']==os.environ['GITHUB_SHA'] and driver['manifest_sha256']==sha(manifest)
 assert driver['bundle_registry_sha256']==sha(HERE/'REGISTRY.json')
 assert driver['root_selection_outside_bundle_hash'] is True and driver['workflow_bindings']
 if len(sys.argv)>1:
  assert sys.argv[1:] == ['wrappers']
  bind_wrappers(m,project,logs)
  return
 runtime=read(logs/'runtime/audit.json');state_path=logs/'runtime/state.json';state=read(state_path)
 assert runtime['status']=='PASS_RUNTIME_GUARD_ONLY' and runtime['probe'] and runtime['source_commands']>0
 assert runtime['state_sha256']==sha(state_path) and state['guard_sha256']==m['runtime_reuse']['sha256']
 commands=logs/'runtime/compiler-commands.jsonl'
 assert Path(state['log']).resolve()==commands.resolve() and runtime['command_log_sha256']==sha(commands)
 batch=read(logs/'BATCH_ACCEPTANCE.json')
 assert batch['status']=='PASS_EXACT_CANDIDATE_CLOSURE_ONLY' and batch['modules']==m['fresh_kernel_modules']
 assert batch['mathematical_modules']==m['mathematical_modules'] and batch['proof_artifact_hash']==sha(logs/'BATCH_OBJECTS_BEFORE.json')
 targets=read(logs/'TARGET17_RESULT.json')
 assert targets['status']=='PASS_EXACT_ORIGINAL17_OWNER_FULL_TYPES_AND_DUAL_AXIOMS'
 assert targets['manifest_sha256']==sha(manifest) and targets['log_sha256']==sha(logs/'batch-types.log')
 assert [r['name'] for r in targets['targets']]==[r['name'] for r in m['target_declarations']]
 consumer_receipts=[]
 for mode in ['wrapper','checker','audit']:
  pre_name='CONSUMER_'+mode+'_PRE.json';post_name='CONSUMER_'+mode+'_POST.json'
  pre=read(logs/pre_name);post=read(logs/post_name)
  assert post['status']=='PASS_SAME_ENV_CANONICAL_OBJECTS_AND_ACTUAL_CONSUMER_EXIT' and post['returncode']==0
  assert pre['selected_public_objects']==post['selected_public_objects'] and len(pre['selected_public_objects'])==(1685 if mode=='wrapper' else 1686)
  for record in [pre,post]:
   assert record['consumer']==mode and record['manifest_sha256']==sha(manifest) and record['driver_commit']==os.environ['GITHUB_SHA']
   assert record['run_id']==os.environ['GITHUB_RUN_ID'] and record['run_attempt']==os.environ['GITHUB_RUN_ATTEMPT']
   assert record['cache_alias_accepted'] is False
  consumer_receipts.extend([pre_name,post_name])
 # Actual wrapper build bindings must precede the stable retained snapshot.
 assert (logs/'WRAPPER_OBJECT_BINDINGS.json').is_file()
 binding=bind_completed(m,project,logs,checkpoint)
 assert binding['status']=='PASS_EXACT_SELECTED_SOURCE_CONFIG_FLAGS_IMPORT_OUTPUT_JOINS_ONLY'
 cp=read(checkpoint/'CHECKPOINT.json');assert not cp['issues'] and cp['runtime_audit_valid'] and cp['all_dependency_source_pins_valid']
 assert cp['manifest_sha256']==sha(manifest) and cp['source_commit']==m['source_commit']
 assert cp['run_id']==os.environ['GITHUB_RUN_ID'] and cp['run_attempt']==os.environ['GITHUB_RUN_ATTEMPT']
 assert not (checkpoint/'CHECKPOINT_FAILURE.json').exists()
 captured={r['resolved_path']:r for r in cp['files'].values()}
 expected_objects={r['module']:str((project/'.lake/build/lib/lean'/Path(*r['module'].split('.'))).with_suffix('.olean').resolve()) for r in m['files']}
 expected_objects.update({r['module']:str((project/'.lake/packages/goldbach/.lake/build/lib/lean'/Path(*r['module'].split('.'))).with_suffix('.olean').resolve()) for r in m['all_native_sources']})
 for mode in ['wrapper','checker','audit']:
  expected=dict(expected_objects)
  if mode!='wrapper':expected['CandidateAudit']=str((project/'.lake/build/lib/lean/CandidateAudit.olean').resolve())
  for phase in ['PRE','POST']:
   consumer=read(logs/('CONSUMER_'+mode+'_'+phase+'.json'))
   assert consumer['runtime_state_sha256']==sha(state_path)
   assert {r['module']:r['canonical_path'] for r in consumer['selected_public_objects']}==expected
   for row in consumer['selected_public_objects']:
    assert row['first_actual_path']==row['canonical_path'] and row['canonical_path'] in captured
    part=captured[row['canonical_path']]
    assert (part['sha256'],part['bytes'])==(row['sha256'],row['bytes'])
   for tool in consumer['actual_tool_runtime_bindings']:
    assert state['runtime_sha256'][tool['runtime_identity_key']]==tool['sha256']
    assert sha(Path(tool['path']))==tool['sha256']
 receipts=['DRIVER_BINDING.json','BATCH_ACCEPTANCE.json','BATCH_OBJECTS_BEFORE.json','batch-types.log','batch-checker.log','TARGET17_RESULT.json','WRAPPER_OBJECT_BINDINGS.json','COMPILE_INPUT_BINDINGS.json','SOURCE_PRE.json','SOURCE_POST.json','NATIVE_SOURCE_PRE.json','NATIVE_SOURCE_POST.json','dependencies.json','runtime/audit.json','runtime/state.json','runtime/compiler-commands.jsonl']+consumer_receipts
 out=logs/'FINAL_ACCEPTANCE.json';assert not out.exists()
 result={'status':'PASS_EXACT_Y18_337_PROJECT_460_RESEARCH_17_TARGETS_ONLY','source_commit':m['source_commit'],'native_revision':m['native_rev'],'manifest_sha256':sha(manifest),'registry_sha256':sha(HERE/'REGISTRY.json'),'driver_commit':os.environ['GITHUB_SHA'],'run_id':os.environ['GITHUB_RUN_ID'],'run_attempt':os.environ['GITHUB_RUN_ATTEMPT'],'strict_math_modules':m['mathematical_modules'],'actually_replayed_modules':m['fresh_kernel_modules'],'canonical_native_dependency_source_object_count':888,'canonical888_individually_declaration_audited':False,'target17':targets['targets'],'checkpoint_sha256':sha(checkpoint/'CHECKPOINT.json'),'receipts':{p:sha(logs/p) for p in receipts},'source_cache_or_ABI_restore_accepted':False,'whole_P2_or_P4_or_PP_or_K_accepted':False}
 out.write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
