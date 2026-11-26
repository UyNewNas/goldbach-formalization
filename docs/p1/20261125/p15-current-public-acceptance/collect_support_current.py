from pathlib import Path
from types import ModuleType
import subprocess,hashlib,json,sys,os
sys.dont_write_bytecode=True
os.environ['GIT_OPTIONAL_LOCKS']='0';os.environ['GIT_NO_LAZY_FETCH']='1'
repo=Path('/workspace/goldbach-formalization');commit='3d292e4cd193ab422ca990e80a25165d5aca33a1'
module='ImbalancedChen.P1OriginalSingletonSupportData'
root=Path('/workspace/p1-complete-proof/20261126-p15-current-corrections-v1')/commit
f=root/'published-entrypoints/run_selected.py';code=f.read_bytes()
assert hashlib.sha256(code).hexdigest()=='ad45eb501f9a89ce1e594497a7105e4f3fac3587963e9249f40021691a82d725'
assert code==subprocess.check_output(['git','show',commit+':docs/p1/20261126/p15-current-corrections/run_selected.py'],cwd=repo)
driver=ModuleType('fixed_B_readonly_owner_reader');driver.__file__=str(f);exec(compile(code,str(f),'exec'),driver.__dict__)
s=driver.helpers();spec=driver.preflight(s,commit,[module])
driver.require_completed_existing_owner(s,commit,spec,module,spec.initial_owners[module])
run=root/'runs/attempt-00000';original=json.loads((run/'RESULT.json').read_bytes())
assert original['source_commit']==commit and original['accepted_owners']==[module]
assert set(original['failures'])=={'ImbalancedChen.P5OriginalPrimeChartHBWitnesses'}
assert not any(k in original for k in ['context_error','final_context_error','git_error'])
for stem in ['CONTEXT','GIT']:assert (run/(stem+'_BEFORE.json')).read_bytes()==(run/(stem+'_AFTER.json')).read_bytes()
assert (run/'executed-driver.py').read_bytes()==code
assert driver.snapshot(s,spec)==spec.baseline
base=root/module;audits=list((base/'audits').iterdir());assert len(audits)==1
audit=audits[0];assert audit.name=='4d31cbea582d1a40af58'
paths={'normal':base/'normal'/module/'NORMAL_PASS.json','audit_plan':audit/'AUDIT_PLAN.json','audit_result':audit/'lane-0/VALIDATION_RESULTS.json','owned_exports':audit/'lane-0/OWNED_EXPORTS.json','owned_log':audit/'lane-0/all-owned-types-axioms.log','reused_normal_evidence':audit/'lane-0/REUSED_NORMAL_EVIDENCE.json'}
def fp(p):
 assert p.is_file() and p.resolve()==p
 b=p.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
validation=json.loads(paths['audit_result'].read_bytes())
row={'source_commit':commit,'source_sha256':spec.sources[module],'owned_count':validation['total_owned_exports'],'public_count':validation['total_public_exports'],'receipt_bindings':{k:fp(p) for k,p in paths.items()},'normal_kernel_full_owned_revalidated_without_execution':True,'receipt_rebound_to_current_commit':False}
result={'schema':'p15_support_B_original_public_acceptance_v1','status':'ONE_ORIGINAL_OWNER_ACCEPTANCE_REVALIDATED_GROUP_REMAINS_FAILED','source_commit':commit,'compiler_job':'job_216f3dbd13b24dab8524da9ada0cac1b','source_manifest':{'commit':commit,'path':'docs/p1/20261126/p15-current-corrections/SOURCE_MANIFEST.json','bytes':324881,'sha256':'198861fae512aa5213a1e779bac287b5bc5551991f4e7508e4d51fe819755d73'},'original_result':fp(run/'RESULT.json'),'original_group_worker_exit_code':original['worker_exit_code'],'owners':{module:row},'published_source_count':360,'selected_owner_live_closure_count':len(spec.active),'source_runtime_and_original_receipts_unchanged':True,'normal_or_kernel_commands_executed':0,'whole_P1_5_complete':False}
assert driver.snapshot(s,spec)==spec.baseline
print(json.dumps(result,sort_keys=True))
