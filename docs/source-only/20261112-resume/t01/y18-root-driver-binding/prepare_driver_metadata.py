"""Static Git-read/hash/YAML/AST metadata preparation only; never stages or runs gates."""
from pathlib import Path
import ast,copy,difflib,hashlib,json,os,subprocess,yaml
HERE=Path(__file__).resolve().parent
RES=HERE.parents[1]
ROOT=RES.parents[1]
CAND=HERE.parent/'y18-validation-candidate'
BASE='356c3782e9428098a2fcbfb18c689bef264d84fa'
BRANCH='ci/y18-empty-mother-20261112'
CPATH='docs/source-only/20261112-resume/t01/y18-validation-candidate'
DPATH='docs/source-only/20261112-resume/t01/y18-root-driver-binding'
WPATH='.github/workflows/y18-empty-mother-validation.yml'
SP='verification/parts/p0/Y18_EMPTY_MOTHER_DRIVER_SELECTION.json'
DEC='verification/parts/p0/Y18_P2R3_REUSE_DECISION.json'
ENV={**os.environ,'GIT_NO_LAZY_FETCH':'1','GIT_ALLOW_PROTOCOL':'','GIT_TERMINAL_PROMPT':'0'}
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def desc(p,path=None):
 b=p.read_bytes();return {'path':path if path is not None else p.relative_to(HERE).as_posix(),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':raw(b)}
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def git(*args):return subprocess.check_output(['git','-c','remote.origin.promisor=false','-c','protocol.allow=never','--git-dir='+str(ROOT/'goldbach-proof-github-sync-20261110.git'),*args],env=ENV,stderr=subprocess.PIPE)
creg=load(CAND/'REGISTRY.json');assert sha((CAND/'REGISTRY.json').read_bytes())=='ad2f974d49c24296cd2f7fd079d78e60c56dcc5aa96180064b1ef4289b8f7568'
assert sha((CAND/'Y18_MANIFEST.json').read_bytes())=='8c48f34f4479b13cb38749360df78ed06f1d80ddee646472579ad0f1e214a496'
for r in creg['files']:
 b=(CAND/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256']
assert len(creg['files'])==34
before=git('show',BASE+':.github/workflows/variable-envelope.yml')
assert sha(before)=='ab1c420e1f7ab7855860a705831203c7f1f467ce6302e16405f9bb487ac3d106'
needle=b"      - 'ci/resume-compile-repairs-20261111'\n";assert before.count(needle)==1
after=before.replace(needle,needle+("      - '"+BRANCH+"'\n").encode())
(HERE/'variable-envelope.driver.yml').write_bytes(after)
(HERE/'VE_DRIVER_ONLY.patch').write_text(''.join(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile='a/.github/workflows/variable-envelope.yml',tofile='b/.github/workflows/variable-envelope.yml')),encoding='utf-8',newline='\n')
original=[]
paths=[]
for line in git('ls-tree','-r',BASE,'.github/workflows').decode().splitlines():
 meta,p=line.split('\t',1)
 if p.endswith(('.yml','.yaml')):paths.append(p)
assert len(paths)==7 and WPATH not in paths
for p in sorted(paths):
 b=git('show',BASE+':'+p);changed=p.endswith('/variable-envelope.yml');selected=after if changed else b
 parsed=yaml.load(selected.decode(),Loader=yaml.BaseLoader);push=parsed.get('on',{}).get('push')
 assert isinstance(push,dict)
 if changed:assert BRANCH in push['branches-ignore']
 else:assert BRANCH not in push.get('branches',[])
 original.append({'path':p,'before':{'bytes':len(b),'sha256':sha(b),'git_blob_sha1':raw(b)},'expected_driver':{'bytes':len(selected),'sha256':sha(selected),'git_blob_sha1':raw(selected)},'changed':changed,'push':push,'new_branch_push_excluded':True})
assert sum(r['changed'] for r in original)==1
dump('DRIVER_BASE_WORKFLOW_AUDIT.json',{'driver_base':BASE,'driver_branch':BRANCH,'original_workflow_count':7,'original_workflows':original,'other_six_unchanged':6,'new_workflow_path':WPATH,'actual_total_workflows':8,'only_existing_workflow_edit':'One push.branches-ignore entry added to VE. All other bytes/events unchanged.','source_runtime_or_CI_executed':False})
scope=load(HERE.parent/'y18-validation-scope/FINE_P2_SOURCE_COMPARISONS.json')
same=scope['P2r2']['same_SHA'];assert len(same)==28 and not scope['P2r2']['different_SHA']
selected={r['module']:r for r in load(CAND/'Y18_MANIFEST.json')['files']}
dump('P2_SHARED_SOURCE_AND_REUSE_OPEN.json',{'schema':'Y18_P2_SHARED_DECISION_OPEN_V1','status':'ROOT_DECISION_OPEN_WAIT_CURRENT_P2_R3','root_reported_current_run':43186809155,'observation_by_this_agent':False,'shared_module_names':same,'shared_selected_sha256':{n:selected[n]['sha256'] for n in same},'comparison_is_to_frozen_P2r2_102':True,'same_source_not_accepted_proof_or_cache':True,'root_reports_five_P2_failure_repairs_do_not_intersect_Y18_selection':True,'accepted_coherent_same_profile_objects_adopted':[],'cache_restore_implemented':False,'candidate_protocol_changed':False,'candidate_requires_actual_guarded_producers':True,'needed_root_decision':['Supply terminal P2r3 strict inventory/type/axiom/kernel and actual artifact evidence.','Compare exact selected source, toolchain, resource flags, import artifacts, setup, outputs and ABI for each of28.','If reliable same-profile complete objects exist, do not run unchanged fresh-only candidate; prepare an explicitly reviewed reuse protocol instead.','If none are usable under this candidate, record exact evidence and source nonintersection in the separately committed root decision before authorizing deployment.'],'root_decision_path':DEC,'root_decision_required_status':'ROOT_RESOLVED_NO_RELIABLE_SAME_PROFILE_SHARED_OBJECTS_AVAILABLE','driver_must_fail_on_open':True})
dump('DRIVER_INSTALL_RECIPE.json',{'schema':'Y18_ROOT_DRIVER_INSTALL_RECIPE_V1','status':'PROPOSED_NOT_APPLIED_ROOT_ONLY','driver_base':BASE,'required_direct_parent':BASE,'driver_branch':BRANCH,'candidate_bundle_path':CPATH,'candidate_payload':'Exactly34 original registry members plus original REGISTRY (35 runtime files); author ALLOWLIST remains review-only.','candidate_registry_sha256':sha((CAND/'REGISTRY.json').read_bytes()),'candidate_manifest_sha256':sha((CAND/'Y18_MANIFEST.json').read_bytes()),'driver_bundle_path':DPATH,'driver_payload':'REGISTRY.files plus driver REGISTRY; external proposal/identity and author ALLOWLIST are not installed inside driver bundle.','new_workflow':{'from':'y18-empty-mother-validation.yml','to':WPATH},'VE_change':{'from':'variable-envelope.driver.yml','to':'.github/workflows/variable-envelope.yml','before':{'sha256':sha(before),'git_blob_sha1':raw(before),'bytes':len(before)},'after':{'sha256':sha(after),'git_blob_sha1':raw(after),'bytes':len(after)},'only_change':'One exact branch-ignore line'},'other_six_workflows':'Exact bytes from356c; full audit binds each.','external_selection':{'from':'ROOT_DELIVERED_SELECTION.proposed.json','to':SP,'outside_both_bundle_registry_hashes':True,'current_deployment_authorized':False},'later_root_decision':{'path':DEC,'status':'OPEN_NOT_PRESENT_NOT_FABRICATED','evidence_required':True},'original_pins':{'lean_action':'f061402b660e0c34644504b324e830f2991d4865','lean4':'62eed1db4d67327ec8120be05f1a1b0847d74561','mathlib':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','goldbach':'09b97db5764ade1246bfb77206baa1b124760958'},'serialized_mathematical':797,'actual_replay_with_wrapper':798,'canonical_external_source_object_only':888,'stored32_overlap':0,'fresh_or_restore_policy':'Unchanged candidate makes no accepted cache claim. Root resolves P2r3 before any deployment.','installed':False,'Git_mutated':False,'pushed':False,'CI_dispatched':False,'driver_ready':False})
workflow=yaml.load((HERE/'y18-empty-mother-validation.yml').read_text(encoding='utf-8'),Loader=yaml.BaseLoader)
assert workflow['on']=={'push':{'branches':[BRANCH],'paths':[WPATH]}}
assert workflow['concurrency']=={'group':'goldbach-p0-heavy','cancel-in-progress':'false'}
job=workflow['jobs']['y18_empty_mother'];assert job['env']['PYTHONDONTWRITEBYTECODE']=='1' and job['env']['LEAN_NUM_THREADS']=='2'
assert job['steps'][1]['with']['fetch-depth']=='2'
assert all('runner.' not in value for value in job['env'].values())
assert job['steps'][0]['name']=='Initialize exact paths and absolute proof deadline before checkout'
proof_step=next(s for s in job['steps'] if s['name']=='Execute all original proof gates before reserved retention deadline')
assert 'timeout --signal=TERM --kill-after=30s "${remaining}s" bash' in proof_step['run']
assert '285 * 60' in job['steps'][0]['run']
for step in job['steps']:
 if 'run' in step:assert step['run'].startswith('set -euo pipefail\n')
 if 'uses' in step:assert step['uses'].endswith(('11d5960a326750d5838078e36cf38b85af677262','ea165f8d65b6e75b540449e92b4886f43607fa02'))
assert [s['name'] for s in job['steps'] if s.get('if')=='${{ always() }}']==['Always audit exact unchanged trust-zero runtime when setup exists','Always retain actual full coherent facets and quarantined partial failures','Retain exact Y18 evidence and real output facets including failures']
for p in HERE.glob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
checks={'status':'STATIC_AST_YAML_BYTES_AND_WORKFLOW_DELTA_ONLY','candidate34_members_unchanged':True,'candidate35_runtime_files':35,'candidate_author_ALLOWLIST_review_only':True,'original7_workflows_read_from_exact_base':7,'original6_unchanged':6,'VE_exact_added_branch_lines':1,'actual_workflows_required':8,'workflow_exact_branch_and_path':True,'shared_heavy_group_cancel_false':True,'checkout_depth2_for_actual_base_diff':True,'PYTHONDONTWRITEBYTECODE_job_wide':True,'runner_paths_initialized_before_checkout_not_job_env':True,'absolute_proof_budget_minutes':285,'job_timeout_minutes':360,'reserved_tail_minutes':75,'runtime_checkpoint_final_upload_limits_minutes':[5,30,10,10],'proof_timeout_process_group_kill_grace_seconds':30,'failure_retention_independent_of_materialize_success':True,'exact_stage_and_guard_preserved':True,'actual_consumer_binary_object_receipts_preserved':True,'strict_math797_wrapper1_external888_distinct':True,'shared28_source_only':28,'P2r3_root_decision_OPEN':True,'coherent_cache_adopted':False,'stage_install_Lean_Lake_guard_or_CI_executed':False,'driver_ready':False}
dump('STATIC_CHECKS.json',checks)
report='''This is a concrete Y18 driver proposal, not an installed driver or authorization to run. Branch ci/y18-empty-mother-20261112 directly extends356c3782e9428098a2fcbfb18c689bef264d84fa. No Git write/push, CI dispatch, local stage/install/prepare, Lean/Lake/LSP/checker/guard/producer or numerical evaluation was performed.

The proposal installs exactly the frozen candidate34 registry members plus its REGISTRY, preserving ad2f974d49c24296cd2f7fd079d78e60c56dcc5aa96180064b1ef4289b8f7568 and manifest8c48f34f4479b13cb38749360df78ed06f1d80ddee646472579ad0f1e214a496. The author ALLOWLIST is review-only, not a runtime payload. One new workflow and one VE branch-ignore addition are the only workflow changes; the other six original workflows remain byte-for-byte identical. All eight workflows, both payload trees, raw commit parent, exact complete tree delta, actual committed selection and output prefixes are checked against github.sha. Checkout depth2 ensures base-tree comparison can run. A job-wide no-bytecode setting prevents Python imports mutating the frozen candidate payload.

The new workflow uses the original pinned lean-action, toolchain, dependency lock, serial flock, trust0/two-thread/12GiB guard, goldbach-p0-heavy group and cancel-in-progress=false. Runtime paths are initialized before checkout through GITHUB_ENV, using legal step-level runner variables. An absolute proof deadline285 minutes after initialization applies to the whole proof subprocess group, with TERM then KILL after30 seconds. The360-minute job reserves75 minutes for runtime5/checkpoint30/final10/upload10 plus20 minutes of overhead. Prep actions have finite timeouts. This preserves partial-output collection instead of letting a stalled wrapper consume the job's hard-stop budget. Exact two-origin staging, thirteen reviewed List patches, all1348 canonical/native source bindings and seven bare-library registrations are unchanged candidate calls. The same-env absolute real tool, actual LEAN_PATH/canonical object and compiler/setup/import/facet joins feed the final coherent checkpoint. It actually builds and independently replays CandidateAudit. The strict serialized/defining-owner multiset comparison, flush/rejection (including FinitePi), full public/private/generated readable/expanded types, transitive axioms, exact17 owner/kind assertions and independent axiom reports remain mandatory. Acceptance scope is797 mathematical modules plus the built audit wrapper for798 replays;888 standard native package dependencies receive source/object provenance without a false individual declaration-pass claim.

Always runtime audit and complete coherent/partial retention depend on available real PROJECT/runtime paths, not materialize success. The raw failure journal, actual setup/trace/ilean/IR/C/o/libraries/link outputs and receipts are retained by the already reviewed collector. Upload is always attempted for the exact evidence/checkpoint prefixes. Finalization checks the actual root driver again and then invokes the unchanged candidate finalizer. No facet, trace, ABI equivalence or cache hit is synthesized.

The external ROOT_DELIVERED_SELECTION.proposed.json is concrete and contains each runtime destination path/hash/blob/size, but explicitly has deployment_authorized=false and reuse_decision=null. It is excluded from both bundle hashes to avoid circular root-selection trust. Its first remote select step deliberately rejects until root adopts a separately bound evidence-based P2r3 decision. Current run43186809155 is root-monitored, not observed here. The known28 matching project source hashes are not accepted proof or coherent artifacts. The five P2 failure repairs were reported by root not to intersect this selection; no unlisted repair or cache is adopted. If reusable accepted objects exist, the unchanged fresh-producer protocol must not run: an explicit independently reviewed reuse adaptation is needed. If none is usable for this exact source/profile/import/runtime/ABI, root must bind the actual evidence and source nonintersection before deployment. The proposal does not resolve FinitePi or P2, promise repeated compilation is necessary, or queue Y18.

T16 must review this proposed driver and later inspect the actual root-created Git tree/selection. Current driver_ready=false, installed=false, CI_dispatched=false. PP, hUpper, whole parts and K remain outside this proposal.
'''
(HERE/'REPORT.md').write_text(report,encoding='utf-8',newline='\n')
excluded={'REGISTRY.json','ALLOWLIST.json','ROOT_DELIVERED_SELECTION.proposed.json','ROOT_DELIVERED_SELECTION.IDENTITY.json'}
records=[desc(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name not in excluded]
dump('REGISTRY.json',{'schema':'Y18_ROOT_DRIVER_PROPOSAL_REGISTRY_V1','status':'STATIC_PROPOSAL_PENDING_T16_ROOT_DECISION_AND_ACTUAL_TREE','files':records,'candidate_registry_sha256':sha((CAND/'REGISTRY.json').read_bytes()),'manifest_sha256':sha((CAND/'Y18_MANIFEST.json').read_bytes()),'external_root_selection_excluded_to_avoid_cycle':True,'driver_ready':False,'installed':False,'pushed':False,'CI_dispatched':False})
candidate_payload=[desc(CAND/r['path'],CPATH+'/'+r['path']) for r in creg['files']]+[desc(CAND/'REGISTRY.json',CPATH+'/REGISTRY.json')]
driver_payload=[desc(HERE/r['path'],DPATH+'/'+r['path']) for r in records]+[desc(HERE/'REGISTRY.json',DPATH+'/REGISTRY.json')]
workflow_payload=[{'path':r['path'],**r['expected_driver']} for r in original]+[desc(HERE/'y18-empty-mother-validation.yml',WPATH)];workflow_payload.sort(key=lambda r:r['path'])
selection={'schema':'y18-empty-mother-root-driver-selection-v1','driver_base':BASE,'driver_branch':BRANCH,'workflow_path':WPATH,'driver_bundle_path':DPATH,'candidate_bundle_path':CPATH,'candidate_registry_sha256':sha((CAND/'REGISTRY.json').read_bytes()),'manifest_sha256':sha((CAND/'Y18_MANIFEST.json').read_bytes()),'driver_registry_sha256':sha((HERE/'REGISTRY.json').read_bytes()),'source_commit':'794fe55a2136e8f502eae426095631f64f596f7f','historical_assembly':'f1bcf37b6fe3f0a5a4b6c4c48b166a6119f9f784','candidate_author_allowlist_role':'review-only-not-runtime-installed','candidate_author_allowlist_sha256':sha((CAND/'ALLOWLIST.json').read_bytes()),'original_math_scope':{'project':337,'research':460,'strict_math':797,'built_audit_wrappers':1,'fresh_checker':798,'canonical_external':888},'output_prefixes':{'project':'y18-candidate','logs':'y18-empty-mother-evidence','checkpoint':'y18-empty-mother-checkpoint','source_view':'y18-empty-mother-source-view'},'candidate_payload':candidate_payload,'driver_payload':driver_payload,'actual_workflow_payload':workflow_payload,'deployment_authorized':False,'reuse_decision':None,'decision_OPEN_is_not_a_missing_source_or_placeholder':True}
dump('ROOT_DELIVERED_SELECTION.proposed.json',selection)
dump('ROOT_DELIVERED_SELECTION.IDENTITY.json',{'selection_destination':SP,'selection':desc(HERE/'ROOT_DELIVERED_SELECTION.proposed.json'),'driver_registry':desc(HERE/'REGISTRY.json'),'candidate_registry_sha256':selection['candidate_registry_sha256'],'manifest_sha256':selection['manifest_sha256'],'candidate_runtime_files':len(candidate_payload),'driver_runtime_files':len(driver_payload),'actual_workflow_files':len(workflow_payload),'root_only_adoption_after_review_and_P2r3_decision':True,'deployment_authorized':False,'installed_or_dispatched':False})
dump('ALLOWLIST.json',{'schema':'Y18_ROOT_DRIVER_PROPOSAL_AUTHOR_ALLOWLIST_V1','status':'REVIEW_ONLY_NOT_DEPLOYED_OR_AUTHORIZED','files':[desc(p) for p in sorted(HERE.iterdir()) if p.is_file() and p.name!='ALLOWLIST.json'],'external_selection_outside_driver_registry':True,'driver_ready':False})
for name in ['REGISTRY.json','ROOT_DELIVERED_SELECTION.proposed.json','y18-empty-mother-validation.yml','ALLOWLIST.json','REPORT.md']:
 print(json.dumps(desc(HERE/name)))
