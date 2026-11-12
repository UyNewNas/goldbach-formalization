"""Read-only source/Git/hash/AST/ZIP metadata; never executes a proof generator.

The accepted generator is copied and its range text edited, not imported/run.
Postimage hashes are reused from the independently reviewed frozen selection.
No numerical data is parsed, recomputed, staged or evaluated.
"""
from pathlib import Path
import ast,copy,difflib,hashlib,json,os,re,subprocess,zipfile
HERE=Path(__file__).resolve().parent
RES=HERE.parents[1];ROOT=RES.parents[1]
REPO=ROOT/'goldbach-proof-github-sync-20261110.git'
ENV={**os.environ,'GIT_ALLOW_PROTOCOL':'','GIT_NO_LAZY_FETCH':'1','GIT_TERMINAL_PROMPT':'0'}
OLD_DRIVER='3fdc2e362d97a03aabef60cfdf68da2f7597be35'
SOURCE='124d09f9fc74e7b78261e2471a573f1657b5633e'
def sha(b):return hashlib.sha256(b).hexdigest()
def raw(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def dump(n,j):(HERE/n).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def desc(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':raw(b)}
def git(*args):return subprocess.check_output(['git','-c','remote.origin.promisor=false','-c','protocol.allow=never','--git-dir='+str(REPO),*args],env=ENV,stderr=subprocess.PIPE)
def save_ref(name,data):
 (HERE/'reference'/name).write_bytes(data);return {'path':'reference/'+name,'bytes':len(data),'sha256':sha(data),'git_blob_sha1':raw(data)}

for revision in [OLD_DRIVER,SOURCE]:assert git('cat-file','-t',revision).strip()==b'commit'
old=git('show',OLD_DRIVER+':verification/parts/p0/prepare_stored_batch.py')
old_workflow=git('show',OLD_DRIVER+':.github/workflows/stored-block-batch.yml')
audit=git('show',OLD_DRIVER+':verification/parts/p0/Round6Audit.lean')
oldref=save_ref('prepare_stored_batch.accepted020_030.py',old)
workflowref=save_ref('stored-block-batch.accepted020_030.yml',old_workflow)
auditref=save_ref('Round6Audit.accepted020_030.lean',audit)
assert b"range(20,31)" in old and old.count(b'range(20,31)')==2
proposal=old.decode('utf-8').replace('range(20,31)','range(31,42)').replace('modules[block-19]','modules[block-30]').replace('blocks020-030 and parent only; not whole T01','blocks031-041 and required parent only; not whole T01')
needle='import hashlib, json, os, pathlib, re, sys\n';assert proposal.count(needle)==1
proposal=proposal.replace(needle,needle+"assert os.environ.get('GITHUB_ACTIONS') == 'true', 'Remote GitHub generation only; never run locally'\n")
ast.parse(proposal)
(HERE/'prepare_stored_batch031_041.proposed.py').write_text(proposal,encoding='utf-8',newline='\n')
(HERE/'RANGE_ONLY_GENERATOR.patch').write_text(''.join(difflib.unified_diff(old.decode('utf-8').splitlines(True),proposal.splitlines(True),fromfile='a/verification/parts/p0/prepare_stored_batch.py',tofile='b/verification/parts/p0/prepare_stored_batch.py')),encoding='utf-8',newline='\n')
# Prove the old proof-generation algorithm is not edited: only the two range
# literals, receipt index, label and explicit remote-only guard differ.
normalized=proposal.replace("assert os.environ.get('GITHUB_ACTIONS') == 'true', 'Remote GitHub generation only; never run locally'\n",'').replace('range(31,42)','range(20,31)').replace('modules[block-30]','modules[block-19]').replace('blocks031-041 and required parent only; not whole T01','blocks020-030 and parent only; not whole T01')
assert normalized.encode()==old

selection_path=RES/'t01/fine-winner-postimage-selection-stage-errata/PROPOSED_FINE_WINNER_SOURCE_SELECTION.stage-corrected.json'
selection=load(selection_path);frozen={r['module']:r for r in selection['files']}
assert sha(selection_path.read_bytes())=='8bae4da647ca49642bebf5076495a836ed4230dd1d5a8d59e6fa2788d5f36b93'
new=[];checks=[]
for block in range(31,42):
 name=f'ImbalancedChen.Data.P5SubdivisionStoredBlock{block:03}';r=copy.deepcopy(frozen[name]);pre=r['pre_input'];origin=pre['origin']
 assert origin['commit']==SOURCE and r['imports']==['ImbalancedChen.P5SubdivisionStoredParentTypes']
 b=git('show',SOURCE+':'+origin['path']);assert (len(b),sha(b),raw(b))==(pre['bytes'],pre['sha256'],pre['git_blob_sha1'])
 assert len(r['transform'])==1
 transformation=r['transform'][0];old_proof=transformation['old'];new_proof=transformation['new']
 assert b.count(old_proof.encode())==1 and b'theorem rows_size : rows.size = 4096 := rfl' in b
 header=old_proof.split(' := by\n',1)[0]
 assert new_proof.count(header+' := by\n')==1
 assert len(re.findall(r'^private theorem source_index_chunk_\d+ :',new_proof,re.M))==64
 assert new_proof.count('  decide +kernel\n')==64
 pos=b.index(old_proof.encode());prefix=b[:pos];suffix=b[pos+len(old_proof.encode()):]
 # Read existing text only. Do not apply the replacement or invoke either old
 # or proposed proof/data producer locally.
 original_public=re.findall(r'(?m)^theorem ([A-Za-z0-9_]+)\s*:\s*([^\n]+?)\s*:=',b.decode('utf-8'))
 r['new_scope_role']='UNVALIDATED_NEW_BLOCK031_041_ONLY'
 r['source_generation_execution']='ROOT_GITHUB_ONLY_NOT_RUN_HERE'
 new.append(r)
 checks.append({'module':name,'block_id':block,'source_original':pre,'planned_postimage':{k:r[k] for k in ['bytes','sha256','git_blob_sha1']},'imports':r['imports'],'public_theorem_header_texts':original_public,'source_index_at_header':header,'rows_size_literal':4096,'unchanged_data_prefix':{'bytes':len(prefix),'sha256':sha(prefix)},'unchanged_suffix':{'bytes':len(suffix),'sha256':sha(suffix)},'private_kernel_chunks':64,'selected_postimage_materialized_here':False,'postimage_kernel_accepted':False})
parent_name='ImbalancedChen.P5SubdivisionStoredParentTypes';parent=copy.deepcopy(frozen[parent_name])
pb=git('show',SOURCE+':'+parent['origin']['path']);assert (len(pb),sha(pb),raw(pb))==(parent['bytes'],parent['sha256'],parent['git_blob_sha1'])
assert pb.startswith(b'import Mathlib.Data.Int.Basic\n') and not pb.startswith(b'module\n')
assert parent['imports']==['Mathlib.Data.Int.Basic']

authority_path=RES/'t02/direct-compiler-candidate-r1/RESTORE32_AUTHORITY.json';authority=load(authority_path)
parent_authority=next(r for r in authority['modules'] if r['module']==parent_name)
zip_path=RES/'ci-watch-v2/stored-blocks-020-030-43153562459-recovery.zip'
with zip_path.open('rb') as f:archive_sha=hashlib.file_digest(f,'sha256').hexdigest()
assert archive_sha=='5d05d304fe22d56efe1315281a53e4856c256418ef5e4397b70687f26d12966b'
with zipfile.ZipFile(zip_path) as z:
 names=z.namelist();assert len(names)==62
 for field,member_field in [('source','source_member'),('olean','olean_member'),('hash_sidecar','hash_member')]:
  b=z.read(parent_authority[member_field]);assert len(b)==parent_authority[field]['bytes'] and sha(b)==parent_authority[field]['sha256']
 assert z.read(parent_authority['source_member'])==pb
 batch=json.loads(z.read('BATCH_ACCEPTANCE.json'));snapshot=json.loads(z.read('BATCH_OBJECTS_BEFORE.json'));state=json.loads(z.read('runtime/state.json'))
 commands=[json.loads(line) for line in z.read('runtime/compiler-commands.jsonl').decode().splitlines()]
 parent_commands=[c for c in commands if c.get('tool')=='lean' and any(a.endswith('/P5SubdivisionStoredParentTypes.lean') for a in c.get('input_args',[]))]
 assert len(parent_commands)==1
 command=parent_commands[0]
 assert command['command'][1:4]==['-t0','-j2','-M12288']
 assert command['input_args'][:2]==['-DmaxRecDepth=100000','-DmaxHeartbeats=4000000']
 assert batch['status']=='PASS_SELECTED_BLOCKS_ONLY' and batch['source_commit']==OLD_DRIVER and len(batch['modules'])==12
 members=[{'path':i.filename,'bytes':i.file_size,'compressed_bytes':i.compress_size} for i in z.infolist()]
 mdirect={k:v for k,v in snapshot.items() if k.endswith(('/Mathlib/Data/Int/Basic.olean','/Mathlib/Data/Int/Basic.olean.private','/Mathlib/Data/Int/Basic.olean.server'))}
 assert len(mdirect)==3
 parent_parts=[i.filename for i in z.infolist() if 'compiled-parent/' in i.filename]
 absent=[suffix for suffix in ['.ilean','.c','.ir','.ir.sig','.setup.json','.trace','.o','.so','.a'] if not any(p.endswith(suffix) for p in parent_parts)]
 profile={Path(k).name:v for k,v in state['input_sha256'].items()}
 assert profile['lakefile.toml']=='26a6b01a52446ad6aae63d5201330b902ec94a1171fb1f0baf9fc61016098491'
 rawmembers={n:{'bytes':len(z.read(n)),'sha256':sha(z.read(n))} for n in ['BATCH_ACCEPTANCE.json','BATCH_OBJECTS_BEFORE.json','runtime/state.json','runtime/compiler-commands.jsonl','batch-checker.log','batch-types.log']}

dump('SOURCE_SELECTION031_041.json',{'schema':'STORED031_041_EXACT_SOURCE_PROPOSAL_V1','status':'SOURCE_ONLY_NOT_GENERATED_OR_VALIDATED','source_commit':SOURCE,'frozen_postimage_selection':desc(selection_path),'parent':parent,'new_modules':[r['module'] for r in new],'files':new,'mathematical_source_order':[parent_name]+[r['module'] for r in new],'direct_external_imports':['Mathlib.Data.Int.Basic'],'new_proof_compile_scope':[r['module'] for r in new],'forbidden_old_source_compile_modules':[parent_name]+[f'ImbalancedChen.Data.P5SubdivisionStoredBlock{k:03}' for k in range(31)],'reuse_only':{'parent':parent_authority,'old000_030_not_imported_by_new_graph':True},'generator':{'accepted_original':oldref,'proposed':{**desc(HERE/'prepare_stored_batch031_041.proposed.py'),'path':'prepare_stored_batch031_041.proposed.py'},'runtime_execution_only':'ROOT_GITHUB_AFTER_SEPARATE_DIRECT_RESTORE_APPROVAL'},'postimage_source_and_public_type_checks':checks,'new_blocks':11,'rows_per_block':4096,'new_rows_claimed_by_source_headers':45056,'old31_rows_already_accepted':126976,'accepted_new_blocks':0,'parent_source_compile_forbidden':True,'proof_or_numeric_program_executed':False,'driver_ready':False})
dump('PARENT_REUSE_INPUTS.json',{'schema':'STORED_PARENT_EXACT_REUSE_INPUTS_V1','status':'ACTUAL_ACCEPTED_OBJECT_NOT_COHERENT_LAKE_CACHE','module':parent_name,'source':parent,'accepted_parent':parent_authority,'RESTORE32_authority':desc(authority_path),'archive':{'path':str(zip_path),'bytes':zip_path.stat().st_size,'sha256':archive_sha,'artifact_id':13924520315,'producer_driver':OLD_DRIVER,'producer_run':43153562459,'producer_job':130968171010,'members':62},'actual_parent_compile_command':command,'original_project_configuration_sha256':profile,'guard_sha256':state['guard_sha256'],'original_pinned_runtime_sha256':state['runtime_sha256'],'original_parent_direct_import_public_private_server_snapshot_sha256':mdirect,'snapshot_is_not_a_compiler_import_trace':True,'snapshot_not_payload_or_cache':True,'actual_parent_archive_parts':parent_parts,'absent_parent_facets_or_setup':absent,'old_actual_acceptance':batch,'bound_raw_member_hashes':rawmembers,'legacy_header':{'is_module':False,'explicit_imports':['Mathlib.Data.Int.Basic'],'source_text':pb.decode('utf-8')},'required_future_matching':['Official metadata-only parent/leaf setup with original headers and exact pinned configuration','Actual current Mathlib transitive importArtifacts including relevant public/private/server/IR and ordered dynlibs/plugins','Actual toolchain/runtime/flags/library ABI equality','Zero Lean source compilation commands for parent or000-030','Real reject/failure evidence when missing facets/metadata cannot be recovered without recompilation'],'new_accepted_proof_claim':False,'root_driver_ready':False})
dump('ACCEPTED_ARTIFACT_MEMBER_INVENTORY.json',{'archive':str(zip_path),'sha256':archive_sha,'members':members,'extracted_payloads_or_restored_objects':False})

# Pin only the existing unexecuted interface source and line spans; do not
# copy or reimplement T02's restore/compiler tool. Its new Stored-mode owner
# will provide a separately frozen implementation.
r1=RES/'t02/direct-compiler-candidate-r1';interfaces=[]
wanted={'direct_compiler.py':['parse_requests','require_legacy','declared_import_modules','guarded_source_commands','completion','safe_members','accepted_payload','restore','oracle','metadata_parity','make_setup','compile_projects'],'direct_common.py':['setup_artifacts','import_map']}
for file,names in wanted.items():
 p=r1/file;src=p.read_text(encoding='utf-8');parsed=ast.parse(src)
 for fn in parsed.body:
  if isinstance(fn,(ast.FunctionDef,ast.ClassDef)) and fn.name in names:interfaces.append({'file':file,'function':fn.name,'start_line':fn.lineno,'end_line':fn.end_lineno,'source_file':desc(p)})
dump('EXISTING_DIRECT_INTERFACES_AND_HOLDS.json',{'schema':'STORED031_041_PARENT_RESTORE_SEAM_V1','status':'BLOCKED_PENDING_T02_STORED_MODE_AND_T10_REVIEW','existing_interfaces':interfaces,'r1_pause':desc(r1/'R1_WIP_PAUSE.json'),'r1_is_frozen_or_driver_ready':False,'general_Fine1859_oracle_not_applicable_to_tiny_graph':True,'reason':'Only project-ancestor-free actual selected module is protected parent; do not unprotect it or add unrelated mathematical lemmas to satisfy safe_modules. General flatten and lone public-parent importArts semantics were not established.','existing_accepted_workflow_unsafe_unchanged':'lake build on parent+11 can recompile accepted parent because no genuine parent ilean/C/setup/trace is retained.','proposed_owner_mode':'T02 separately authorized restricted Stored mode: genuine lake --no-build setup-file on each actual registered leaf, typed official setup preserved unchanged, protected-parent original-header metadata-only positive control, direct only new11 leaves.','must_fail_closed_if':'Original IR/trace/importArtifacts/plugin/ABI or official no-build metadata cannot be matched without protected compilation.','no_duplicate_compiler_or_setup_tool_written':True,'T10_review_and_GitHub_observations_required':True})
dump('DRIVER_DECISION_OPEN.json',{'schema':'STORED031_041_DRIVER_DECISION_V1','status':'NO_RUNNABLE_DRIVER_WHILE_PARENT_RESTORE_OPEN','branch':'ci/stored-blocks-031-041-20261112','preferred_base':OLD_DRIVER,'alternative_base':'356c3782e9428098a2fcbfb18c689bef264d84fa','why_preferred_base':'Exact source/config/rechunk/audit/runtime predecessor actually accepted for020-030.','new11_only':True,'parent_restore_only':True,'old000_030_proof_compilation':False,'source_selection_file':'SOURCE_SELECTION031_041.json','parent_authority_file':'PARENT_REUSE_INPUTS.json','old_generator_range_delta':'RANGE_ONLY_GENERATOR.patch','existing_workflow_reference':workflowref,'strict_type_axiom_audit_reference':auditref,'required_gates':['Parent authority ZIP/source/olean/hash and actual original binary/config binding','Official complete import/setup/IR/plugin/ABI without any protected source compilation','Exact source data prefix and public declarations/numeric literals unchanged','Real new11 guarded source compilation only; exact source/output/facet/import receipts','Original whole serialized declaration and owner inventory including private/generated names; full readable/expanded types and transitive allowed axioms','Fresh checker actual new11 and restored parent, with receipt distinguishing old accepted parent from current kernel replay','Original serial -t0 -j2 -M12288 guard and actual runtime audit','Always complete raw and coherent/partial facet retention; no synthetic trace/cache claim'],'new_workflow_written':False,'existing_unsafe_lake_recursive_compile_not_copied_as_active_driver':True,'T02_new_restricted_mode_not_frozen_or_executed_here':True,'driver_ready':False,'Git_write_or_CI_or_producer_execution':False})
checks={'source_original11_Git_SHA_bytes_matched':True,'source_public_headers_and4096_literals_matched':True,'planned_postimage_hashes_reused_from_frozen8bae':True,'postimage_producer_or_transform_not_executed_here':True,'generator_only_two_ranges_index_scope_and_remote_guard_differ':True,'accepted_generator_AST_parsed_not_executed':True,'accepted_archive_SHA_and62members_checked':True,'actual_parent_source_olean_hash_checked':True,'parent_legacy_header_and_original_profile_checked':True,'new_import_graph_parent_plus11_external_IntBasic_only':True,'protected31_leaves_not_required_as_inputs':True,'missing_real_parent_setup_C_IR_trace_prevents_Lake_cache_claim':True,'old2887decl_acceptance_not_new11_acceptance':True,'new_mathematical_accepted_modules':0,'driver_ready':False}
dump('STATIC_CHECKS.json',checks)
report='''Stored031–041 is prepared as an exact source-selection and minimal accepted-generator delta, not a runnable driver. The only new proof scope is eleven4096-row blocks. Their original bytes at124d09f9 are hash-bound, and their unexecuted bounded postimage pins are copied from the already independently reviewed8bae source selection. No data values, row arrays, numerical certificate or Lean expression were evaluated. The original data prefix/suffix and all public theorem header literals are checked textually; the64-chunk proof algorithm is not redesigned. The accepted020–030 generator changes only its two range literals, receipt array index, scope label, plus an explicit remote-only guard. Neither generator was executed locally.

The exact accepted predecessor is3fdc2e362d97a03aabef60cfdf68da2f7597be35/run43153562459/job130968171010. Its62-member recovery ZIP is verified against5d05d304fe22d56efe1315281a53e4856c256418ef5e4397b70687f26d12966b. The actual parent source470B/87f1a913 and olean119440B/5279a69c with its16B hash sidecar are present and verified from that ZIP. The original profile is the487B project lakefile26a6b01a with maxRecDepth100000/maxHeartbeats4000000, under the unchanged serial trust0/two-thread/12GiB guard. The original batch passed12 modules and2887 serialized declarations; that does not validate031–041. The prior31 blocks/126976 rows remain accepted historical scope, not repeated proof work or fresh cache acceptance.

All eleven new sources import only P5SubdivisionStoredParentTypes; the legacy parent explicitly imports only Mathlib.Data.Int.Basic. Old000–030 are not inputs to this graph. Parent and all31 old leaf source compilations are forbidden; only parent restoration, metadata read and separately labeled current kernel replay may occur. The old recursive lake build parent+11 cannot safely be reused because the archive has no parent ilean/C/IR/setup/real trace. The historical all-olean snapshot contains hashes, not the corresponding whole cache bytes or an actual complete parent setup. No trace, facet or cache hit is invented.

The existing T02 direct-r1 contains the needed restore/setup/import/command/completion primitives, but it is not frozen or run-ready. Its general oracle requires an unprotected project-ancestor-free selected module; this tiny graph has none except the protected parent. We do not unprotect it, add an unrelated mathematical module or duplicate that compiler tool. T02 owns a separately authorized restricted Stored mode using genuine no-build official setup on actual registered leaves, metadata-only original parent controls and direct compilation only for the new leaves. Actual helper/JSON/setup parity, full importArts/IR/plugin/ABI compatibility and zero protected commands require T10 review and genuine GitHub observations. If those checks reject, retain the rejection and partial bytes rather than compiling the parent as fallback.

The next branch is proposed as ci/stored-blocks-031-041-20261112, preferably from the exact accepted3fdc predecessor (356c is an explicit alternative for root review). No active workflow is written while its restore seam is unresolved. Original source/public-type/numeric-literal, every serialized public/private/generated declaration, both full type forms, transitive axiom, actual bundled fresh checker, unchanged runtime and complete archive gates are mandatory. Current driver_ready=false, new accepted blocks=0, no stage/install/setup/Lean/Lake/LSP/guard/checker/producer/numerical execution, Git mutation, remote action or CI dispatch occurred. Existing frozen sources and the dirty original repository are untouched.\n'''
(HERE/'REPORT.md').write_text(report,encoding='utf-8',newline='\n')
for p in HERE.rglob('*.py'):ast.parse(p.read_text(encoding='utf-8'))
for p in HERE.rglob('*.json'):
 if p.name not in ['REGISTRY.json','ALLOWLIST.json']:load(p)
records=[]
for p in sorted(HERE.rglob('*')):
 if p.is_file() and p.name not in ['REGISTRY.json','ALLOWLIST.json']:
  d=desc(p);d['path']=p.relative_to(HERE).as_posix();records.append(d)
dump('REGISTRY.json',{'schema':'STORED031_041_SOURCE_AND_DRIVER_HOLD_REGISTRY_V1','status':'FROZEN_STATIC_SELECTION_AND_EXPLICIT_RESTORE_HOLD','files':records,'new_blocks':11,'new_proof_accepted':0,'old31_and_parent_protected':True,'driver_ready':False,'source_or_proof_producer_run_locally':False,'active_workflow_written':False})
d=desc(HERE/'REGISTRY.json');d['path']='REGISTRY.json'
dump('ALLOWLIST.json',{'schema':'STORED031_041_AUTHOR_SOURCE_ALLOWLIST_V1','files':records+[d],'status':'SOURCE_SELECTION_AND_RANGE_DELTA_ONLY_NOT_DRIVER_APPROVAL','driver_ready':False})
for name in ['SOURCE_SELECTION031_041.json','PARENT_REUSE_INPUTS.json','RANGE_ONLY_GENERATOR.patch','REGISTRY.json','REPORT.md','ALLOWLIST.json']:
 print(json.dumps(desc(HERE/name)))
