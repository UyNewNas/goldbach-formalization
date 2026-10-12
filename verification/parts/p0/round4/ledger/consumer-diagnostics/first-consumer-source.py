#!/usr/bin/env python3
"""Read fixed Git objects / original receipts only. No Lean, CI, network, or Git mutations."""
from pathlib import Path,PurePosixPath
from collections import Counter
import subprocess,json,hashlib,re,datetime,csv,io,zipfile,copy
HERE=Path(__file__).resolve().parent
ROUND4=HERE.parent
REPO=ROUND4.parent/'goldbach-formalization'
P0='28fd630ef7cc38eba86beb6c0ba123336b5d05f2'
BASELINE='1a80c1bcce67886f699d097fc37fd245cd3620bf'
MANUSCRIPT='ba6ec11d800eccc54406490631895e174de85766'
OLD_LEDGER='verification/parts/p0/round3/ledger/module-ledger.json'
OLD_TYPES='verification/parts/p0/round3/ledger/compiler-declarations.json'
BUCHSTAB='ImbalancedChen.CurrentChenBuchstabRefinement'
ALLOWED={'propext','Classical.choice','Quot.sound'}
checks=[]
def check(value,label,detail=None):
    checks.append({'check':label,'pass':bool(value),'detail':detail})
    if not value:raise AssertionError(label+': '+repr(detail))
def sha(b):return hashlib.sha256(b).hexdigest()
def git(path,commit=P0):return subprocess.check_output(['git','show',commit+':'+path],cwd=REPO)
def put_bytes(path,b):
    p=HERE/path;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'path':path,'bytes':len(b),'sha256':sha(b)}
def write(path,v):return put_bytes(path,(json.dumps(v,ensure_ascii=False,indent=2)+'\n').encode())
def copy_input(src,dst):return put_bytes(dst,Path(src).read_bytes())
def copied_json(src,dst):r=copy_input(src,dst);return json.loads((HERE/dst).read_text()),r
def omissions(s):return [x for x in ['⋯','...','…','<proof>','<unavailable>'] if x in s]
def type_record(raw,fmt,source,provenance):
    check(not omissions(raw['type']),'complete_primary_type:'+raw['name'],omissions(raw['type']))
    check(set(raw['axioms'])<=ALLOWED and raw['kind']!='axiom','allowed_axioms:'+raw['name'])
    r=copy.deepcopy(raw)
    if 'display_kind' in r:r['historical_display_kind']=r.pop('display_kind')
    r['display_kind']=fmt;r['actual_type_format']=fmt;r['contains_omission_marker']=False
    r['production_source_sha256']=source['sha256'];r['source_fixed_commit']=source['fixed_commit'];r['provenance']=provenance
    return r
try:
    old_bytes=git(OLD_LEDGER);types_bytes=git(OLD_TYPES)
    check(old_bytes==(REPO/OLD_LEDGER).read_bytes(),'round3_ledger_matches_fixed_P0')
    check(types_bytes==(REPO/OLD_TYPES).read_bytes(),'round3_types_match_fixed_P0')
    oldref=put_bytes('original-evidence/round3-module-ledger.json',old_bytes)
    oldtyperef=put_bytes('original-evidence/round3-compiler-declarations.json',types_bytes)
    old=json.loads(old_bytes);oldtypes=json.loads(types_bytes)
    oldmods={r['module']:r for r in old['modules']}
    oldaccepted={n:m for n,m in oldmods.items() if m['component_acceptance']['accepted']}
    check(len(oldmods)==31 and len(oldaccepted)==19,'old_module_census')
    check(len(oldtypes)==591 and len({r['name'] for r in oldtypes})==591,'old_type_census')
    p1,p1ref=copied_json(ROUND4/'p1-intake/REUSE_RECEIPT.json','input-receipts/P1_REUSE_RECEIPT.json')
    p1install,_=copied_json(ROUND4/'p1-intake/INSTALL_MANIFEST.json','input-receipts/P1_INSTALL_MANIFEST.json')
    p1cand,p1candref=copied_json(ROUND4/'p1-intake/CANDIDATE_RECEIPT.json','input-receipts/P1_CANDIDATE_RECEIPT.json')
    p1types,p1typesref=copied_json(ROUND4/'p1-intake/COMPILER_TYPES_PRODUCTION_14.json','input-receipts/P1_TYPES_14.json')
    p2,p2ref=copied_json(ROUND4/'p2-intake/P2_INTAKE_RECEIPT.json','input-receipts/P2_REUSE_RECEIPT.json')
    p2types,p2typesref=copied_json(ROUND4/'p2-intake/NEW_400_COMPLETE_TYPES.json','input-receipts/P2_TYPES_400.json')
    p5,p5ref=copied_json(ROUND4/'p5-intake/P5_FIXED_INTAKE.json','input-receipts/P5_UPSTREAM_RECEIPT.json')
    p5types,p5typesref=copied_json(ROUND4/'p5-intake/COMPILER_TYPES_8.json','input-receipts/P5_UPSTREAM_TYPES_8.json')
    check(p1['status']=='PASS_ARCHIVED_EVIDENCE_REUSE' and p1['production_declarations']==14,'P1_received_status')
    check(p2['status']=='PASS_FIXED_P2_SOURCE_ORIGINAL_OBJECT_LINEAGE_AND_REAL_CI' and p2['new_owned_declarations']==400,'P2_received_status')
    check(p5['status']=='PASS_REUSED_FIXED_PRODUCER_GATES' and p5['declaration_count']==8,'P5_received_status')
    # Recheck the restored actual prior CI archive, metadata, fixed inputs, and output hashes.
    run,runref=copied_json(ROUND4/'previous-core.json','previous-ci/run.json')
    artifact_metadata,artmetaref=copied_json(ROUND4/'previous-artifacts.json','previous-ci/artifacts.json')
    artifact=artifact_metadata['artifacts'][0];zipbytes=(ROUND4/'previous-28fd630/core-artifact.zip').read_bytes()
    check(run['head_sha']==P0 and run['id']==38250288277 and run['status']=='completed' and run['conclusion']=='success','prior_CI_run_identity')
    check(artifact['workflow_run']['head_sha']==P0 and artifact['workflow_run']['id']==run['id'],'prior_CI_artifact_run_identity')
    check(sha(zipbytes)==artifact['digest'].split(':',1)[1] and len(zipbytes)==artifact['size_in_bytes'],'prior_CI_zip_digest_size')
    zipref=put_bytes('previous-ci/core-artifact.zip',zipbytes)
    extracted=ROUND4/'previous-28fd630/artifact'
    ziprecords=[]
    with zipfile.ZipFile(io.BytesIO(zipbytes)) as z:
        infos=z.infolist();check(len(infos)==25 and len({i.filename for i in infos})==25,'prior_CI_zip_census')
        for i in infos:
            pp=PurePosixPath(i.filename);check(not pp.is_absolute() and '..' not in pp.parts and not i.is_dir(),'prior_CI_zip_safe:'+i.filename)
            b=z.read(i);check(b==(extracted/i.filename).read_bytes(),'prior_CI_extraction_exact:'+i.filename)
            ziprecords.append(put_bytes('previous-ci/artifact/'+i.filename,b))
    logs=extracted/'_temp/lean-verification-logs'
    check('project_commit='+P0 in (logs/'provenance.log').read_text(),'prior_CI_provenance_SHA')
    check((logs/'outcomes.log').read_text().splitlines()==['build=success','leanchecker=success','axiom-audit=success','round3-types=success'],'prior_CI_actual_outcomes')
    stage_rows=[]
    for stage,seconds in [('build',35),('leanchecker',365),('axiom-audit',25),('round3-types',473)]:
        ts=list(csv.DictReader(io.StringIO((logs/(stage+'.timing.tsv')).read_text()),delimiter='\t'))
        check(len(ts)==1 and ts[0]['stage']==stage and int(ts[0]['exit_code'])==0 and int(ts[0]['elapsed_seconds'])==seconds,'prior_CI_timing:'+stage)
        text=(logs/(stage+'.log')).read_text();check('stage='+stage+' finished=' in text and 'elapsed_seconds='+str(seconds)+' exit_code=0' in text,'prior_CI_actual_exit_footer:'+stage)
        stage_rows.append({**ts[0],'elapsed_seconds':seconds,'exit_code':0,'log_sha256':sha(text.encode())})
    check('Build completed successfully (9798 jobs).' in (logs/'build.log').read_text(),'prior_full_build_count')
    replaylog=(logs/'leanchecker.log').read_text()
    replayed=set(re.findall(r'^replaying (\S+)$',replaylog,re.M))
    check(set(oldaccepted)|{'ImbalancedChen'}<=replayed,'prior_root_replay_covers_19_accepted',sorted(set(oldaccepted)-replayed))
    check('Bundled leanchecker:' in replaylog and '62eed1db4d67327ec8120be05f1a1b0847d74561' in replaylog,'prior_stock_checker_toolchain')
    axlog=(logs/'axiom-audit.log').read_text()
    check("axiom-audit: audited 5458 declaration(s) under 'ImbalancedChen'; all within the allowlist [propext, Classical.choice, Quot.sound]." in axlog,'prior_root_axiom_count_allowlist')
    check('axiom-audit @ v0.1.2 (46024e005996495c65ef609368e11ab39c4222e3)' in axlog,'prior_axiom_audit_pin')
    receipts=list(extracted.rglob('receipt.json'));check(len(receipts)==1,'unique_previous_type_receipt')
    typed=receipts[0].parent;treceipt=json.loads(receipts[0].read_text());new198=json.loads((typed/'declarations.json').read_text())
    check(treceipt['status']=='PASS' and treceipt['source_commit']==treceipt['source_commit_after']==P0 and treceipt['lean_exit_code']==0 and treceipt['pin_check_exit_code']==0,'previous_type_receipt_status_SHA')
    check(treceipt['inputs_before']==treceipt['inputs_after'],'previous_type_source_object_stability')
    for path,digest in treceipt['inputs_before']['source_sha256'].items():check(sha(git(path))==digest,'prior_type_fixed_git_source:'+path)
    check(len(treceipt['inputs_before']['source_sha256'])==270 and len(treceipt['inputs_before']['production_olean_parts'])==263,'previous_type_input_census')
    for f,digest in treceipt['compiler_output_files_sha256'].items():check(sha((typed/f).read_bytes())==digest,'previous_type_output_hash:'+f)
    check(sha((typed/'stdout.log').read_bytes())==treceipt['stdout_sha256'] and sha((typed/'stderr.log').read_bytes())==treceipt['stderr_sha256'],'previous_type_raw_output_hashes')
    check(treceipt['full_types_untruncated'] and treceipt['declaration_count']==198 and treceipt['bridge_count']==1 and len(new198)==198,'previous_full_types_census')
    check(dict(Counter(r['module'] for r in new198))==treceipt['expected_defining_module_counts'],'previous_new_type_module_census')
    check(not treceipt['hLower_hUpper_discharged'] and treceipt['final_bridge_is_conditional'],'previous_final_bridge_still_conditional')
    bridge=json.loads((typed/'final-bridge.json').read_text());bridge_ref=copy_input(typed/'final-bridge.json','INHERITED_FINAL_BRIDGE.json')
    copy_input(typed/'final-bridge-type.txt','INHERITED_FINAL_BRIDGE_TYPE.txt')
    prior_type_audit=git('verification/parts/p0/Round3Audit.lean').decode()
    check('`pp.all true' in prior_type_audit or 'setBool `pp.all true' in prior_type_audit,'prior_198_actual_pp_all_audit_option')
    # Replace the previous round's partial/default new-198 records using actual completed CI output.
    prior_by_name={r['name']:r for r in oldtypes};new198names={r['name'] for r in new198}
    check(new198names<=set(prior_by_name) and len(new198names)==198,'previous_new_198_names_bind_existing_inventory')
    old393=[r for r in oldtypes if r['name'] not in new198names]
    check(len(old393)==393,'old_393_partition')
    restored=[]
    for r in old393:
        m=oldmods[r['module']];check(m['component_acceptance']['accepted'],'old_type_is_accepted:'+r['name'])
        check(sha(git(m['repository_path']))==m['source']['sha256']==r['production_source_sha256'],'old_type_source_unchanged_at_P0:'+r['name'])
        fmt='DEFAULT_META_PPEXPR_COMPLETE' if r['module']==BUCHSTAB else 'PP_ALL_COMPLETE'
        restored.append(type_record(r,fmt,m['source'],{'kind':'REUSED_PRIOR_COMPILER_RECORD_EXACT_SOURCE','record_source':oldtyperef,'record_name':r['name'],'root_validated_at':P0,'actual_record_reexecuted_this_intake':False,'format_correction':'Historical PP_ALL label is corrected to original default Meta.ppExpr for the five Buchstab records only.' if r['module']==BUCHSTAB else None}))
    check(sum(r['actual_type_format']=='DEFAULT_META_PPEXPR_COMPLETE' for r in restored)==5,'old_393_corrected_format_388_plus_5')
    for r in new198:
        m=oldmods[r['module']];check(sha(git(m['repository_path']))==m['source']['sha256'],'new_198_source_bind_to_old_module:'+r['module'])
        restored.append(type_record(r,'PP_ALL_COMPLETE',m['source'],{'kind':'ACTUAL_PRIOR_P0_CI_TYPE_EXPORT','run_id':run['id'],'source_commit':P0,'artifact_id':artifact['id'],'artifact_sha256':sha(zipbytes),'declarations_sha256':treceipt['compiler_output_files_sha256']['declarations.json'],'record_name':r['name'],'replaces_round3_pending_or_default_record':True}))
    restored.sort(key=lambda r:(r['module'],r['name']))
    check(len(restored)==591 and len({r['name'] for r in restored})==591,'restored_591_complete_unique')
    restored_counts=Counter(r['actual_type_format'] for r in restored)
    check(restored_counts=={'PP_ALL_COMPLETE':586,'DEFAULT_META_PPEXPR_COMPLETE':5},'restored_591_format_counts')
    check(Counter(r['module'] for r in restored)=={n:m['declarations']['owned_audited'] for n,m in oldaccepted.items()},'restored_591_module_census')
    write('INHERITED_TYPES_591.json',restored)
    formatrows=[{'name':r['name'],'module':r['module'],'actual_type_format':r['actual_type_format'],'primary_type_complete':True,'contains_omission_marker':False,'source_fixed_commit':r['source_fixed_commit'],'production_source_sha256':r['production_source_sha256'],'compiler_record_origin':r['provenance']['kind'],'prior_default_or_pending_record_replaced':r['name'] in new198names} for r in restored]
    write('INHERITED_TYPE_FORMATS_591.json',formatrows)
    oldCI={'status':'PASS_RESTORED_ORIGINAL_CI_EVIDENCE_IDENTITY','source_commit':P0,'run_id':run['id'],'run_url':run['html_url'],'artifact_id':artifact['id'],'artifact_bytes':len(zipbytes),'artifact_sha256':sha(zipbytes),'artifact_members':25,'archive':zipref,'metadata':[runref,artmetaref],'stages':stage_rows,'full_build_jobs':9798,'root_owned_declarations_audited':5458,'old_accepted_modules_replayed':sorted(oldaccepted),'axiom_audit_version':'v0.1.2','axiom_audit_commit':'46024e005996495c65ef609368e11ab39c4222e3','allowed_axioms':sorted(ALLOWED),'type_export_declarations':198,'type_export_separate_bridge':1,'type_export_source_inputs':270,'type_export_production_object_modules':263,'full_type_output_sha256':treceipt['compiler_output_files_sha256']['declarations.json'],'restored_type_census':{'old393_pp_all':388,'old393_default_complete':5,'actual_round3_198_pp_all':198,'total_complete':591,'total_pp_all':586,'total_default_complete':5},'object_claim':'Original captured object digests and unchanged before/after bindings. The archive does not embed all production objects.','new_lean_or_ci_execution':False,'final_bridge_conditional':True,'hLower_hUpper_discharged':False}
    write('PREVIOUS_CI_VALIDATION.json',oldCI)
    # Preserve first diagnostics and immutable original records; no chronology is rewritten.
    for part,name in [('p1','CANDIDATE_RECEIPT.json'),('p2','FIRST_DIAGNOSTICS.json'),('p5','FIRST_DIAGNOSTICS.json')]:
        copy_input(ROUND4/(part+'-intake')/name,'input-receipts/'+part.upper()+'_'+name)
    modules=[];latest={'P1':p1['source_commit'],'P2':p2['source_head'],'P5':p5['fixed_commit']}
    for m in old['modules']:
        acc=m['component_acceptance']['accepted'];src=copy.deepcopy(m['source']);owner=m['part_owner']
        # Read the fixed source from original owner commit, independently of a mutable working tree.
        content=git(m['repository_path'],src['fixed_commit']);check(sha(content)==src['sha256'],'old_fixed_module_source:'+m['module'])
        source_snapshot=put_bytes('snapshot-sources/'+m['repository_path'],content)
        src['snapshot']=source_snapshot
        if owner in latest:
            check(git(m['repository_path'],latest[owner])==content,'latest_owner_handoff_source_unchanged:'+m['module'])
            src['latest_fixed_handoff']=latest[owner];src['latest_fixed_handoff_byte_identity_checked']=True
        fmt=Counter(r['actual_type_format'] for r in restored if r['module']==m['module'])
        modules.append({'module':m['module'],'repository_path':m['repository_path'],'part_owner':owner,'source':src,'compiled_object_sha256':m['compiled_object_sha256'],'component_evidence_accepted':acc,'accepted_at_previous_integration':acc,'previous_integration_sha':P0 if acc else None,'new_component_this_round':False,'validation_status':'PREVIOUSLY_INTEGRATED_AND_ROOT_VERIFIED' if acc else m['component_acceptance']['status'],'validation_scope':'Prior fixed-source leaf receipts and actual P0 '+P0+' canonical root checks; no new execution.' if acc else 'Inherited fixed-source candidate; no new success implied by old root build.','validation':copy.deepcopy(m['validation']),'declarations':{'owned_audited':m['declarations']['owned_audited'],'complete_received_production_types':sum(fmt.values()),'actual_type_formats':dict(fmt),'source_headers_only':not acc and not m['declarations']['owned_audited']},'direct_imports':m['direct_imports'],'receiving_parts':m['receiving_parts'],'unclosed_real_inputs':m['unclosed_real_inputs'],'outstanding_component_validation_gates':m['outstanding_validation_gates'],'new_integration_sha':None,'new_integration_gates':'PENDING_ROOT_EXECUTION','inherited_record':{'ledger':oldref,'module_key':m['module']}})
    # Add P1 permit and two fixed-but-uncompiled historical candidates.
    prodt=next(t for t in p1['targets'] if t['module']=='ImbalancedChen.StoredHistoricalBoxPermit')
    p1src=next(r for r in p1install['files_to_copy_exactly'] if r['role']=='production')
    source={'fixed_commit':p1['source_commit'],'latest_fixed_handoff':p1['source_commit'],'sha256':p1src['sha256'],'git_blob_sha1':p1src['git_blob']}
    content=git(p1src['path'],p1['source_commit']);check(sha(content)==source['sha256'],'new_P1_source_fixed')
    source['snapshot']=put_bytes('snapshot-sources/'+p1src['path'],content)
    permit_unclosed=['Actual adopted per-cell J, I, old, nu, cap data and finite storedMeshCapCheck = true.','Identification of each supplied old j with the effective inherited preceding history level.','Actual carrier dictionary, global coverage, support and factorization; old/new own-cube gates remain separate.','Full adopted integral/ledger composition, same actual rho K proof, full Chen mean/c/hLower/hUpper.']
    modules.append({'module':prodt['module'],'repository_path':p1src['path'],'part_owner':'P1','source':source,'compiled_object_sha256':prodt['object_sha256'],'component_evidence_accepted':True,'accepted_at_previous_integration':False,'previous_integration_sha':None,'new_component_this_round':True,'validation_status':'SOURCE_AND_ORIGINAL_GATES_ACCEPTED_PENDING_NEW_ROOT_SHA','validation_scope':'Three independent producer strict official frontend/stock replay targets; 36 declaration audit = 14 production + 22 probe. Read-only evidence consumer PASS.','validation':{'compile':{'status':'PASS_STRICT_TRUST0','exit_code':0,'elapsed_seconds':prodt['strict_compile_seconds']},'kernel_replay':{'status':'PASS_ORIGINAL_LEANCHECKER','exit_code':0,'elapsed_seconds':prodt['stock_replay_seconds']},'axiom_audit':{'status':'PASS_COMPLETE_OWNED_IMPORT_BOUND','exit_code':0,'production_owned_declarations':14,'probe_owned_declarations':22,'actual_format':'DEFAULT_META_PPEXPR_COMPLETE'}},'declarations':{'owned_audited':14,'complete_received_production_types':14,'actual_type_formats':{'DEFAULT_META_PPEXPR_COMPLETE':14}},'direct_imports':['ImbalancedChen.SelectedPrefixRationalMesh'],'receiving_parts':['P1','P2','P3','P4-A','P5','P0'],'unclosed_real_inputs':permit_unclosed,'outstanding_component_validation_gates':[],'new_integration_sha':None,'new_integration_gates':'PENDING_ROOT_EXECUTION','intake_receipt':p1ref})
    for t in p1cand['targets']:
        if not t['source'].startswith('ImbalancedChen/'):continue
        b=git(t['source'],p1['source_commit']);check(sha(b)==t['source_sha256'],'fixed_fifth_candidate_source:'+t['module'])
        modules.append({'module':t['module'],'repository_path':t['source'],'part_owner':'P1','source':{'fixed_commit':p1['source_commit'],'latest_fixed_handoff':p1['source_commit'],'sha256':sha(b),'git_blob_sha1':subprocess.check_output(['git','rev-parse',p1['source_commit']+':'+t['source']],cwd=REPO,text=True).strip(),'snapshot':put_bytes('snapshot-sources/'+t['source'],b)},'compiled_object_sha256':None,'component_evidence_accepted':False,'accepted_at_previous_integration':False,'previous_integration_sha':None,'new_component_this_round':False,'new_fixed_candidate_this_round':True,'validation_status':'FIXED_SOURCE_UNCOMPILED_CANDIDATE','validation_scope':'Four separate historical targets never started; supplier queue stopped at 162 / 683. Permit success does not cover these leaves.','validation':{'compile':{'status':'NOT_STARTED','exit_code':None},'kernel_replay':{'status':'NOT_STARTED','exit_code':None},'axiom_audit':{'status':'NOT_STARTED','exit_code':None}},'declarations':{'owned_audited':None,'complete_received_production_types':0,'actual_type_formats':{},'source_headers_only':True},'direct_imports':re.findall(r'^import\s+(\S+)',b.decode(),re.M),'receiving_parts':['P1','P2','P3','P4-A','P5','P0'],'unclosed_real_inputs':['Explicit strict compilation, stock replay and complete defining-module audit of this fixed source.','The previously independently reported inherited-fifth single-module-compiled source remains SOURCE_PENDING; these fixed joint-cell sources do not identify it.','Full actualHistoricalFifthSaving nested-sum to tuple correction bridge, adopted multilevel policy instance, full integral composition and analytic K/c.'],'outstanding_component_validation_gates':['strict_compile','stock_kernel_replay','complete_owned_axiom_audit'],'new_integration_sha':None,'new_integration_gates':'EXCLUDED_UNTIL_COMPONENT_ACCEPTANCE','intake_receipt':p1candref})
    for n in p2['new_modules']:
        b=git(n['source'],p2['fixed_proof_commit']);check(sha(b)==n['source_identity']['sha256'] and b==git(n['source'],p2['source_head']),'new_P2_fixed_head_proof_source:'+n['module'])
        gs={g['action']:g for g in p2['original_gates'] if g['module']==n['module']}
        modules.append({'module':n['module'],'repository_path':n['source'],'part_owner':'P2','source':{'fixed_commit':p2['fixed_proof_commit'],'latest_fixed_handoff':p2['source_head'],'same_source_ci_commit':p2['ci']['head_sha'],'sha256':n['source_identity']['sha256'],'git_blob_sha1':n['source_identity']['git_blob_sha1'],'snapshot':put_bytes('snapshot-sources/'+n['source'],b)},'compiled_object_sha256':n['object_sha256'],'component_evidence_accepted':True,'accepted_at_previous_integration':False,'previous_integration_sha':None,'new_component_this_round':True,'validation_status':'SOURCE_ORIGINAL_GATES_AND_PART2_CI_ACCEPTED_PENDING_NEW_ROOT_SHA','validation_scope':'Exact proof/source/head identities, original per-target strict/replay object lineage and actual same-source Part2 CI explicit 12 modules / 709 owned declaration audit.','validation':{'compile':{'status':'PASS_STRICT_AND_EXPLICIT_PART2_CI',**gs['compile']},'kernel_replay':{'status':'PASS_ORIGINAL_AND_PART2_CI',**gs['replay']},'axiom_audit':{'status':'PASS_COMPLETE_OWNED_IMPORT_BOUND_PP_ALL','exit_code':0,'production_owned_declarations':n['declarations'],'part2_total_owned_declarations':709,'actual_format':'PP_ALL_COMPLETE','ci_run_id':p2['ci']['run_id'],'ci_job_id':p2['ci']['job_id']}},'declarations':{'owned_audited':n['declarations'],'complete_received_production_types':n['declarations'],'actual_type_formats':{'PP_ALL_COMPLETE':n['declarations']}},'direct_imports':re.findall(r'^import\s+(\S+)',b.decode(),re.M),'receiving_parts':p2['receivers'],'unclosed_real_inputs':p2['unclosed_inputs'],'outstanding_component_validation_gates':[],'new_integration_sha':None,'new_integration_gates':'PENDING_ROOT_EXECUTION','intake_receipt':p2ref})
    modules.sort(key=lambda m:(m['part_owner'],m['module']))
    check(len(modules)==37 and len({m['module'] for m in modules})==37,'new_37_module_census')
    check(sum(m['component_evidence_accepted'] for m in modules)==23,'new_23_component_evidence_acceptance')
    check(sum(not m['component_evidence_accepted'] for m in modules)==14,'new_14_pending_module_count')
    # Construct current complete received records; these are producer-reused, not new integration output.
    bymod={m['module']:m for m in modules};alltypes=list(restored)
    check(len(p1types['declarations'])==14 and not p1types['pp_all'],'new_P1_type_format_evidence')
    for r in p1types['declarations']:alltypes.append(type_record(r,'DEFAULT_META_PPEXPR_COMPLETE',bymod[r['module']]['source'],{'kind':'REUSED_FIXED_P1_PRODUCER_COMPILER_RECORD','receipt':p1ref,'record_source':p1typesref,'new_integration_type_export_pending':True}))
    check(len(p2types)==400 and p2['all_types_actual_pp_all'],'new_P2_type_format_evidence')
    for r in p2types:alltypes.append(type_record(r,'PP_ALL_COMPLETE',bymod[r['module']]['source'],{'kind':'REUSED_FIXED_P2_PRODUCER_AND_SAME_SOURCE_CI_COMPILER_RECORD','receipt':p2ref,'record_source':p2typesref,'ci_run_id':p2['ci']['run_id'],'new_integration_type_export_pending':True}))
    alltypes.sort(key=lambda r:(r['module'],r['name']))
    check(len(alltypes)==1005 and len({r['name'] for r in alltypes})==1005,'current_1005_complete_unique')
    check(Counter(r['actual_type_format'] for r in alltypes)=={'PP_ALL_COMPLETE':986,'DEFAULT_META_PPEXPR_COMPLETE':19},'current_1005_actual_formats')
    check(Counter(r['module'] for r in alltypes)=={m['module']:m['declarations']['owned_audited'] for m in modules if m['component_evidence_accepted']},'current_component_types_by_module')
    write('COMPONENT_TYPES_1005.json',alltypes)
    write('COMPONENT_TYPE_FORMATS_1005.json',[{'name':r['name'],'module':r['module'],'actual_type_format':r['actual_type_format'],'source_fixed_commit':r['source_fixed_commit'],'production_source_sha256':r['production_source_sha256'],'origin':r['provenance']['kind']} for r in alltypes])
    # P5 upstream is deliberately excluded from all ImbalancedChen module/type counts.
    upstream={'module':p5['module'],'fixed_handoff':p5['fixed_commit'],'dependency_name':'goldbach','dependency_pin':'09b97db5764ade1246bfb77206baa1b124760958','source_sha256':p5['source_sha256'],'object_sha256':p5['object_sha256'],'status':p5['status'],'counted_in_37_component_modules':False,'counted_in_1005_component_types':False,'declaration_count':8,'public_theorem_count':2,'actual_type_format':'PP_EXPLICIT_UNIVERSES_FULLNAMES_PROOFS_AND_RAW_EXPR_NOT_PP_ALL','format_details':p5['type_formats'],'gates_including_original_failure':p5['gate_records'],'receipt':p5ref,'types':p5typesref,'remaining_inputs':p5['remaining_inputs'],'next_target':p5['next_target'],'receiving_parts':p5['receiving_parts']}
    check(len(p5types)==8 and p5['module'].startswith('MathlibNt.'),'upstream_separate_8')
    write('UPSTREAM_S1LowerRosser.json',upstream)
    counts={'fixed_component_modules':37,'component_evidence_accepted_modules':23,'pending_component_modules':14,'already_root_validated_at_28fd_modules':19,'new_component_evidence_accepted_modules':4,'new_fixed_P1_uncompiled_modules':2,'inherited_complete_types':591,'inherited_pp_all_types':586,'inherited_default_complete_types':5,'new_received_complete_types':414,'new_received_pp_all_types':400,'new_received_default_complete_types':14,'current_received_complete_types':1005,'current_received_pp_all_types':986,'current_received_default_complete_types':19,'new_integration_root_validated_modules':0,'new_integration_root_gates_status':'PENDING_ROOT_EXECUTION','upstream_new_S1LowerRosser_owned_declarations_excluded':8}
    ledger={'schema':'chen-p0-round4-component-ledger-candidate-v1','generated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Fixed-source original evidence reception and actual prior-CI reconstruction; no Lean or CI execution in ledger builder.','proof_baseline':BASELINE,'manuscript_baseline':MANUSCRIPT,'source_branch':'codex/variable-envelope-boxes','integration_branch':'chatgpt/chen-p0-integration','previous_exact_integration_sha':P0,'new_integration':{'commit':None,'status':'PENDING_ROOT_PUBLICATION_AND_CANONICAL_GATES','full_build':'PENDING','root_stock_kernel_replay':'PENDING','root_axiom_audit':'PENDING','new_full_type_export':'PENDING','main_theorem_is_still_conditional':True,'hLower_hUpper_discharged':False},'counts':counts,'toolchain':old['toolchain'],'certificate':{**old['certificate'],'round4_accepted_E0_batch':p2['scope'],'overlap_rule':'Prefix64 already includes Prefix4 and Batch4To64. Do not add Prefix4 or the first cell again; K/80 already includes its quarter/Buchstab factor.','part4_upper_certificate_scope_extended':False},'prior_actual_root_validation':'PREVIOUS_CI_VALIDATION.json','modules':modules,'separate_prior_upstream_S1Carrier':old['separate_upstream_S1Carrier'],'separate_new_upstream_S1LowerRosser':upstream,'independently_reported_fifth_candidate':{'status':'SOURCE_PENDING','distinct_from_fixed_joint_cell_sources':True,'needed':['Full fixed source SHA or patch','Exact module and dependency list','Same-source original single-module compilation receipt']},'final_mathematical_inputs':old['final_mathematical_inputs'],'cross_part_inputs':old['cross_part_inputs'],'dependency_rule':'Part5 depends on Part4-A actual same-rho K, not Part4-B hUpper.','original_record_scope':{'old_module_records':oldref,'old_incomplete_or_mislabeled_type_records':oldtyperef,'format_corrections_file':'INHERITED_TYPE_FORMATS_591.json','never_interpret_old_publishing_time_pending_as_current_prior_CI_state':True},'local_actions':{'new_lean_execution':False,'new_CI_execution':False,'Git_ref_or_worktree_mutation':False,'output_only_under':str(HERE)}}
    write('MODULE_LEDGER_CANDIDATE.json',ledger)
    md=['# Part 0 Round 4：模块台账候选','',f'共同证明基线 `{BASELINE}`；手稿 `{MANUSCRIPT}`。','',f'前一实际核验集成 `{P0}`。本文件仅汇总固定源码与已执行原始回执；**本轮新集成 SHA 的规范门仍待 root 执行**。','',f'固定组件 **37**：**23** 已具可复用的完整组件证据，**14** 未完全接收。23 中的 19 已在上轮根门通过，本批新增 4（P1 permit 1 + P2 3）。另 2 个 P1 第五层源从未固定候选变成固定未编译候选。','', '## 类型口径','', '恢复上轮 591 项 = 586 项实际 pp.all + 5 项完整默认 Meta.ppExpr（Buchstab）。老 393 分区为 388 + 5；上轮实际 CI 新 198 均为 pp.all。旧 140 项 P1 默认输出（其中 7 项曾省略）已经由该实际 198 输出中的对应记录替换。','', '本批收到 414 项 = P1 14 项完整默认 Meta.ppExpr + P2 400 项 pp.all。当前合计 1005 项完整生产类型 = 986 pp.all + 19 默认完整；这是原始回执接收口径，不是本轮新集成类型导出执行结果。P5 S1LowerRosser 的 8 项依赖声明单列，不计入 37 或 1005。','', '## 模块清单','', '| Part | 模块 | 固定证明源 | 组件证据 / 新根门 | 完整生产类型 |','| --- | --- | --- | --- | ---: |']
    for m in modules:
        st=('旧根已通过 / 新根待执行' if m['accepted_at_previous_integration'] else '新组件原始门已通过 / 新根待执行') if m['component_evidence_accepted'] else '候选，未完全接收'
        md.append('| '+m['part_owner']+' | `'+m['module']+'` | `'+m['source']['fixed_commit']+'` | '+st+' | '+str(m['declarations']['complete_received_production_types'])+' |')
    md+=['','## 本批来源','',f'- P1 固定 `{p1["source_commit"]}`：许可模块 14；两历史叶仍未编译。',f'- P2 固定证明 `{p2["fixed_proof_commit"]}`；最新交接 `{p2["source_head"]}`；同源码实际 CI `{p2["ci"]["head_sha"]}`，run {p2["ci"]["run_id"]}。',f'- P5 固定交接 `{p5["fixed_commit"]}`：固定 goldbach 依赖 S1LowerRosser 8 项独立原始门已过，非新 ImbalancedChen 模块。','', '## 未闭合输入','', 'P1 仍需采用的实际历史表、继承 old 身份、覆盖/支持/因式分解及完整历史积分和桥；P2 仅闭合 E0 原始 [4,64) 与 Prefix64，剩余 E0/E1、saved-floor、全域并和及实际父许可仍缺；P3 实际分布供应未齐；P4-A 同一实际 rho 的 K、P4-B hUpper、P5 完整 Chen 均值及解析 c/hLower 仍缺。Part5 只等 Part4-A，不等 Part4-B。','', '继承前层选择、仅过单模块编译的独立第五层候选身份继续 SOURCE_PENDING；744316… 的两份 joint-cell 源不能冒作该候选。','', '## 旧 CI 实际回执','', '| 原始阶段 | 结果 | 秒 |','| --- | --- | ---: |','| 完整 build | 9798 jobs，exit 0 | 35 |','| 原装根 leanchecker | 19 接收模块均被 replay，exit 0 | 365 |','| 根 axiom-audit v0.1.2 | 5458 声明，标准三公理，exit 0 | 25 |','| Round3 类型导出 | 新198 + 主条件桥1，exit 0 | 473 |','', '该结果仅适用于 28fd630…；恢复过程未启动 Lean / CI。完整旧 CI 身份核对为 `PREVIOUS_CI_VALIDATION.json`。','', '详尽逐模块未闭合输入、第一诊断和原始来源请读 JSON 及固定来源证据；源码类型与编译器类型分别保留。']
    put_bytes('MODULE_LEDGER_CANDIDATE.md','\n'.join(md).encode())
    typemd=['# 恢复的上轮 591 项完整编译器类型','',f'固定集成 `{P0}`；586 项实际 pp.all，5 项完整默认 Meta.ppExpr。原始格式与逐声明来源在 JSON 中明确记录。','']
    for r in restored:typemd+=['## '+r['name'],'','模块 `'+r['module']+'`；格式 `'+r['actual_type_format']+'`。','','```lean',r['type'],'```','']
    put_bytes('INHERITED_TYPES_591.md','\n'.join(typemd).encode())
    write('BUILD_RECEIPT.json',{'status':'PASS_EVIDENCE_RECONSTRUCTION_ONLY','counts':counts,'checks':len(checks),'failures':[],'source_inputs':[oldref,oldtyperef,p1ref,p2ref,p5ref],'new_lean_or_ci_execution':False,'new_integration_sha':None,'new_integration_gates':'PENDING_ROOT_EXECUTION'})
    write('CHECKS.json',checks)
    manifests=[]
    for p in sorted(HERE.rglob('*')):
        if p.is_file() and p.name!='OUTPUT_MANIFEST.json':
            b=p.read_bytes();manifests.append({'path':str(p.relative_to(HERE)),'bytes':len(b),'sha256':sha(b)})
    write('OUTPUT_MANIFEST.json',{'files':manifests,'builder_scope':'Read-only ledger reconstruction. No Lean, CI, network, or Git mutation.'})
    print(json.dumps({'status':'PASS','counts':counts,'output':str(HERE),'output_files':len(manifests),'checks':len(checks)},ensure_ascii=False,indent=2))
except Exception as e:
    write('FIRST_CONSUMER_FAILURE.json',{'exception_type':type(e).__name__,'error':str(e),'checks':checks})
    raise
