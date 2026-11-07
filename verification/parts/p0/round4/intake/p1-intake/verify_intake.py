#!/usr/bin/env python3
"""Read-only fixed Git object / archived evidence consumer. Never invokes Lean or CI."""
from pathlib import Path, PurePosixPath
from collections import Counter
import subprocess, json, hashlib, re, datetime, tarfile
BASE=Path(__file__).resolve().parent
REPO=BASE.parent.parent/'goldbach-formalization'
SHA='744316efd1887f21c91dd4b63c218fa27704c931'
P0='28fd630ef7cc38eba86beb6c0ba123336b5d05f2'
PREFIX='verification/parts/p1/round2/permit/'
EVID=BASE/'permit-evidence'
FIXED=BASE/'fixed-source'
PROD='ImbalancedChen.StoredHistoricalBoxPermit'
ALLOWED={'propext','Classical.choice','Quot.sound'}
checks=[]
def check(condition,label,detail=None):
    checks.append({'check':label,'pass':bool(condition),'detail':detail})
    if not condition: raise AssertionError(label+': '+repr(detail))
def digest(b): return hashlib.sha256(b).hexdigest()
def git(path,sha=SHA):return subprocess.check_output(['git','show',sha+':'+path],cwd=REPO)
def write(name,value): (BASE/name).write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n')
def data(path):return json.loads((EVID/path).read_text())
try:
    art=json.loads((FIXED/PREFIX/'ARTIFACT.json').read_text())
    archive=(FIXED/PREFIX/'EVIDENCE.tar.gz').read_bytes()
    check(digest(archive)==art['sha256'] and len(archive)==art['bytes'],'fixed_archive_identity',art)
    manifest=data('MANIFEST.json')
    with tarfile.open(FIXED/PREFIX/'EVIDENCE.tar.gz','r:gz') as tf:
        ms=tf.getmembers(); manifestrows={r['member']:r for r in manifest['members']}
        check(len(ms)==art['member_count'] and len(set(m.name for m in ms))==len(ms),'archive_count_unique',len(ms))
        check(set(m.name for m in ms)==set(manifestrows)|{'MANIFEST.json'},'archive_member_census')
        for m in ms:
            pp=PurePosixPath(m.name)
            check(m.isfile() and not pp.is_absolute() and '..' not in pp.parts,'archive_safe_file:'+m.name)
            content=tf.extractfile(m).read()
            check(content==(EVID/m.name).read_bytes(),'archive_extraction_exact:'+m.name)
            if m.name!='MANIFEST.json':
                row=manifestrows[m.name];check(digest(content)==row['sha256'] and len(content)==row['bytes'],'archive_member_digest:'+m.name)
    receipt_bytes=(FIXED/PREFIX/'VERIFICATION.json').read_bytes();d=json.loads(receipt_bytes)
    check(receipt_bytes==(EVID/'runtime/part1-permit-final-receipt.json').read_bytes(),'receipt_byte_identity')
    check(digest(receipt_bytes)==art['receipt_sha256']==manifest['receipt_sha256'],'receipt_digest')
    check(d['status']=='VERIFIED' and d['verification']['trustLevel']==0 and d['verification']['target_warning_as_error'] and not d['verification']['metadata_adapter_during_compilation_or_replay'],'producer_execution_mode')
    binding=data('runtime/logs/round2/permit/dependency-bindings.json')
    state=data('runtime/logs/round2/permit/compile/state.json')
    by_original={r['original_path']:r for r in manifest['members']}
    omitted={r['original_path']:r for r in manifest['unembedded_verified_references']}
    def resolve(path):
        row=by_original.get(path)
        if row:return EVID/row['member']
        for alias in manifest['original_log_aliases']:
            if alias['original_path']==path:return resolve(alias['resolved_path'])
        raise KeyError(path)
    # Preserve honest distinction: digest consistency for omitted objects, byte checks for embedded text.
    refs={}
    def walk(v):
        if isinstance(v,dict):
            if isinstance(v.get('path'),str) and isinstance(v.get('sha256'),str):
                refs[(v['path'],v['sha256'],v.get('bytes'))]=v
            for a in v.values():walk(a)
        elif isinstance(v,list):
            for a in v:walk(a)
    walk(d);walk(binding)
    refcounts=Counter()
    for (path,sha,sz),v in refs.items():
        r=by_original.get(path) or omitted.get(path)
        if r is None:
            try:
                content=resolve(path).read_bytes();check(digest(content)==sha and (sz is None or len(content)==sz),'reference_alias:'+path);refcounts['embedded_alias']+=1;continue
            except KeyError:pass
        check(r is not None,'reference_is_archived_or_explicitly_omitted:'+path)
        check(r['sha256']==sha and (sz is None or r['bytes']==sz),'reference_digest_binding:'+path)
        refcounts['embedded' if path in by_original else 'omitted_digest_only']+=1
    copied=[]
    for name,row in manifestrows.items():
        if name.startswith('repo/'):
            rel=name[len('repo/'):];content=(EVID/name).read_bytes()
            check(git(rel)==content,'archived_repo_file_matches_fixed_commit:'+rel)
            copied.append(rel)
    pins=[]
    for rel in ['lean-toolchain','lake-manifest.json','lakefile.toml','docs/CURRENT_MANUSCRIPT_MAP.md','docs/EXTERNAL_REUSE.md','ImbalancedChen/CurrentMainTheorem.lean','ImbalancedChen/CurrentNumericalTransfer.lean']:
        b=git(rel);check(b==git(rel,P0),'protected_input_unchanged:'+rel)
        pins.append({'path':rel,'sha256':digest(b)})
    local=binding['local_modules'];cached=binding['cached_modules']
    check(len(local)==16 and len(cached)==3368 and binding['source_module_count']==3384,'supplier_closure_census')
    localrows=[];import_count=0
    allmods={**local,**cached}
    for module,row in local.items():
        source=resolve(row['source']['path']).read_bytes();rel=row['source']['path'].split('/goldbach-formalization/',1)[1]
        check(source==git(rel),'local_supplier_fixed_source:'+module)
        st=state[module]
        check(st['source_sha256_before']==st['source_sha256_after']==digest(source),'local_compile_source_binding:'+module)
        obj=row['artifact_parts'][module.split('.')[-1]+'.olean']['sha256']
        check(st['olean_sha256']==obj and st['returncode']==0,'local_compile_object_exit:'+module)
        log=resolve(row['raw_compile_log']['path']).read_text()
        check('FRONTEND_OK module='+module+' trustLevel=0' in log,'local_original_frontend_marker:'+module)
        # All direct local imports are bound to recorded source/object records; official Lean core import separately bound.
        imports=row['direct_import_olean_sha256']
        check(imports==st['import_olean_sha256'],'local_compile_direct_import_record:'+module)
        for imp,imp_sha in imports.items():
            if imp in allmods:
                part=allmods[imp]['artifact_parts'][imp.split('.')[-1]+'.olean']['sha256']
                check(part==imp_sha,'internal_import_object_identity:'+module+' -> '+imp)
            else:
                check(imp.startswith('Lean.') or imp=='Lean' or imp.startswith('Lake.'),'external_import_is_toolchain:'+module+' -> '+imp)
            import_count+=1
        localrows.append({'module':module,'source':rel,'source_sha256':digest(source),'object_sha256':obj,'new_this_batch':row['compiled_in_permit']})
    replay=d['replay'];check(replay['returncode']==0 and replay['verified'],'replay_success')
    for prefix in ['source_sha256','artifacts_sha256','direct_import_olean_sha256']:
        check(replay[prefix+'_before']==replay[prefix+'_after'],'replay_stable_'+prefix)
    targetrows=[]
    for module,t in d['targets'].items():
        check(t['returncode']==0 and t['strict'] and t['trustLevel']==0 and not t['metadata_adapter'],'target_strict_compile:'+module)
        check(t['source_sha256_before']==t['source_sha256_after']==replay['source_sha256_before'][module],'target_source_replay_binding:'+module)
        check(t['import_olean_sha256']==replay['direct_import_olean_sha256_before'][module],'audit_and_replay_import_binding:'+module)
        check(t['olean_sha256']==replay['artifacts_sha256_before'][module][module.split('.')[-1]+'.olean'],'target_object_replay_binding:'+module)
        log=resolve(t['log']['path']).read_text();check('strict=strict Lean.githash=62eed1db4d67327ec8120be05f1a1b0847d74561' in log,'actual_strict_and_lean_commit:'+module)
        call=next(c for c in replay['calls'] if c['module']==module)
        rlog=resolve(call['log']).read_text()
        check(digest(rlog.encode())==call['log_sha256'],'replay_raw_log_digest:'+module)
        check(call['returncode']==0 and call['observed_replay_lines']==[module] and module in rlog and call['command'][-2:]==['--verbose',module],'actual_original_replay_target:'+module)
        targetrows.append({'module':module,'source_sha256':t['source_sha256_before'],'object_sha256':t['olean_sha256'],'strict_compile_seconds':t['elapsed_seconds'],'stock_replay_seconds':call['elapsed_seconds'],'compile_exit':t['returncode'],'replay_exit':call['returncode']})
    auditlog=resolve(d['audit']['full_types_in_raw_audit_log']['path']).read_text()
    rows=[json.loads(line.split(' ',1)[1]) for line in auditlog.splitlines() if line.startswith('PART1_STORED_CAP_AUDIT_DECL ')]
    counts=Counter(r['module'] for r in rows)
    check(rows==d['audit']['declarations'],'audit_raw_declarations_equal_receipt')
    check(len(rows)==len(set(r['name'] for r in rows))==36 and dict(counts)==d['audit']['module_counts'],'complete_audit_census',dict(counts))
    check('PART1_STORED_CAP_AUDIT_COUNT 36' in auditlog,'audit_complete_footer')
    check(set().union(*(set(r['axioms']) for r in rows))==ALLOWED and all(r['kind']!='axiom' for r in rows),'transitive_axiom_allowlist')
    elided=[r['name'] for r in rows if any(marker in r['type'] for marker in ['⋯','...','…','<proof>','<unavailable>'])]
    check(not elided,'complete_default_ppExpr_types',elided)
    audit_source=git(PREFIX+'StoredCapAudit.lean').decode()
    check('env.constants.fold' in audit_source and 'getModuleIdxFor?' in audit_source and 'info.isUnsafe' in audit_source and 'info.isAxiom' in audit_source and 'collectAxioms name' in audit_source,'owned_declaration_audit_mechanism')
    check('pp.all' not in audit_source,'types_format_is_default_Meta_ppExpr_not_pp_all')
    prodsource=git('ImbalancedChen/StoredHistoricalBoxPermit.lean').decode()
    prodcode=re.sub(r'/\-.*?\-/','',prodsource,flags=re.S)
    check(not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe)\b',prodcode),'production_no_prohibited_proof_tokens')
    check(re.findall(r'^import\s+(\S+)',prodsource,re.M)==['ImbalancedChen.SelectedPrefixRationalMesh'],'minimal_production_import')
    source_heads=[]
    for m in re.finditer(r'^(?:theorem|def)\s+(\S+)',prodsource,re.M):
        start=m.start();end=prodsource.find(':=',m.end());check(end>=0,'source_header_end:'+m.group(1))
        source_heads.append({'name':'ImbalancedChen.'+m.group(1),'type_source_declaration':prodsource[start:end].rstrip(),'source_sha256':digest(prodsource.encode()),'format':'SOURCE_DECLARATION_HEAD'})
    check(len(source_heads)==12,'source_public_inventory_two_defs_ten_theorems')
    write('SOURCE_DECLARATIONS_12.json',source_heads)
    write('COMPILER_TYPES_36.json',{'source_commit':SHA,'format':'DEFAULT_META_PPEXPR_COMPLETE_NO_ELISION','pp_all':False,'source_audit_sha256':digest(audit_source.encode()),'raw_audit_log_sha256':digest(auditlog.encode()),'declarations':rows})
    write('COMPILER_TYPES_PRODUCTION_14.json',{'source_commit':SHA,'format':'DEFAULT_META_PPEXPR_COMPLETE_NO_ELISION','pp_all':False,'module':PROD,'declarations':[r for r in rows if r['module']==PROD]})
    md=['# Fixed P1 stored-cap complete interfaces','',f'Source: `{SHA}`. Source declaration heads and original compiler records are separate. Actual compiler formatting is default `Meta.ppExpr`, not `pp.all`; all 14 production records and all 36 including probes have no elision markers.','']
    for row in source_heads:
        compiler=next(r for r in rows if r['name']==row['name'])
        md.extend(['## '+row['name'],'','Source declaration head:','','```lean',row['type_source_declaration'],'```','','Original compiler type:','','```lean',compiler['type'],'```','','Axioms: '+', '.join('`'+a+'`' for a in compiler['axioms'])+'.',''])
    (BASE/'KEY_INTERFACES.md').write_text('\n'.join(md))
    summary={'status':'PASS_ARCHIVED_EVIDENCE_REUSE','source_commit':SHA,'against_integration':P0,'mathematical_baseline':d['mathematical_baseline_commit'],'archive_sha256':art['sha256'],'archive_bytes':art['bytes'],'archive_members':art['member_count'],'payload_files_verified':len(manifestrows),'explicit_omitted_digest_only_references':len(omitted),'recursive_reference_counts':dict(refcounts),'fixed_git_files_verified':len(copied),'local_supplier_count':len(local),'local_direct_import_bindings':import_count,'cached_source_and_artifact_inventory_count':len(cached),'targets':targetrows,'production_modules':[PROD],'production_declarations':14,'probe_declarations':22,'allowed_axioms':sorted(ALLOWED),'type_format':'DEFAULT_META_PPEXPR_COMPLETE_NO_ELISION','local_lean_or_ci_started':False,'root_build_or_replay_claimed':False,'notes':['This consumer verifies archived bytes and cross-record object bindings; compiled binaries are intentionally not embedded or locally rehashed.','Producer used official Lean.Elab.runFrontend via unchanged Lake, trustLevel 0, strict warnings, then stock checker; normal stock CLI startup failed.','Official Lean.enableInitializersExecution appears as an unsafe runtime lifecycle call in the archived driver; it is not imported by production proof modules. No new driver or Lean invocation was executed by this intake.','The fixed resulting P0 integration SHA still requires canonical root gates and new full pp.all export.'],'protected_inputs':pins,'local_suppliers':localrows,'checks_count':len(checks),'failures':[],'recorded_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    write('REUSE_RECEIPT.json',summary);write('CHECKS.json',checks)
    print(json.dumps({k:v for k,v in summary.items() if k not in ['protected_inputs','local_suppliers','notes']},ensure_ascii=False,indent=2))
except Exception as e:
    write('FIRST_CONSUMER_FAILURE.json',{'error_type':type(e).__name__,'error':str(e),'checks':checks})
    raise
