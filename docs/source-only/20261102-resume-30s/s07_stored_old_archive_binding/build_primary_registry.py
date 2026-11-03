"""Primary source pins, declaration locations, and raw byte hashes only."""
from pathlib import Path
import hashlib,json,re
here=Path(__file__).resolve().parent
repo=here.parents[3]
q=json.loads((repo/'docs/source-only/20261102-resume-30q/fifth_parent/REGISTRY.json').read_text(encoding='utf8'))
r=json.loads((repo/'docs/source-only/20261102-resume-30r/fifth_old_defect/REGISTRY.json').read_text(encoding='utf8'))

def pin(p,module=None):
    p=Path(p);data=p.read_bytes()
    try: rel=p.relative_to(repo).as_posix()
    except ValueError: rel=p.as_posix()
    out={'path':rel,'absolute_path':p.as_posix(),'raw_sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
    if module: out.update(module=module,install_as=module.replace('.','/')+'.lean')
    return out

def lean(p):
    txt=p.read_text(encoding='utf8'); ns=re.search(r'^namespace (\S+)',txt,re.M).group(1)
    out=pin(p,ns);out['imports']=re.findall(r'^import (\S+)',txt,re.M)
    out['declarations']=[{'kind':m.group(1),'name':m.group(2),'line':txt[:m.start()].count('\n')+1}
        for m in re.finditer(r'^(?:private )?(def|abbrev|theorem|instance)\s+([^\s(:]+)',txt,re.M)]
    out.update(source_only=True,compiled=False,kernel_verified=False)
    return out

new=[lean(here/n) for n in ['P5OriginalTaylorRationalData.lean','P5OriginalStoredOldArchiveBinding.lean']]
modules={m for s in new for m in s['imports'] if not m.startswith('Mathlib')}
dependencies=[]
for rec in r['new_sources']+r['reused_dependencies']:
    if rec.get('module') in modules:
        dependencies.append(pin(rec['absolute_path'],rec['module']))
for name in ['P5SubdivisionStoredParentTypes','P5SubdivisionStoredParentArchive']:
    dependencies.append(pin(repo/f'docs/source-only/20261028-resume-30g/upper_fifth/{name}.lean','ImbalancedChen.'+name))
dependencies += [pin(x['absolute_path'],x.get('module')) for x in q['typed_source_authority']['interfaces']]
dependencies += [pin(repo/'docs/source-only/20261102-certificates-l/original_npy_kernel/P1HistoricalFifthOriginalNpyKernel.lean','ImbalancedChen.P1HistoricalFifthOriginalNpyKernel')]
data=[]
mismatches=[]
for rec in q['typed_source_authority']['blocks']+q['stored_parent_authority']['blocks']:
    x=pin(rec['absolute_path'],rec['module'])
    if x['raw_sha256']!=rec['raw_sha256'] or x['bytes']!=rec['bytes']: mismatches.append(x['path'])
    data.append(x)
originals=[pin(x['absolute_path']) for x in r['original_sources']]
context=[pin(repo/'docs/source-only/20261102-resume-30s/BRIEF.md'),
    pin(repo/'docs/source-only/20261102-resume-30r/fifth_old_defect/REPORT.md'),
    pin(repo/'docs/source-only/20261102-resume-30r/fifth_old_defect/REGISTRY.json'),
    pin(repo/'docs/source-only/20261102-resume-30r/reviews/r25_review_archive_history.md'),
    pin(repo/'docs/source-only/20261102-resume-30q/fifth_parent/REGISTRY.json'),
    pin(repo/'docs/source-only/20261102-resume-30q/fifth_keys/REPORT.md')]
reg={'batch':'20261102-resume-30s','slot':7,'task_id':'s07_stored_old_archive_binding',
    'owner':'/root/s07_stored_old_archive_binding','status':'PRIMARY_SOURCE_COMPLETE_UNCOMPILED',
    'assigned_primary_source_complete':True,'whole_D02_yellow_scope_closed':False,
    'compiled':False,'kernel_verified':False,'formal_credit':0,
    'original_parent_count':292633,'new_finite_bodies':72,'finite_bodies_status':'UNEVALUATED',
    'new_sources':new,'reused_sources':dependencies,'actual_typed_and_stored_literal_sources':data,
    'original_sources':originals,'context':context,'report':pin(here/'REPORT.md'),
    'support_scripts':[pin(here/'generate_binding_source.py'),pin(Path(__file__).resolve())],
    'data_integrity':{'raw_pin_mismatches_against_Q':mismatches,'raw_payload_parsed':False,
        'data_literals_rewritten':False,'raw_NPY_authentication_claimed':False,
        'raw_NPY_authentication_source':'Existing L ten-column full comparison reused; all finite bodies UNEVALUATED. Stored-old raw Unicode association is optional local work, outside primary payload.'},
    'terminal_declarations':['original_stored_old_eq_max','strict_stored_taylor_available',
        'strict_stored_taylor_primitive_facts','strict_stored_taylor_branchFacts',
        'strict_stored_old_eq_original_taylor_floor','actual_ranges'],
    'premises_removed':['Caller supplied old-floor equality/licence',
        'Caller supplied actual smooth-row BranchFacts and range/gap instances',
        'Any identification of the stored Taylor field with a newly defined defect'],
    'remaining':['All finite source truths, elaboration, dependency staging and same-source remote kernel/axiom evidence',
        'S04/S05/S06/S08 complete parent-integral/endpoint assembly, independently supplied',
        'Broader P1.4 original raw stored Unicode NPY authentication not claimed'],
    'primary_publish_allowlist':[x['path'] for x in new]+[
        (here/n).relative_to(repo).as_posix() for n in ['REPORT.md','REGISTRY.json','generate_binding_source.py','build_primary_registry.py']],
    'local_only_excluded_from_primary_publication':[
        'provenance/original-stored-old/**','P5OriginalStoredOldByteParser.lean',
        'P5OriginalStoredOldBytesBlock*.lean','P5OriginalStoredOldBytesComplete.lean',
        'materialize_original_old_bytes.py','ORIGINAL_OLD_BYTE_EXTRACTION.json','BYTE_MATERIALIZATION.log'],
    'mathlib_revision':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1',
    'lean_toolchain':'leanprover/lean4:v4.33.0-rc1',
    'operations':{'compiler':False,'guard_execution':False,'numerical_replay':False,
        'git_or_CI_mutation':False,'subagents':False,'metadata_only_static_checks':True}}
(here/'REGISTRY.json').write_text(json.dumps(reg,indent=2,ensure_ascii=False)+'\n',encoding='utf8')
print(json.dumps({'new_sources':len(new),'data_source_pins':len(data),'pin_mismatches':mismatches,
    'primary_source_hashes':[{k:x[k] for k in ['path','raw_sha256','bytes']} for x in new]}))
