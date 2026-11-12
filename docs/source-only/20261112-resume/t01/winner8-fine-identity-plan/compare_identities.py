"""Read-only source/closure/artifact-receipt comparison. No proof or prepare run."""
from pathlib import Path
import ast, collections, hashlib, json, re
BASE=Path('E:/timot/Documents/FilesForGPT/Myath');HERE=Path(__file__).resolve().parent
REPO=BASE/'goldbach-proof-continuation'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def ident(p):
    b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b)}
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
FP=BASE/'output/resume-20261112/t01/density-validation-v2/DENSITY_MANIFEST.json';F=load(FP);FM={r['module']:r for r in F['files']}
SP=BASE/'output/resume-20261112/t01/new-target-validation-plan/STATIC_SOURCE_SELECTION.json';S=load(SP);SM={r['module']:r for r in S['modules']}
targets=sorted(r['module'] for r in S['target_rows'] if r['package']=='winner-next');assert len(targets)==8
winner=set().union(*(set(S['target_closures'][t]['modules']) for t in targets));assert winner<=set(SM)
common=sorted(winner&set(FM));new=sorted(winner-set(FM));fine_only=sorted(set(FM)-winner)
different=[{'module':n,'Fine':FM[n],'winner':SM[n]} for n in common if FM[n]['sha256']!=SM[n]['sha256']]
assert set(new)==set(targets) and not different
native={r['module']:r for r in F['native_sources']}
direct_external=sorted({im for n in winner for im in SM[n]['imports'] if not im.startswith('ImbalancedChen.')})
fine_external={im for r in F['files'] for im in r['imports'] if not im.startswith('ImbalancedChen.')}
native_direct=sorted(n for n in direct_external if n.startswith('MathlibNt.'))
research=set();native_external=set()
def native_visit(n):
    if n in research:return
    if n not in native:native_external.add(n);return
    research.add(n)
    for im in native[n]['imports']:
        if im.startswith('MathlibNt.'):native_visit(im)
for n in native_direct:native_visit(n)
assert not(set(direct_external)-fine_external)
assert research<=set(native)
winner_rows=[SM[n] for n in sorted(winner)]
union_rows=[FM[n] for n in sorted(FM)]+[SM[n] for n in new]
dump('WINNER8_FINE_CLOSURE_COMPARISON.json',{
 'schema':'T01_WINNER8_FINE_EXACT_CLOSURE_COMPARISON_V1','Fine_manifest':ident(FP),'source_selection':ident(SP),'winner_targets':targets,
 'counts':{'Fine_project_modules':len(FM),'winner_project_modules':len(winner),'common_names':len(common),'identical_common_sources':len(common)-len(different),'differing_common_sources':len(different),'winner_only':len(new),'Fine_only':len(fine_only),'combined_project_modules':len(FM)+len(new),'Fine_native_research_copies':len(native),'winner_reached_native_research_copies':len(research),'new_native_research_copies':len(research-set(native)),'combined_mathematical_module_count_if_existing_native_scope_retained':len(FM)+len(new)+len(native)},
 'intersection':common,'winner_only':[SM[n] for n in new],'Fine_only':fine_only,'different_common_sources':different,'winner_complete_project_rows':winner_rows,
 'native':{'direct_MathlibNt_imports':native_direct,'research_reachable':sorted(research),'research_rows':[native[n] for n in sorted(research)],'canonical_locked_native_direct_or_boundary':sorted((set(native_direct)|native_external)-research),'all_winner_research_sources_are_in_Fine43':True,'new_direct_external_imports_vs_Fine':sorted(set(direct_external)-fine_external),'extra_native_source_or_overlay_selected':False,'distinction':'Canonical locked MathlibNt dependencies are not themselves members of the research43; all occur already in the existing Fine import environment. No new native transitive reachability is introduced by the eight new sources.'},
 'combined_sources':union_rows,'accepted_cached_objects':[],'Fine_prepared_is_not_a_passed_closure':True,'audit_wrappers_not_added_or_counted_here':True,'source_replacement_performed':False})

# Independently traverse the actual Fine mathematical target. Do not infer
# reachability from a source merely being present in the manifest.
target='ImbalancedChen.P4AOriginalFiniteAll22FineDensity';parent={target:None};todo=collections.deque([target])
while todo:
    n=todo.popleft();assert n in FM,n
    for im in FM[n]['imports']:
        if im.startswith('ImbalancedChen.') and im not in parent:parent[im]=n;todo.append(im)
assert len(parent)==len(FM)
def path(n):
    a=[]
    while n is not None:a.append(n);n=parent[n]
    return list(reversed(a))
AP0=BASE/'output/resume-20261112/t10/SCOPE_ALLOWLIST.json';AP1=BASE/'output/resume-20261112/t10/STORED_009_019_ALLOWLIST.json'
A0=load(AP0);A1=load(AP1);accepted={};batch_rows=[]
assert sha(AP0.read_bytes())==A1['previous_green_allowlist_sha256']
batch_specs=[('000-004-43033551155',A0['stored'][0]),('005-008-43080955096',A0['stored'][1]),('009-019-43122130246',A1)]
for dirname,review in batch_specs:
    directory=BASE/'output/resume-20261112/ci'/('stored-blocks-'+dirname)
    repair=load(directory/'STORED_BATCH_REPAIRS.json');accept=load(directory/'BATCH_ACCEPTANCE.json');snapshot=load(directory/'BATCH_OBJECTS_BEFORE.json')
    assert accept['status']=='PASS_SELECTED_BLOCKS_ONLY' and not accept['whole_t01_accepted']
    indexed=review.get('staged_scope') or {r['module']:r for r in review['new_scope']['modules']}
    facet_rows=[]
    for r in repair['repairs']:
        n=r['module'];stem=n.split('.')[-1];source=directory/'compiled-blocks'/(stem+'.lean');b=source.read_bytes();assert sha(b)==r['new_sha256']
        rec=indexed[n];review_new=rec.get('repaired_source_sha256') or rec.get('compiled_source_sha256');assert sha(b)==review_new
        source_key=n.replace('.','/')+'.lean';olean_key='.lake/build/lib/lean/'+n.replace('.','/')+'.olean'
        assert snapshot[source_key]==sha(b)
        olean_hash=rec.get('replayed_olean_sha256') or rec.get('olean_sha256');assert snapshot[olean_key]==olean_hash
        saved=[p.name for p in (directory/'compiled-blocks').glob(stem+'.*')]
        assert stem+'.olean' in saved and stem+'.olean.hash' in saved
        chunk_count=len(re.findall(r'^private theorem source_index_chunk_\d+\b',b.decode(),re.M))
        # Some producers make helper theorems public. Count the actual names.
        if not chunk_count:chunk_count=len(re.findall(r'^(?:private )?theorem source_index_chunk_\d+\b',b.decode(),re.M))
        payloads=[{'path':str(directory/'compiled-blocks'/q),'bytes':(directory/'compiled-blocks'/q).stat().st_size,'sha256':sha(b) if q.endswith('.lean') else snapshot[olean_key+('.hash' if q.endswith('.hash') else '')],'hash_authority':'Source rehashed here; object/sidecar hashes reused from exact T10-accepted snapshot.'} for q in saved]
        accepted[n]={'run_id':review['run_id'],'source_commit':review.get('source_commit') or review.get('driver_commit'),'artifact_id':review.get('artifact_id'),'artifact_zip':str(directory)+'.zip','artifact_sha256_from_T10':review['artifact_sha256'],'T10_review_source':str(AP0 if 'staged_scope' in review else AP1),'postimage_source':str(source),'postimage_sha256':sha(b),'postimage_git_blob_sha1':blob(b),'old_source_sha256':r['old_sha256'],'replayed_olean_sha256':olean_hash,'source_index_chunk_theorem_count':chunk_count,'saved_facets':payloads,'accepted_scope':'Literal rows count and sourceIndex alignment only; not old/new Q80 correctness or whole floor.'}
        facet_rows.append({'module':n,'source_sha256':sha(b),'olean_sha256_from_accepted_snapshot':olean_hash,'present_payloads':payloads,'missing_from_archive':['.ilean','.c/native objects','Lake .trace and actual setup/import-artifact files'],'rebind_accepted':False})
    parent_types='ImbalancedChen.P5SubdivisionStoredParentTypes';pp=FM[parent_types]
    pkey='.lake/build/lib/lean/'+parent_types.replace('.','/')+'.olean'
    expected_parent=(review.get('parent_type') or {}).get('snapshot_olean_sha256') or next(r['olean_sha256'] for r in review['new_scope']['modules'] if r['module']==parent_types)
    expected_parent_source=(review.get('parent_type') or {}).get('source_sha256') or next(r['compiled_source_sha256'] for r in review['new_scope']['modules'] if r['module']==parent_types)
    assert pp['sha256']==expected_parent_source
    assert snapshot[pkey]==expected_parent
    state=load(directory/'runtime/state.json');audit=load(directory/'runtime/audit.json')
    assert sha((directory/'runtime/state.json').read_bytes())==audit['state_sha256']
    assert sha((directory/'runtime/compiler-commands.jsonl').read_bytes())==audit['command_log_sha256']
    batch_rows.append({'directory':str(directory),'run_id':review['run_id'],'artifact_sha256_from_review':review['artifact_sha256'],'acceptance':ident(directory/'BATCH_ACCEPTANCE.json'),'snapshot':ident(directory/'BATCH_OBJECTS_BEFORE.json'),'repair_receipt':ident(directory/'STORED_BATCH_REPAIRS.json'),'runtime_audit':ident(directory/'runtime/audit.json'),'commands':ident(directory/'runtime/compiler-commands.jsonl'),'dependency_receipt':ident(directory/'dependencies.json'),'parent_module':{'module':parent_types,'Fine_selected_source_sha256':pp['sha256'],'replayed_parent_olean_snapshot_sha256':expected_parent,'parent_olean_bytes_in_archive':False},'module_facets':facet_rows,'existing_proof_evidence_reused':True,'complete_Lake_restore_facets_present':False,'coherent_restore_or_ABI_rebind_claimed':False})
assert len(accepted)==20
stored=[]
for k in range(72):
    n=f'ImbalancedChen.Data.P5SubdivisionStoredBlock{k:03}';r=FM[n];b=(REPO/r['origin']['path']).read_bytes();assert sha(b)==r['sha256'] and blob(b)==r['git_blob_sha1']
    text=b.decode();m=re.search(r'theorem source_index_at\b([\s\S]*?)\nend ',text);assert m and ':= by\n  decide' in m.group(0)
    row={'module':n,'Fine_selected':r,'actually_reachable_from_Fine_target':n in parent,'import_path':path(n),'Fine_source_index_at_proof':'original whole-block by decide; no kernel-bounded source_index_chunk helpers','Fine_selected_chunk_count':len(re.findall(r'(?:private )?theorem source_index_chunk_\d+\b',text)),'accepted_postimage':accepted.get(n)}
    if n in accepted:
        post=accepted[n];assert r['sha256']==post['old_source_sha256']
        rb=Path(post['postimage_source']).read_bytes();prefix=b.split(b'/-- Positional index alignment, closed source only; not executed. -/')[0]
        row['literal_prefix_through_rows_size_unchanged']=rb.startswith(prefix)
        assert row['literal_prefix_through_rows_size_unchanged']
        row['same_Fine_source_as_accepted_postimage']=r['sha256']==post['postimage_sha256'];assert not row['same_Fine_source_as_accepted_postimage']
        row['old_by_decide_source_covered_by_postimage_acceptance']=False
    stored.append(row)
dump('STORED72_FINE_VS_ACCEPTED20.json',{'schema':'T01_FINE_STORED72_VS_ACCEPTED20_EXACT_IDENTITIES_V1','Fine_manifest':ident(FP),'Fine_target':target,'Fine_actual_DFS_project_module_count':len(parent),'reached_stored_blocks':72,'original_whole_block_decide_sources_selected':72,'accepted_kernel_bounded_postimages_available':20,'same_source_as_accepted_postimage':0,'different_source_from_accepted_postimage':20,'rows':stored,'T10_allowlists':[ident(AP0),ident(AP1)],'Fine_frozen_source_selection_not_changed':True,'remaining52_not_claimed_accepted_by_these_receipts':True})
dump('EXISTING_STORED_ARTIFACT_FACETS.json',{'schema':'T01_EXISTING_STORED_PROOF_PAYLOAD_SCOPE_V1','batches':batch_rows,'zip_downloaded_or_extracted_again':False,'zip_or_olean_rehashed_again':False,'existing_T10_zip_member_object_hash_validation_reused':True,'source_postimages_rehashed_for_identity_comparison':True,'coherent_restore_accepted':False,'actual_reuse':'Preserve the accepted repaired proof sources, existing20 olean bytes/hash sidecars, T10 exact type/axiom/kernel receipts and actual runtime/snapshot evidence. These are reliable selected leaves; do not prove their statements anew.','actual_shortfall':'No complete source+parent+setup/import/trace/native facet restore bundle is retained. The parent olean snapshot exists but its bytes were not archived. No installer restoration or ABI rebinding is established.'})

# A future explicit postimage repin invalidates actual import dependants. This
# is planning metadata only; no source selection is changed.
union={r['module']:r for r in union_rows};reverse={n:set() for n in union}
for n,r in union.items():
    for im in r['imports']:
        if im in reverse:reverse[im].add(n)
cone=set(accepted);todo=list(cone)
while todo:
    n=todo.pop()
    for p in reverse[n]:
        if p not in cone:cone.add(p);todo.append(p)
dump('FUTURE_REPIN_DEPENDENCY_CONE.json',{'status':'PLANNED_ONLY_NO_REPIN_PERFORMED','changed_source_roots':sorted(accepted),'combined_source_modules':len(union),'reverse_import_cone':sorted(cone),'reverse_import_cone_count':len(cone),'old_Fine_driver_and_ca9_unchanged':True,'source_or_import_match_is_not_restore_acceptance':True,'note':'Module-name census does not change for a20-source proof-only repin; serialized declaration inventories do change because the accepted postimages include chunk helper declarations.'})
dump('STATIC_CHECKS.json',{'python_AST_parsed':bool(ast.parse(Path(__file__).read_text(encoding='utf-8'))),'winner_targets':len(targets),'winner_modules':len(winner),'Fine_common_same':len(common),'winner_new':len(new),'Fine_source_replacements':len(different),'native_research_reachable':len(research),'new_native_research':0,'Fine_DFS_1808':len(parent)==1808,'Stored72_reached':all(r['actually_reachable_from_Fine_target'] for r in stored),'Stored72_original_decide':all(r['Fine_selected_chunk_count']==0 for r in stored),'postimages20_all_different':all(not r['same_Fine_source_as_accepted_postimage'] for r in stored if r['accepted_postimage']),'postimages20_literal_prefixes_preserved':all(r['literal_prefix_through_rows_size_unchanged'] for r in stored if r['accepted_postimage']),'postimage_chunk_counts':sorted({r['source_index_chunk_theorem_count'] for r in accepted.values()}),'stage_prepare_guard_or_proof_execution':False,'new_download':False})
print(json.dumps({'Fine':len(FM),'winner':len(winner),'intersection':len(common),'Fine_only':len(fine_only),'winner_only':len(new),'replacements':len(different),'combined':len(union),'winner_native_direct':len(native_direct),'winner_native_research':len(research),'Fine_native43':len(native),'new_external':len(set(direct_external)-fine_external),'math_union':len(union)+len(native),'Stored72_original':72,'accepted20_different':20,'future_repin_cone':len(cone),'chunk_counts':sorted({r['source_index_chunk_theorem_count'] for r in accepted.values()})},indent=2))
