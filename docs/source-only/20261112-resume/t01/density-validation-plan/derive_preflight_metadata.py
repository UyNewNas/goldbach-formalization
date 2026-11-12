"""Derive static preflight receipts; hashes archive bytes, never evaluates certificates."""
from pathlib import Path
import hashlib,json,zipfile

B=Path('E:/timot/Documents/FilesForGPT/Myath')
R=B/'goldbach-proof-continuation'
H=B/'output/resume-20261112/t01/density-validation-plan'
P=R/'docs/source-only/20261110-yellow-closure-10t/t06_actual_mixed_fourier/full87_remote_v3'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def put(n,v):(H/n).write_text(json.dumps(v,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def receipt(p):
    b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b),git_blob_sha1=blob(b))

base=read(P/'EXACT_INSTALL_MANIFEST.json')
runtime=read(P/'RUNTIME_SETUP_IMPORT_ACCEPTANCE_MAP.json')
graph=read(H/'STATIC_DEPENDENCIES.json')
assert graph['closure_complete']
rows={r['module']:r for r in graph['modules']}
active=set(rows)
old_paths=set()
for r in runtime['project_module_inputs']:
    if r['module'] in active:old_paths.update(r['declared_direct_compile_time_input_paths'])
old_data=[r for r in base['data_inputs'] if r['install_path'] in old_paths or r.get('consuming_module') in active]
unmapped_old_paths=sorted(old_paths-{r['install_path'] for r in old_data})

g7_path=R/'docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/successor_G7/G7_INPUT_BINDINGS.json'
later_path=R/'docs/source-only/20261110-yellow-closure-10t/t05_all22_actual_density/successor_sixth_history/LATER_PAYMENT_REGISTRY.json'
g7=read(g7_path)['compile_inputs']
later=read(later_path)['original_fixture_inputs']
archive=B/'tmp/publication-20261010/verification-renewal-v2/_release/chen-numerical-evidence-20261010.zip'
assert archive.stat().st_size==base['release_asset']['bytes']
new_data=[]
with zipfile.ZipFile(archive) as z:
    names=z.namelist();assert len(names)==len(set(names))
    for r in g7+later:
        name=Path(r['path']).name
        hits=[s for s in names if s.endswith('/'+name)]
        assert len(hits)==1,(name,hits)
        b=z.read(hits[0]);assert len(b)==r['bytes'] and sha(b)==r['sha256'],name
        if 'git_blob_sha1' in r:assert blob(b)==r['git_blob_sha1']
        new_data.append(dict(install_path='../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/'+name,
            bytes=len(b),sha256=sha(b),git_blob_sha1=blob(b),
            consuming_module='ImbalancedChen.P2OriginalSixthLogArchive' if r in g7 else 'ImbalancedChen.P2OriginalLaterSixthArchive',
            origin=dict(kind='release_member',member=hits[0]),source_authority=str(g7_path if r in g7 else later_path)))

put('DATA_INPUT_DELTA.json',dict(schema='T01_FINE_DENSITY_DATA_INPUT_DELTA_V1',
    official_release_asset=base['release_asset'],
    local_member_inspection_archive=str(archive),
    whole_asset_hash_recomputed=False,whole_asset_hash_authority='Inherited full87 exact release pin; runtime installer must verify whole asset before reading members.',
    old_data_inputs=old_data,old_data_inputs_count=len(old_data),
    old_declared_paths_not_mapped=unmapped_old_paths,
    new_data_inputs=new_data,new_data_inputs_count=len(new_data),
    new_member_bytes_hash_match=True,new_data_certificate_evaluation_performed=False,
    new_uploads_required=False,new_permitted_external_root='../tmp/publication-20261010/verification-renewal-v2/_runs/full-final/',
    exact_external_destination_list=[r['install_path'] for r in new_data],
    byte_reuse_not_proof=True,
    note='FourthRawTableMetadata.wireFile is a provenance string, not a new IO reader. Existing original fourth binary read remains pinned through the inherited source/input map.'))

trees=read(R/'docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/repairs/PINNED_EXTERNAL_TREES.json')
added=sorted(set(graph['external_imports'])-set(base['active_external_direct_imports']))
mathlib=next(t for t in trees if t['package']=='mathlib')
new_external=[]
for name in added:
    p=name.replace('.','/')+'.lean'
    matches=[r for r in mathlib['files'] if r['path']==p]
    assert len(matches)==1,(name,matches)
    new_external.append(dict(module=name,package='mathlib',revision=mathlib['ref'],**matches[0]))
put('EXTERNAL_IMPORT_DELTA.json',dict(schema='T01_FINE_DENSITY_EXTERNAL_IMPORT_DELTA_V1',
    prior_direct_external_count=len(base['active_external_direct_imports']),new_direct_external_count=len(graph['external_imports']),
    new_external_imports=new_external,prior_imports_removed=sorted(set(base['active_external_direct_imports'])-set(graph['external_imports'])),
    native_overlay=receipt(P/'NATIVE_RESEARCH_OVERLAY.json'),native_source_gate=receipt(P/'stage_native_research_overlay_v3.py'),
    native_43_acceptance=receipt(P/'NATIVE_ACCEPTANCE_REQUIREMENTS.json'),
    native_revision=base['native_rev'],new_native_imports=[],
    scope='Only one new external module name. Existing native43 research-to-canonical overlay is unchanged; original external package source remains at its locked repository/revision, not a new upload. Actual setup/import/native ABI verification is still mandatory.'))

source_identity=sha(json.dumps([[n,rows[n]['sha256']] for n in sorted(rows)],separators=(',',':'),ensure_ascii=True).encode())
required_theorems=[
 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity.exists_fine_same_rho_hdensity',
 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity.upper_lt_currentK',
 'ImbalancedChen.P4AOriginalFiniteAll22FineCofinalCoefficient.exists_fine_cofinal_same_coefficient_density_and_count',
 'ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.exists_cofinal_same_coefficient_density_and_count',
 'ImbalancedChen.P4AOriginalEarlyFinitePayment.cofinal_actual_early_defect',
 'ImbalancedChen.p4aActualPresieveCorrection_nonneg']
required_definitions=[
 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity.modulusFamily',
 'ImbalancedChen.P4AOriginalFiniteAll22FineDensity.coefficientFamily',
 'ImbalancedChen.P4AOriginalFiniteAll22CofinalCoefficient.upper',
 'ImbalancedChen.P4AOriginalFiniteFallbackPolicy.F',
 'ImbalancedChen.P4AOriginalFiniteFallbackPolicy.rho',
 'ImbalancedChen.physicalDensitySum',
 'ImbalancedChen.realPhysicalDistributionError']
decl_modules={n:n.rsplit('.',1)[0] for n in required_theorems+required_definitions}
decl_modules['ImbalancedChen.p4aActualPresieveCorrection_nonneg']='ImbalancedChen.P4AHistoricalPhysicalSavingsReserve'
decl_modules['ImbalancedChen.physicalDensitySum']='ImbalancedChen.PhysicalUpperWeightBridge'
decl_modules['ImbalancedChen.realPhysicalDistributionError']='ImbalancedChen.FiniteUpperCarrierCore'
floor_audit=R/'docs/source-only/20261110-yellow-closure-10t/t01_remote_fifth_kernel/T01Audit-v3.lean'
put('TARGET_AUDIT_REQUIREMENTS.json',dict(schema='T01_FINE_DENSITY_TARGET_AUDIT_REQUIREMENTS_V1',
    primary_module=graph['target'],primary_terminal=required_theorems[0],source_identity_sha256=source_identity,
    source_identity_recipe="hashlib.sha256(json.dumps([[module, selected[module]['sha256']] for module in sorted(selected)], ensure_ascii=True, separators=(',', ':')).encode('utf-8')).hexdigest()",
    required_unelided_theorem_types=required_theorems,required_unelided_definitions=required_definitions,
    required_preserved_obligations=['single q after a with 256 divisibility and mesh lower bound','one beta/k and all five fine precision inequalities','delta-constant same Q/rho and common pre-N threshold','actual compilerReserve expense exactly once','same signed realPhysicalDistributionError plus ceil(z),T+1','actual 599/1000 strict support','positive actual correction supplier with unchanged w<=z premise'],
    allowed_standard_axioms=['propext','Classical.choice','Quot.sound'],
    fresh_project_kernel_modules=[r['module'] for r in graph['modules']],
    fresh_project_kernel_modules_count=len(rows),
    audit_module_pending_root_adapter=True,
    kernel_gate='Replay each actual mathematical supplier module, plus any new audit module; a run_cmd/#print-only wrapper replay is not supplier replay.',
    inventory_gate='Retain strict equality of full serialized declaration/defining-module inventory and complete transitive-axiom census. A mismatch fails; no skip/allowlist relaxation. P2 102 is diagnostic only for its own exact source environment.',
    raw_audit_gate='After Lake build, separately run the exact audit through lake env lean and retain raw unprefixed untruncated output; do not parse Lake info-prefixed logs as exact markers.',
    build_command_proposal=['lake','build',graph['target']],
    default_T01_audit_not_retargeted=True,expanded_types_observed=False,kernel_executed=False,
    required_declared_module_and_source_binding=[dict(name=n,defining_module=m,source_sha256=rows[m]['sha256']) for n,m in decl_modules.items()],
    retained_original_floor_audit=dict(path=str(floor_audit),module='T01Audit',sha256=sha(floor_audit.read_bytes()),nine_original_type_gates_preserved=True,imports_already_in_mathematical_closure=True,not_math_supplier_replay=True)))

shared=read(H/'P2_SHARED_SOURCE_CENSUS.json')
put('RUNTIME_AND_TOOL_REUSE.json',dict(schema='T01_FINE_DENSITY_RUNTIME_AND_TOOL_REUSE_V1',
    runtime=dict(toolchain=base['toolchain'],mathlib=base['mathlib_rev'],goldbach=base['native_rev'],trust=0,source_threads=2,source_memory_MiB=12288,moreLeanArgs=base['source_elaboration_resource_options']['moreLeanArgs']),
    configuration=base['configuration'],inherited_project_lakefile=base['inherited_T01']['project_lakefile'],
    source_installer=receipt(P/'stage_project_full87_v3.py'),source_gate=receipt(P/'verify_staged_sources_v3.py'),
    inherited_runtime_adaptation_plan=receipt(P/'INHERITED_TOOL_ADAPTATIONS.json'),
    alternate_existing_simple_installer=receipt(B/'output/resume-20261112/p2-validation-v2/reused/stage_p4.py'),
    P2_102_driver_not_reimplemented=True,P2_shared_modules=len(shared['overlap']),P2_equal_source_count=sum(r['same_source_bytes'] for r in shared['overlap']),
    P2_different_source_count=sum(not r['same_source_bytes'] for r in shared['overlap']),
    existing_CI_inventory=receipt(B/'output/resume-20261112/ci/REPORT.md'),
    accepted_object_cache=[],potential729_not_accepted=True,
    existing_artifact_use='Root first binds immutable existing CI artifact and exact module source/data/runtime/setup/import/native-facet provenance. Only independently verified coherent matching outputs may be restored; propagate mismatch to dependants and retain fresh kernel/type/axiom gates.',
    runtime_adapters_implemented_by_this_packet=False,installer_executed=False,guard_executed=False))
print(json.dumps(dict(project_modules=len(rows),source_identity_sha256=source_identity,old_data_inputs=len(old_data),unmapped_old_paths=unmapped_old_paths,new_release_members=len(new_data),new_external_imports=len(new_external),P2_shared=len(shared['overlap']),P2_equal=sum(r['same_source_bytes'] for r in shared['overlap']),P2_different=sum(not r['same_source_bytes'] for r in shared['overlap'])),indent=2))
