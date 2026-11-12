"""Metadata-only static checks and noncircular freeze; never imports a candidate gate."""
from pathlib import Path
import ast,hashlib,json,tomllib
HERE=Path(__file__).resolve().parent
RES=HERE.parents[1]
def load(p):return json.loads(p.read_text(encoding='utf-8'))
def dump(n,j):(HERE/n).write_text(json.dumps(j,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def desc(p):
 b=p.read_bytes();return {'path':p.relative_to(HERE).as_posix(),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}
m=load(HERE/'Y18_MANIFEST.json');g=load(HERE/'ACTUAL_IMPORT_GRAPH.json');n=load(HERE/'NATIVE_SOURCE_SELECTION.json')
assert len(m['files'])==len(set(m['project_modules']))==337
assert len(m['native_sources'])==460 and len(m['all_native_sources'])==1348 and len(m['standard_native_modules'])==888
assert len(m['mathematical_modules'])==797 and len(m['fresh_kernel_modules'])==798
assert m['fresh_kernel_modules']==m['mathematical_modules']+['CandidateAudit']
assert len(m['target_declarations'])==17 and len(n['shadow_variants'])==61 and len(n['bare_module_libraries'])==7
assert len(g['actual_combined_dependency_order'])==1685
assert not m['data_inputs'] and not n['data_read_source_mentions']
choices=RES/'t16-empty-review/y18-validation/NATIVE_SOURCE_CHOICES.json'
assert hashlib.sha256(choices.read_bytes()).hexdigest()=='6b03ea13ee1de8f092d1789e4b5987015bb74073a91c290bd0601435c37f2d03'
m['native_source_choice_authority']={'path':str(choices),'bytes':choices.stat().st_size,'sha256':hashlib.sha256(choices.read_bytes()).hexdigest(),'status':'Original producers and actual direct consumer APIs checked; all61 different alternate blobs retained. No historical ABI claim.'}
(HERE/'reused/NATIVE_SOURCE_CHOICES.json').write_bytes(choices.read_bytes())
m['native_source_choice_authority']['path']='reused/NATIVE_SOURCE_CHOICES.json'
files=sorted(p for p in HERE.rglob('*') if p.is_file() and p.name not in {'Y18_MANIFEST.json','REGISTRY.json','ALLOWLIST.json','REPORT.md','STATIC_CHECKS.json'})
assert not any('__pycache__' in p.parts or p.suffix=='.pyc' for p in files)
m['support_files']=[desc(p) for p in files]
dump('Y18_MANIFEST.json',m)
asts=[];tomls=[];jsons=[]
for p in sorted(HERE.rglob('*')):
 if not p.is_file():continue
 if p.suffix=='.py':ast.parse(p.read_text(encoding='utf-8'),filename=str(p));asts.append(p.relative_to(HERE).as_posix())
 elif p.suffix=='.toml':tomllib.loads(p.read_text(encoding='utf-8'));tomls.append(p.name)
 elif p.suffix=='.json' and p.name not in {'REGISTRY.json','ALLOWLIST.json'}:load(p);jsons.append(p.name)
audit=(HERE/'CandidateAudit.lean').read_text(encoding='utf-8')
strict=['unless owned.qsort Name.lt == data.constNames.qsort Name.lt do','P0_ROUND6_INVENTORY_MISMATCH','Serialized declarations and defining-module inventory differ','(← IO.getStdout).flush','Unsafe declaration','Partial declaration','Unproved axiom declaration','Forbidden transitive axiom','pp.all true','pp.proofs true','pp.deepTerms true']
assert all(x in audit for x in strict)
assert audit.count('#print axioms ')==17
assert not any('StoredBlock' in r['module'] or 'P5SubdivisionStoredParentTypes' in r['module'] for r in m['files'])
assert not any(r.get('selection','')=='UNRESOLVED' for r in m['files'])
profile=tomllib.loads((HERE/'project-lakefile.toml').read_text(encoding='utf-8'))
assert profile['moreLeanArgs']==['-DmaxRecDepth=100000','-DmaxHeartbeats=4000000']
bind=(HERE/'bind_compile_receipts_y18.py').read_text(encoding='utf-8')
assert 'for name, arrays in arts.items():' in bind and 'selected_output_parts' in bind and 'expected_definition_options' in bind
consume=(HERE/'consume_y18.py').read_text(encoding='utf-8')
assert 'subprocess.run(command,env=os.environ.copy(),check=False)' in consume and "selected_public_objects" in consume and "actual LEAN_PATH" in consume
checks={'status':'STATIC_SOURCE_JSON_TOML_AST_AND_GRAPH_CHECKS_ONLY','project':337,'native_research':460,'native_standard':888,'full_native':1348,'combined_source_graph':1685,'strict_math':797,'actual_fresh_checker_required':798,'target17':17,'shadow61':61,'bare_libraries7':7,'project_List_hunks13':13,'project_List_postimage_files12':12,'Fine_project_same_source232':232,'Fine_project_union1921':1921,'P2_same_source28':28,'acceptedStored32_overlap':0,'AST_checked_python_files':asts,'TOML_checked_files':tomls,'JSON_checked_files':jsons,'FinitePi_strict_gate_and_diagnostic_preserved':True,'all_selected_setup_consumed_facets_join_canonical':True,'same_env_final_consumers_require_actual_resolver_receipts':True,'full_project_root_loadable_census':True,'all_pinned_native_source_data_mentions':0,'unrelated_data_or_floor_imports_added':False,'new_workflow_or_external_driver_written':False,'stage_or_Lake_or_Lean_or_guard_executed':False,'compiled':False,'kernel_verified':False,'driver_ready':False}
dump('STATIC_CHECKS.json',checks)
report='''This is an isolated, static Y18 validation candidate. It reuses the existing P2v3 strict audit/runtime protocol and the Fine coherent checkpoint collector. No driver/workflow, stage, installer, Lean, Lake, checker, guard, producer, CI, Git mutation or remote write was run. driver_ready=false.

The actual target graph contains337 project modules:335 exact historical dependencies plus the two published Y18 sources. The 13 reviewed List API edits affect12 selected postimages. All26 historical-only paths are explicitly pinned to f1bcf37b; the two targets come from794fe55a. The graph intersects FineWinner1816 in232 identical selected bytes and P2r2 in28 identical selected bytes. Merging with Fine adds105 project modules, producing1921. No accepted Stored32 source is reached, and no accepted coherent Y18 project cache is available. Source equality is not object or ABI acceptance.

The full09b native source closure is1348:460 research-only source-copy overlays and888 canonical standard package inputs. All61 alternate research blobs are recorded; canonical/default selection follows the original native library roots, with original producer pins and both differing direct consumer APIs independently checked by T16. No research override is guessed. Runtime setup, actual compiler paths and consumed facets must prove the selected canonical objects were used. Seven bare SecondFunctionalUnit modules receive exact new library/glob registrations; the original four libraries, dependency pins, default targets and native flags stay intact. Architect is already in the unchanged lock. There are no data-read/include mentions in the337 project or1348 selected native texts; no original release bytes or numerical work are re-created.

The strict declaration census and mathematical replay scope is337+460=797; the actually compiled CandidateAudit wrapper adds one separate kernel module, for798. The888 standard native dependencies must have exact source/config/setup/import/artifact and guarded-build provenance, including real coherent output facets; they are not claimed individually declaration-audited. Pure reexports are not misrepresented as positive mathematical declaration counts. All17 original leaf theorems have exact names, kinds and owners, full readable/expanded types, collectAxioms and independent #print axioms. No Fine nine-floor import is added.

FinitePiIntegral is a true needed input, SHA22c7e16d66361c4aec2913237c8b8866db59575d36c50416805094e351f5c54c, matching the old real strict serialized-versus-owner failure. The original multiset comparison, diagnostic JSON, stdout flush and rejection remain. This candidate does not presume that failure is resolved; root must supply any currentP2/R3 repair decision and explicitly repin a reviewed shared source before deployment. The four existing P2r2 repaired modules are absent from Y18.

The project compiler profile explicitly matches Fine's -DmaxRecDepth=100000/-DmaxHeartbeats=4000000. Native code inherits its original empty moreLeanArgs. The wrapper passes its options independently. The original trust0/two-thread/12GiB serial guard remains byte-for-byte. The generic P4 stage differs only in the explicit project lakefile blob. Runtime/ABI/source/setup/flags joins are retained and extended across all1348 native producers. Every selected direct or transitive setup artifact must join the corresponding canonical module and facet. The final wrapper/checker/audit launchers record actual ordered LEAN_PATH in the same environment and cwd, bind the first existing public objects to those canonical outputs, SHA-bind the actual absolute guard/runtime executables to the retained pinned state, run the original tools, and check the consumed objects and tools again afterwards. All three actual consumer receipts then join the final checkpoint by module/path/hash/size. No unreviewed cache alias is allowed.

P2's old object-only archive is insufficient for a later Fine cache. The reused Fine collector retains actual ilean/setup/IR/C/o/link/library/trace facets when produced, raw failure bytes and the immediate path/hash journal. No missing facet is synthesized and no restore is authorized. Source roots and full native choices are checked both before and after compilation; the entire project-root loadable census rejects bare-name shadows. A separately reviewed root driver must bind the actual immutable external selection and committed workflow inventory, preserve the shared concurrency group and all always-retention semantics, then pass every gate. Those driver/CI steps and T16's independent candidate review remain pending. Acceptance, if later earned, covers the actual Y18 targets/input scope only; PP, whole parts, hUpper and K are not completed by this packet.
'''
(HERE/'REPORT.md').write_text(report,encoding='utf-8',newline='\n')
records=[desc(p) for p in sorted(HERE.rglob('*')) if p.is_file() and p.name not in {'REGISTRY.json','ALLOWLIST.json'}]
dump('REGISTRY.json',{'schema':'Y18_VALIDATION_CANDIDATE_REGISTRY_V1','status':'STATIC_CONFIG_FROZEN_FOR_INDEPENDENT_REVIEW','files':records,'manifest_sha256':hashlib.sha256((HERE/'Y18_MANIFEST.json').read_bytes()).hexdigest(),'strict_math797':True,'fresh_kernel798':True,'target17':True,'driver_ready':False,'compiled':False,'kernel_verified':False,'coherent_cache_accepted':False,'all_original_frozen_packets_unchanged':True})
dump('ALLOWLIST.json',{'schema':'Y18_VALIDATION_CANDIDATE_AUTHOR_ALLOWLIST_V1','status':'CANDIDATE_SOURCE_ONLY_NOT_ROOT_DRIVER_APPROVAL','files':records+[desc(HERE/'REGISTRY.json')],'no_author_self_hash_cycle':True})
print(json.dumps({'manifest':desc(HERE/'Y18_MANIFEST.json'),'registry':desc(HERE/'REGISTRY.json'),'report':desc(HERE/'REPORT.md'),'allowlist':desc(HERE/'ALLOWLIST.json'),'files':len(records),'driver_ready':False},indent=2))
