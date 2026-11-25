from pathlib import Path
import hashlib,json,re,difflib
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'ImbalancedChen'
SOURCES=Path('/workspace/p26-source-closure')
V2=Path('/workspace/p26-recovery-candidates/archive-v2/ImbalancedChen')
PACK=Path('/workspace/p26-recovery-candidates/archive-packed-chars')
BRIDGE=Path('/workspace/p26-recovery-candidates/archive-char-input')
METADATA=SOURCES/'docs/verification/20261125-p26/ORIGINAL_INPUT_SCALE.json'
NS='ImbalancedChen.P2OriginalSaving19Archive'
PN='ImbalancedChen.P2OriginalSaving19PackedChars'
PREFIX='P2OriginalSaving19'

def sha(b):return hashlib.sha256(b).hexdigest()
def fp(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b)}
def emit(rel,body):
 p=ROOT/rel;b=body.encode() if isinstance(body,str) else body
 if p.exists():assert p.read_bytes()==b, f'Do not silently overwrite changed candidate: {p}'
 else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return fp(p)

pins={
 'PackedChars':(PACK/'ImbalancedChen/P2OriginalSaving19PackedChars.lean','cf65b9e0f3b0a4735cdb962d9b317ed29e8f39c8507647bab04f7e48800ad001'),
 'CharInputBridge':(BRIDGE/'ImbalancedChen/P2OriginalSaving19CharInputBridge.lean','18d5e23b30fd7333bb2b3a80c4bedae0ff4f8e190b45833c390a6cbffc1bba21'),
 'SourceJsonCharInput':(BRIDGE/'ImbalancedChen/P2OriginalSaving19SourceJsonCharInput.lean','64c20a58a005b83aec402c9b1e65e570fdcbe35fb9530be1220596679da97396'),
 'SourceJson':(BRIDGE/'local/reader-source/ImbalancedChen/P2OriginalSaving19SourceJson.lean','ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424')}
for key,(p,h) in pins.items():
 assert sha(p.read_bytes())==h
 emit(f'ImbalancedChen/{PREFIX}{key}.lean',p.read_bytes())
assert sha(METADATA.read_bytes())=='3e022a419c35152589c2c3fb26cb0fe5839c79a348277b0643174b4f078f3954'
metadata=json.loads(METADATA.read_bytes())
assert metadata['original_input_count']==26 and len(metadata['all_inputs'])==26
assert sum(x['bytes'] for x in metadata['all_inputs'])==metadata['total_raw_bytes']==80189086
emit('ORIGINAL_INPUT_SCALE.json',METADATA.read_bytes())

loader='''import ImbalancedChen.P2OriginalSaving19PackedChars

/-!
SOURCE CANDIDATE, NOT COMPILED. Shared raw-input quotation only.
Each data owner supplies one original ../goldbach-research/ path. The loader
reads that complete UTF-8 file via IO.FS.readFile, preserves s.toList in order,
runs the same proved PackedChars.pack, and quotes only the resulting Tree
constructors. It performs no JSON parse, typed decoding, numerical check,
source hash check, truncation, padding, or line-ending normalization.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

open Lean Elab Term
set_option maxRecDepth 1000000

private def quoteOriginalPackedTree : P2OriginalSaving19PackedChars.Tree → Expr
  | .empty => mkConst ``P2OriginalSaving19PackedChars.Tree.empty
  | .leaf n word =>
      mkApp2 (mkConst ``P2OriginalSaving19PackedChars.Tree.leaf) (mkNatLit n) (mkNatLit word)
  | .branch l r =>
      mkApp2 (mkConst ``P2OriginalSaving19PackedChars.Tree.branch)
        (quoteOriginalPackedTree l) (quoteOriginalPackedTree r)

elab "originalPackedText% " p:str : term => do
  let s ← IO.FS.readFile p.getString
  return quoteOriginalPackedTree (P2OriginalSaving19PackedChars.pack s.toList)

end ImbalancedChen.P2OriginalSaving19Archive
'''
emit('ImbalancedChen/P2OriginalSaving19ArchivePackedLoader.lean',loader)
paths=[]
for family in ['geometry','moment']:
 for cell in range(13):
  suffix=f'{cell:02}'
  filename=(f'eighth-third-minorant-extension-20261009-a23-s23_low-{suffix}-cell.witness.json'
   if family=='geometry' else f'eighth-third-moment-refinement-20261009-a23-low-{suffix}.witness.json')
  original='../goldbach-research/'+filename
  matching=[x for x in metadata['all_inputs'] if x['family']==family and x['cell']==cell]
  assert len(matching)==1
  m=matching[0]
  assert m['loader_relative_path']==original
  assert m['loader_absolute_path']==m['resolved_actual_path']=='/workspace/goldbach-research/'+filename
  module=f'{PREFIX}Archive{family.title()}Data{suffix}'
  name=f'{family}Packed{suffix}'
  body=f'''import ImbalancedChen.P2OriginalSaving19ArchivePackedLoader

/-! SOURCE CANDIDATE, NOT COMPILED. Exactly one complete original input;
no parse, decode, shape, numerical, or success assertion is made here. -/
namespace {NS}
set_option maxRecDepth 1000000

noncomputable def {name} : P2OriginalSaving19PackedChars.Tree :=
  originalPackedText% "{original}"

end {NS}
'''
  info=emit('ImbalancedChen/'+module+'.lean',body)
  paths.append({**m,'module':'ImbalancedChen.'+module,'relative_source':'ImbalancedChen/'+module+'.lean','definition':NS+'.'+name,'candidate_source':info,'full_UTF8_read':True,'expected_byte_count_is_not_codepoint_count':True,'raw_payload_read_by_generator':False})
emit('INPUT_PATHS.json',json.dumps({'schema':'saving19_archive_v4_exact_original_paths_v1','metadata_preimage':fp(METADATA),'source_evidence':{k:metadata[k] for k in ['source_artifact','source_artifact_sha256','source_member']},'total_bytes':metadata['total_raw_bytes'],'paths':paths},indent=2)+'\n')
# Remaining maps/Core/facade and provenance are generated below after the first
# stable loader/data batch has been made available for read-only review.
print(json.dumps({'stable_loader':fp(SRC/'P2OriginalSaving19ArchivePackedLoader.lean'),'first_data_owners':[p for p in paths if (p['family'],p['cell']) in [('geometry',0),('geometry',12),('moment',12)]],'data_owners_generated':len(paths)},indent=2))

imports=''.join('import '+p['module']+'\n' for p in paths)
inputs=imports+'''
/-! SOURCE CANDIDATE, NOT COMPILED. Fin 13 input maps only. Fin.cases gives
exactly thirteen ordered entries and an impossible Fin 0 tail, with no default
cell or dropped source fields. This module performs no file I/O itself. -/
namespace ImbalancedChen.P2OriginalSaving19Archive

'''
for family in ['geometry','moment']:
 names=[f'{family}Packed{i:02}' for i in range(13)]
 expr='Fin.elim0'
 for name in reversed(names):expr=f'Fin.cases {name} ({expr})'
 # Formatting changes only whitespace; the nested complete Fin map has no
 # out-of-range fallback or duplicated last-cell entry.
 inputs+=f'noncomputable def {family}Packed : Fin 13 → P2OriginalSaving19PackedChars.Tree :=\n  {expr}\n\n'
 inputs+=f'noncomputable def {family}Chars (c : Fin 13) : List Char :=\n  ({family}Packed c).toList\n\n'
inputs+=f'end {NS}\n'
emit('ImbalancedChen/P2OriginalSaving19ArchivePackedInputs.lean',inputs)

oldcore=(V2/'P2OriginalSaving19ArchiveCore.lean').read_bytes()
oldarchive=(V2/'P2OriginalSaving19Archive.lean').read_bytes()
assert sha(oldcore)=='df9c1855bb3b97c8191390a3310f041e5f46c0fb1f4a0349011d5689a5435182'
assert sha(oldarchive)=='f48ba6e6522a3a76bd81ef1be15875563163a4df6e7891c1422b6562ee31ed49'
emit('preimages/P2OriginalSaving19ArchiveCore.v2.lean',oldcore)
emit('preimages/P2OriginalSaving19Archive.v2.lean',oldarchive)
oldtext=oldcore.decode();oldfull=oldarchive.decode()
start=oldtext.index('def parseInteger ')
stop=oldtext.index('def geometryParse ')
schema=oldtext[start:stop]
getter_end=oldtext.index('\n\n/-!\nDIAGNOSTIC CANDIDATE ONLY.',stop)
getters=oldtext[stop:getter_end]
newgetters=getters
for name in ['geometryParse','momentParse','geometry','moments']:
 oldhead=f'def {name} ('
 assert newgetters.count(oldhead)==1
 newgetters=newgetters.replace(oldhead,'noncomputable '+oldhead)
assert newgetters.replace('noncomputable def ','def ')==getters

core='''import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import ImbalancedChen.P2OriginalSaving19SourceJson
import ImbalancedChen.P2OriginalSaving19ArchivePackedInputs
import ImbalancedChen.P2OriginalSaving19SourceJsonCharInput

/-!
SOURCE CANDIDATE, NOT COMPILED OR ACCEPTED. New input representation, requiring
fresh Core acceptance. The old v2 Core object/export acceptance is not reused.
All 26 original files are quoted separately by their data owners; Core only
assembles already quoted complete characters. SourceJson.parse and every typed
schema/decoder below retain the v2 source bodies. The new parse_ofList bridges
preserve the entire parser result; they assert no concrete parse success.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

set_option maxRecDepth 1000000

noncomputable def geometryText : Fin 13 → String :=
  fun c => String.ofList (geometryChars c)

noncomputable def momentText : Fin 13 → String :=
  fun c => String.ofList (momentChars c)

'''+schema+newgetters+'''

/-- Exact input-representation bridge, including unchanged typed decoding.
This does not discharge a parse-success, shape, or numerical obligation. -/
theorem geometryParse_eq_parseChars (c : Fin 13) :
    geometryParse c = (SourceJson.parseChars (geometryChars c) >>= decodeGeometry) :=
  congrArg (fun result => result >>= decodeGeometry)
    (SourceJson.parse_ofList (geometryChars c))

theorem momentParse_eq_parseChars (c : Fin 13) :
    momentParse c = (SourceJson.parseChars (momentChars c) >>= decodeMoments) :=
  congrArg (fun result => result >>= decodeMoments)
    (SourceJson.parse_ofList (momentChars c))

end ImbalancedChen.P2OriginalSaving19Archive
'''
emit('ImbalancedChen/P2OriginalSaving19ArchiveCore.lean',core)
assert core[core.index('def parseInteger '):core.index('noncomputable def geometryParse ')]==schema

# The complete old post-Core obligation source is retained as a facade. No
# theorem statements or proof bodies are changed, assumed, or replaced by data.
anchor='/-- Closed pure kernel checks, deliberately NOT run in this source task.'
tail=oldfull[oldfull.index(anchor):]
newtail=tail
noncomp_facade=[]
for name in ['rawGeometryRow','rawMomentRow','rawVertex']:
 needle=f'def {name} ('
 assert newtail.count(needle)==1
 newtail=newtail.replace(needle,'noncomputable '+needle)
 noncomp_facade.append(name)
for needle in [
 'instance (c : Fin 13) : Decidable (CellShape c) :=',
 'instance (r : OriginalRowIndex) : Decidable (RowShape r) :=']:
 assert newtail.count(needle)==1
 newtail=newtail.replace(needle,'noncomputable '+needle)
 noncomp_facade.append(needle)
assert newtail.replace('noncomputable def ','def ').replace('noncomputable instance ','instance ')==tail
facade='''import ImbalancedChen.P2OriginalSaving19ArchiveCore

/-!
SOURCE CANDIDATE, NOT COMPILED OR ACCEPTED. This facade retains all original
parse-success, cell-shape, row-shape, row-id and row-count obligations. Their
statements and proof bodies are unchanged. Only runtime definitions/Decidable
instances depending on the new noncomputable input are marked noncomputable.
No successful v4 Archive or downstream numerical acceptance is claimed.
-/
namespace ImbalancedChen.P2OriginalSaving19Archive

set_option maxRecDepth 1000000

'''+newtail
emit('ImbalancedChen/P2OriginalSaving19Archive.lean',facade)

# Exact migration diff: old Core to new Core, old monolithic Archive to its
# obligation facade, plus the original sources of byte-identical helpers.
diffs=[]
for name,before,after in [('P2OriginalSaving19ArchiveCore.lean',oldtext,core),('P2OriginalSaving19Archive.lean',oldfull,facade)]:
 diffs.extend(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/ImbalancedChen/'+name,tofile='b/ImbalancedChen/'+name))
emit('MIGRATION.patch',''.join(diffs))

source_declarations=[]
for name in re.findall(r'^(?:noncomputable )?(?:def|theorem|structure)\s+(\S+)',oldfull,re.M):
 source_declarations.append(name)
combined=core+'\n'+facade
missing=[];duplicates=[]
for name in source_declarations:
 n=len(re.findall(r'^(?:noncomputable )?(?:def|theorem|structure)\s+'+re.escape(name)+r'(?=\s|\()',combined,re.M))
 if n==0:missing.append(name)
 if n>1:duplicates.append(name)
assert not missing and not duplicates
for p in SRC.glob('*.lean'):
 assert not re.search(r'\b(sorry|admit|native_decide|unsafe)\b|^\s*axiom\b',p.read_text(),re.M),p

semantic={
 'v2_core_preimage':fp(V2/'P2OriginalSaving19ArchiveCore.lean'),
 'v2_archive_preimage':fp(V2/'P2OriginalSaving19Archive.lean'),
 'schema_decoder_slice':{'old_start_byte':len(oldtext[:start].encode()),'old_end_byte_exclusive':len(oldtext[:stop].encode()),'bytes':len(schema.encode()),'sha256':sha(schema.encode()),'new_bytes_identical':True,'first_declaration':'parseInteger','last_declaration':'decodeMoments'},
 'four_typed_getter_definitions':{'names':['geometryParse','momentParse','geometry','moments'],'original_bodies_and_declared_types_preserved':True,'only_change':'noncomputable prefix','old_slice_sha256':sha(getters.encode()),'normalized_new_slice_sha256':sha(newgetters.replace('noncomputable def ','def ').encode())},
 'facade':{'original_post_core_slice_sha256':sha(tail.encode()),'normalized_new_slice_sha256':sha(newtail.replace('noncomputable def ','def ').replace('noncomputable instance ','instance ').encode()),'only_noncomputable_additions':noncomp_facade,'all_theorem_statements_and_bodies_byte_preserved':True},
 'all_original_named_declarations_retained_once':source_declarations,
 'declaration_missing':missing,'declaration_duplicates':duplicates,
 'original_input_elaborators_replaced':{'names':['originalGeometryText%','originalMomentText%'],'reason':'Input-only read+String-literal elaborators replaced by one full-character packed quote loader and 26 owners. No other repository use was found in the inspected project tree.'},
 'new_input_maps':'Fin.cases over exactly 13 ordered owner declarations, terminating in Fin.elim0; no default fallback cell',
 'new_core_bridges':['geometryParse_eq_parseChars','momentParse_eq_parseChars'],
 'core_imports_old_core':False,'closed_success_obligations_proved':False,'getD_fallback_eliminated':False,'all26_input_data_compiled':False,'production_modified':False,'compilation_run':False,'remote_jobs_started':False,
 'forbidden_tokens_present':False}
emit('SEMANTIC_DIFF.json',json.dumps(semantic,indent=2)+'\n')

# Static source import closure. Project sources are read only for exact import
# and SHA provenance; no compiler/build, external package or witness is run.
def direct_imports(p):
 out=[]
 for line in p.read_text().splitlines():
  m=re.match(r'^(?:public |private )?import\s+(.+)$',line)
  if m:
   out.extend(t for t in m[1].split() if not t.startswith('--'))
 return out

def source_for(module):
 relative=module.replace('.','/')+'.lean'
 for base in [ROOT,SOURCES]:
  p=base/relative
  if p.is_file():return p
 return None

closure_cache={}
def closure(root):
 if root in closure_cache:return closure_cache[root]
 seen={};external=set();missing=[]
 def go(m):
  if not m.startswith('ImbalancedChen.'):
   external.add(m);return
  if m in seen:return
  p=source_for(m)
  if p is None:
   missing.append(m);return
  ds=direct_imports(p)
  seen[m]={'source':fp(p),'direct_imports':ds,'candidate_owned':p.is_relative_to(ROOT)}
  for d in ds:go(d)
 go(root)
 value={'root':root,'project_module_count_including_root':len(seen),'candidate_module_count':sum(x['candidate_owned'] for x in seen.values()),'external_import_roots':sorted(external),'missing_project_sources':sorted(set(missing)),'modules':seen}
 closure_cache[root]=value
 return value

roots=['ImbalancedChen.P2OriginalSaving19ArchiveGeometryData00','ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12','ImbalancedChen.P2OriginalSaving19ArchiveMomentData12','ImbalancedChen.P2OriginalSaving19ArchivePackedInputs','ImbalancedChen.P2OriginalSaving19ArchiveCore','ImbalancedChen.P2OriginalSaving19Archive']
closures={r:closure(r) for r in roots}
assert all(not x['missing_project_sources'] for x in closures.values())
input_closure=closures[roots[3]]
assert len([m for m in input_closure['modules'] if re.fullmatch(r'ImbalancedChen.P2OriginalSaving19Archive(Geometry|Moment)Data\d\d',m)])==26
for r in roots[:3]:
 assert closures[r]['project_module_count_including_root']==3
 assert closures[r]['external_import_roots']==['Lean']
# Topological candidate-only source order. Existing accepted suppliers are
# referenced as provenance; this list never requests their optional rebuild.
visited=set();order=[]
def topo(m):
 if m in visited:return
 visited.add(m);p=source_for(m)
 if p is None:return
 for d in direct_imports(p):
  if d.startswith('ImbalancedChen.'):topo(d)
 if p.is_relative_to(ROOT):order.append(m)
topo('ImbalancedChen.P2OriginalSaving19Archive')
emit('SOURCE_CLOSURE.json',json.dumps({'schema':'saving19_archive_v4_static_source_import_closure_v1','project_reference_root':str(SOURCES),'project_reference_commit':'e3824f6d30f5ce193c8aa86a725bfb77d941d5d7','counts_are_static_not_compiled_acceptance':True,'roots':closures,'candidate_topological_order':order},indent=2)+'\n')

prior_objects={
 'PackedChars':PACK/'objects/ImbalancedChen/P2OriginalSaving19PackedChars.olean',
 'CharInputBridge':BRIDGE/'local/lib/lean/ImbalancedChen/P2OriginalSaving19CharInputBridge.olean',
 'SourceJsonCharInput':BRIDGE/'local/lib/lean/ImbalancedChen/P2OriginalSaving19SourceJsonCharInput.olean',
 'SourceJson':BRIDGE/'local/lib/lean/ImbalancedChen/P2OriginalSaving19SourceJson.olean'}
reused=[]
for k,(p,h) in pins.items():
 reused.append({'module':'ImbalancedChen.'+PREFIX+k,'source':fp(p),'candidate_source':fp(SRC/(PREFIX+k+'.lean')),'source_bytes_identical':True,'existing_local_object':fp(prior_objects[k]),'existing_local_evidence':str(PACK/'RESULT.json') if k=='PackedChars' else str(BRIDGE/'local'/('DIAGNOSTIC.json' if k=='CharInputBridge' else 'COMPANION_DIAGNOSTIC.json')),'object_copied_into_candidate':False,'reuse_conditions':'Same module/FQN, exact source and import fingerprints and toolchain; root must apply its actual strict-reuse policy. Prior local receipts are not a v4 full-closure strict receipt.'})
allmods=sorted('ImbalancedChen.'+p.stem for p in SRC.glob('*.lean'))
newmods=[m for m in allmods if m not in [r['module'] for r in reused]]
obligations=[
 {'name':'geometry_parse_success','statement':'∀ c, geometryParse c = .ok (geometry c)','scope':'all 13 geometry files','status':'original statement/proof retained in uncompiled facade; not discharged'},
 {'name':'moments_parse_success','statement':'∀ c, momentParse c = .ok (moments c)','scope':'all 13 moment files','status':'original statement/proof retained in uncompiled facade; not discharged'},
 {'name':'original_cell_shapes','statement':'∀ c, CellShape c','scope':'dimensions, Jacobian, row counts, source witness names, factor counts, degrees, Q80/Q96 denominators','status':'original statement/proof retained; not discharged'},
 {'name':'original_row_shapes','statement':'∀ r, RowShape r','scope':'all 28918 rows; exact IDs, nine distinct vertices and bounds, ten factors/floors','status':'original statement/proof retained; not discharged'},
 {'name':'downstream numerical / ownership / integral endpoints','statement':'unchanged downstream sources continue to import the facade API','scope':'Original28918 / FloorBinding / OwnedSource / PullingOwnership / OwnedIntegral / ActualEndpoint','status':'no new acceptance or transferred object credit from this source preparation'}]
emit('ACCEPTANCE_PLAN.json',json.dumps({'schema':'saving19_archive_v4_acceptance_boundary_v1','status':'SOURCE_ONLY_UNCOMPILED','byte_identical_source_reuse':reused,'must_receive_new_acceptance':newmods,'new_core_old_224_exports_credit_transferred':False,'old_core_object_reused':False,'old_archive_object_reused':False,'first_review_compile_candidates':roots[:3],'first_review_dependencies':['ImbalancedChen.P2OriginalSaving19PackedChars','ImbalancedChen.P2OriginalSaving19ArchivePackedLoader'],'full_candidate_topological_order':order,'still_open_semantic_obligations':obligations,'guard_execution_warning':'Retaining original by-decide source is not a claim those whole-file guards will fit resource limits. Do not infer parser success from the new representation alone.','object_copy_performed':False,'compiler_invocations':0,'raw_input_reads_by_generator':0},indent=2)+'\n')
manifest={'schema':'saving19_archive_v4_source_candidates_v1','status':'SOURCE_ONLY_UNCOMPILED','candidate_root':str(ROOT),'core_baseline':fp(V2/'P2OriginalSaving19ArchiveCore.lean'),'archive_baseline':fp(V2/'P2OriginalSaving19Archive.lean'),'metadata_baseline':fp(METADATA),'p1_original_reference_commit':'298670f119d24874b719facb3ef756f1e01223a1','source_closure_reference_commit':'e3824f6d30f5ce193c8aa86a725bfb77d941d5d7','lean_pin':'4.33.0-rc1 / 62eed1db4d67327ec8120be05f1a1b0847d74561','mathlib_pin':'e4c91783ca8e6a7c693ae624ade32fd22d4e43c1','source_module_count':len(allmods),'core_input_layout_module_count_excluding_unchanged_reader_and_obligation_facade':len(allmods)-2,'data_owner_count':26,'candidate_files':[{'module':'ImbalancedChen.'+p.stem,'install_path':'ImbalancedChen/'+p.name,**fp(p)} for p in sorted(SRC.glob('*.lean'))],'same_byte_source_reuse':[x['module'] for x in reused],'new_or_replaced_modules':newmods,'production_changed':False,'compile_invocations':0,'no_actual_raw_payloads_loaded_or_generated':True,'old_core_reimported':False,'archive_complete':False,'only_cell00_proved':False}
emit('SOURCE_MANIFEST.json',json.dumps(manifest,indent=2)+'\n')
print(json.dumps({'total_lean_sources':len(allmods),'core':fp(SRC/'P2OriginalSaving19ArchiveCore.lean'),'facade':fp(SRC/'P2OriginalSaving19Archive.lean'),'schema_decoder_slice':semantic['schema_decoder_slice'],'closures':{r:{k:x[k] for k in ['project_module_count_including_root','candidate_module_count','missing_project_sources']} for r,x in closures.items()},'new_acceptance_module_count':len(newmods)},indent=2))
