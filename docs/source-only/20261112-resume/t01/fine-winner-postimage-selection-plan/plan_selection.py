"""Static text selection only. Never executes prepare/stage/Lean/guards/producers."""
from pathlib import Path
import ast, copy, hashlib, json, re, zipfile
BASE=Path('E:/timot/Documents/FilesForGPT/Myath');HERE=Path(__file__).resolve().parent;REPO=BASE/'goldbach-proof-continuation'
def load(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def dump(n,x):(HERE/n).write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n',encoding='utf-8',newline='\n')
def ident(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b)}
old=BASE/'output/resume-20261112/t01/winner8-fine-identity-plan'
C=load(old/'WINNER8_FINE_CLOSURE_COMPARISON.json');B=load(old/'STORED72_FINE_VS_ACCEPTED20.json');A=load(old/'EXISTING_STORED_ARTIFACT_FACETS.json')
F_PATH=BASE/'output/resume-20261112/t01/density-validation-v2/DENSITY_MANIFEST.json';F=load(F_PATH)
selected={r['module']:copy.deepcopy(r) for r in C['combined_sources']};assert len(selected)==1816
recipe=BASE/'output/resume-20261112/stored-020-030-config/payload/verification/parts/p0/prepare_stored_batch.py'
assert sha(recipe.read_bytes())=='a7a34c273db2cbfe6fb4d5b0809e7b6618044666d50c64233b03832484780ecf'
review=BASE/'output/resume-20261112/t10/STORED_020_030_SCOPED_CONFIG_ALLOWLIST.json'
assert sha(review.read_bytes())=='f980f86f9934d08812d56b24a047f09c00232655b1f93195a6b9a6614d5881e6'

# Extract ONLY the already reviewed generator's pure string/list statements.
# Do not execute its module, prepare branch, file IO, environment reads, audit
# generator, snapshot, verifier or compiler invocation.
tree=ast.parse(recipe.read_text(encoding='utf-8'))
branch=next(n for n in tree.body if isinstance(n,ast.If) and ast.unparse(n.test)=="mode == 'prepare'")
loop=next(n for n in branch.body if isinstance(n,ast.For) and isinstance(n.target,ast.Name) and n.target.id=='block')
pure=[];started=False
for node in loop.body:
 target=node.targets[0].id if isinstance(node,ast.Assign) and isinstance(node.targets[0],ast.Name) else None
 if target=='base':started=True
 if started:pure.append(copy.deepcopy(node))
 if target=='after':break
assert pure and isinstance(pure[-1],ast.Assign) and pure[-1].targets[0].id=='after'
for node in ast.walk(ast.Module(body=pure,type_ignores=[])):
 if isinstance(node,ast.Call):
  if isinstance(node.func,ast.Name):assert node.func.id=='range'
  else:assert isinstance(node.func,ast.Attribute) and node.func.attr in {'count','append','extend','replace','join'}
 if isinstance(node,ast.Name):assert node.id not in {'root','logs','p','receipt','os','sys','pathlib','open','compile','exec','eval'}
fn=ast.FunctionDef(name='generate_full_block_text',args=ast.arguments(posonlyargs=[],args=[ast.arg(arg='before'),ast.arg(arg='block')],kwonlyargs=[],kw_defaults=[],defaults=[]),body=pure+[ast.Return(value=ast.Name(id='after',ctx=ast.Load()))],decorator_list=[])
pure_module=ast.fix_missing_locations(ast.Module(body=[fn],type_ignores=[]));ns={'range':range,'__builtins__':{}}
exec(compile(pure_module,'<reviewed-pure-text-generator>','exec'),ns)
generate_full=ns['generate_full_block_text']
dump('PURE_TEXT_RECIPE_AST.json',{'source':ident(recipe),'source_configuration_review':ident(review),'pure_AST_sha256':sha(ast.dump(pure_module,include_attributes=False).encode()),'pure_AST':ast.dump(pure_module,include_attributes=False,indent=2),'allowed_calls':['range','str.count','list.append','list.extend','str.replace','str.join'],'original_prepare_or_producer_executed':False,'scope':'Full4096-row blocks000-070 only. This evaluates text construction, not any Lean declaration or numerical certificate.'})

def generate_partial(before,block,size):
 assert block==71 and size==1817
 base=4096*block
 old=f'theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = {base} + j.val := by\n  decide'
 assert before.count(old)==1 and 'theorem rows_size : rows.size = 1817 := rfl' in before
 chunks=[]
 for k in range(29):
  width=64 if k<28 else 25;off=64*k
  chunks.append(f'private theorem source_index_chunk_{k} : ∀ j : Fin {width}, (rows[{off} + j.val]\'(by rw [rows_size]; have := j.isLt; omega)).sourceIndex = {base} + ({off} + j.val) := by\n  decide +kernel\n')
 proof=[f'theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = {base} + j.val := by','  intro j','  have hj := j.isLt','  change j.val < 1817 at hj']
 for k in range(29):
  if k<28:proof.append(f'  by_cases h{k} : j.val < {64*(k+1)}');prefix='  · ';indent='    '
  else:prefix='  ';indent='  '
  proof.append(prefix+f'have hi : {64*k} + j.val % 64 = j.val := by omega')
  if k<28:proof.append(indent+f'have hc := source_index_chunk_{k} ⟨j.val % 64, Nat.mod_lt _ (by decide)⟩')
  else:
   proof.append(indent+'have htail : j.val % 64 < 25 := by omega')
   proof.append(indent+'have hc := source_index_chunk_28 ⟨j.val % 64, htail⟩')
  proof.append(indent+'simpa only [hi, Nat.zero_add] using hc')
 return before.replace(old,'\n'.join(chunks+['\n'.join(proof)]))

rows=[];known20={r['module']:r['accepted_postimage'] for r in B['rows'] if r['accepted_postimage']}
for k in range(72):
 n=f'ImbalancedChen.Data.P5SubdivisionStoredBlock{k:03}';r=selected[n]
 raw=(REPO/r['origin']['path']).read_bytes();assert sha(raw)==r['sha256'] and blob(raw)==r['git_blob_sha1']
 before=raw.decode();size=int(re.search(r'theorem rows_size : rows.size = (\d+) := rfl',before).group(1))
 assert size==(4096 if k<71 else 1817)
 after=generate_full(before,k) if k<71 else generate_partial(before,k,size)
 public=f'theorem source_index_at : ∀ j : Fin rows.size, (rows[j.val]).sourceIndex = {4096*k} + j.val'
 oldproof=public+' := by\n  decide';start=before.index(oldproof);suffix=before[start+len(oldproof):]
 assert before[:start]==after[:after.index('private theorem source_index_chunk_0')]
 assert after.count(public)==1 and after.endswith(suffix)
 assert re.search(r'theorem rows_size[^\n]*',before).group(0)==re.search(r'theorem rows_size[^\n]*',after).group(0)
 replacement=after[start:len(after)-len(suffix)]
 assert before.replace(oldproof,replacement)==after
 b=after.encode();accepted=known20.get(n)
 if accepted:
  existing=Path(accepted['postimage_source']).read_bytes();assert b==existing and sha(b)==accepted['postimage_sha256']
 status='EXACT_EXISTING_REMOTE_ACCEPTED_POSTIMAGE' if k<20 else ('PLANNED_SAME_RECIPE_AWAIT_ACTUAL020_030_ACCEPTANCE' if k<=30 else ('UNVALIDATED_PARTIAL_TAIL_SOURCE_VARIANT' if k==71 else 'PLANNED_UNVALIDATED_FULL_BLOCK_POSTIMAGE'))
 pre={'bytes':len(raw),'sha256':sha(raw),'git_blob_sha1':blob(raw)}
 r.update({'pre_input':pre,'transform':[{'old':oldproof,'new':replacement,'count':1}],'sha256':sha(b),'git_blob_sha1':blob(b),'bytes':len(b),'selection':'EXPLICIT_SUCCESSOR_STORED_KERNEL_BOUNDED_POSTIMAGE','source_validation_status':status,'proof_source_authority':accepted or {'kind':'DETERMINISTIC_STATIC_TEXT_VARIANT_NOT_KERNEL_ACCEPTED','reviewed_full_block_recipe_sha256':sha(recipe.read_bytes()),'partial_tail':k==71}})
 row={'module':n,'rows_size':size,'base':4096*k,'old_source':pre,'postimage':{'bytes':len(b),'sha256':sha(b),'git_blob_sha1':blob(b)},'prefix_before_source_index_at_sha256':sha(before[:start].encode()),'prefix_unchanged':True,'rows_size_declaration_unchanged':True,'source_index_at_public_type':public.removeprefix('theorem '),'source_index_at_public_type_unchanged':True,'chunk_widths':[64]*64 if k<71 else [64]*28+[25],'status':status,'accepted_receipt':accepted,'actual_source_file':None}
 if k==71:
  out=HERE/'partial-tail/P5SubdivisionStoredBlock071.lean';out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(b);row['actual_source_file']=str(out)
 rows.append(row)
assert len(known20)==20 and all(r['prefix_unchanged'] for r in rows)
dump('STORED72_PROPOSED_POSTIMAGES.json',{'schema':'T01_STORED72_EXPLICIT_SUCCESSOR_SOURCE_SELECTION_V1','status':'STATIC_SELECTION_ONLY_NOT_INSTALLED_OR_COMPILED','rows':rows,'accepted20_byte_for_byte_reproduced':True,'actual_020_030_artifact_required_before_acceptance':True,'unvalidated52':True,'tail071_unvalidated':True,'Fine_or_ca9_changed':False})

source_rows=[selected[n] for n in sorted(selected)]
identity=json.dumps([[r['module'],r['sha256'],r['git_blob_sha1']] for r in source_rows],ensure_ascii=False,separators=(',',':')).encode()
dump('PROPOSED_FINE_WINNER_SOURCE_SELECTION.json',{'schema':'T01_FINE_WINNER_PROPOSED_SUCCESSOR_SOURCE_SELECTION_V1','status':'PLANNED_UNINSTALLED_UNCOMPILED_NOT_DRIVER_READY','targets':[F['targets'][0]]+C['winner_targets'],'project_modules':1816,'mathematical_module_count':1859,'audit_modules_not_frozen':True,'files':source_rows,'native_sources':F['native_sources'],'same_native43_no_repin':True,'source_identity_sha256':sha(identity),'source_identity_recipe':'SHA256(UTF8(json.dumps([[module,sha256,git_blob_sha1] for rows sorted by module],ensure_ascii=False,separators=(comma,colon)))); project sources only, native43 separately bound unchanged.','changed_existing_source_modules':[r['module'] for r in rows],'new_winner_source_modules':C['winner_targets'],'Fine_manifest_before':ident(F_PATH),'Fine_or_ca9_mutated':False,'accepted_objects':[]})

reverse={n:set() for n in selected}
for n,r in selected.items():
 for im in r['imports']:
  if im in reverse:reverse[im].add(n)
changed={r['module'] for r in rows};cone=set(changed);todo=list(cone)
while todo:
 n=todo.pop()
 for v in reverse[n]:
  if v not in cone:cone.add(v);todo.append(v)
newwinner=set(C['winner_targets']);others=set(selected)-set(known20)-changed-newwinner
assert len(others)==1736
dump('REQUIRED_REMOTE_OUTPUTS_AND_CONES.json',{'schema':'T01_FINE_WINNER_REQUIRED_OUTPUT_PLAN_V1','changed72_source_roots':sorted(changed),'changed72_reverse_import_cone':sorted(cone),'changed72_reverse_import_cone_count':len(cone),'outside_changed72_cone':sorted(set(selected)-cone),'known_accepted20':sorted(known20),'accepted20_action':'Keep exact accepted postimage/olean evidence. Require actual reviewed object/parent/import/facet binding before restore. Do not schedule original whole-block decide or pretend Lake cache hit. Recovery route owned by T02 dependency-reuse-plan.','unaccepted52_source_builds':sorted(changed-set(known20)),'new8_source_builds':sorted(newwinner),'other1736_project_output_modules':sorted(others),'other1736_action':'No complete retained coherent project artifacts identified here. Real same-selection remote output production is required unless an actual matching dependency artifact is subsequently verified; hashes/success logs are not payloads. ParentTypes output may be recovered from future020-030 artifact; otherwise remote production is necessary.','native43_action':'Keep original09b exact source/config/guard/facet policy. No new native source, but do not skip fresh source compilation merely from equality unless real accepted coherent outputs exist.','minimum_new_proof_source_obligations':60,'complete_old_Lake_restore_ready':False,'verified_object_restore_set':[],'kernel_type_axiom_gates_not_waived':True,'020_030_policy':'When root supplies actual successful kernel/type/axiom artifact, compare each actual source against these fixed expected postimages and bind parent/payloads before changing its acceptance status. No live CI queried here.'})

inventory=[]
for name in ['core-verification-43020290951.zip','p2-f5415e4-closure-43115954951.zip','p4-4c2d214-profile-43108198136.zip']:
 p=BASE/'output/resume-20261112/ci'/name
 with zipfile.ZipFile(p) as z:
  names=[m.filename for m in z.infolist()]
  inventory.append({'path':str(p),'bytes':p.stat().st_size,'member_count':len(names),'object_members':[n for n in names if n.endswith('.olean')],'ilean_members':[n for n in names if n.endswith('.ilean')],'C_native_members':[n for n in names if n.endswith(('.c','.o','.so','.dll'))],'trace_setup_members':[n for n in names if n.endswith(('.trace','.setup.json'))]})
dump('EXISTING_DEPENDENCY_ARTIFACT_BOUNDARIES.json',{'status':'READ_ONLY_EXISTING_INVENTORY_NOT_GLOBAL_REMOTE_CACHE_DENIAL','ZIP_central_directory_only':inventory,'known_Stored_artifact_receipt':ident(old/'EXISTING_STORED_ARTIFACT_FACETS.json'),'known_accepted_Stored_payloads':20,'Core_three_olean_members_are_audit_wrappers_not_mathematical_suppliers':True,'old_P2_P4_no_math_olean_payloads':True,'complete_coherent_project_dependency_artifact_identified':False,'possible_future_remote_cache_not_inferred_absent':True,'official_Mathlib_cache':'Reuse only actual same-pinned official package cache full facets through the existing guard/provenance path; cached snapshot hashes alone are not package bytes. T02 owns exact recovery API/facets plan.','T01_v3':'Only stale local live/source metadata found; no downloaded coherent checkpoint artifact identified. No live CI or cache API queried.'})
dump('STATIC_CHECKS.json',{'Python_AST_parsed':True,'all72_original_preimage_hashes_verified':True,'all72_prefixes_and_public_types_preserved':True,'accepted20_exact_output_bytes_reproduced':True,'full_blocks_000_070_exact_reviewed_pure_AST':71,'071_rows':1817,'071_full64_chunks':28,'071_tail_width':25,'all_selected_imports_unchanged':True,'project_modules':1816,'mathematical_modules':1859,'reverse_cone':len(cone),'new_or_unaccepted_proof_sources':60,'prepare_stage_producer_or_Lean_executed':False,'actual_020_030_acceptance_claimed':False,'tail071_kernel_claimed':False})
print(json.dumps({'project':1816,'math':1859,'changed72_cone':len(cone),'outside_cone':len(set(selected)-cone),'accepted20_same_bytes':20,'unaccepted_stored':52,'new_winner':8,'other_project_outputs':len(others),'tail071_sha256':rows[71]['postimage']['sha256'],'source_identity':sha(identity)},indent=2))
