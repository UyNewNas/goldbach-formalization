import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,base64
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
out=root/'.lake/proof-continuation/source-reviews'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
ns=ast.parse(helper.read_text());wanted={'sha','uncomment','imports','assignment_at_top','declarations'}
exec(compile(ast.Module(body=[n for n in ns.body if isinstance(n,ast.FunctionDef) and n.name in wanted],type_ignores=[]),str(helper),'exec'))
p=root/'ImbalancedChen/ActualRosserOddBox.lean'
old=p.read_bytes();old_sha=hashlib.sha256(old).hexdigest()
assert old_sha=='2beffd8af22239e3a5428713c614e8e37bcbb300b16c950ff254d2c9ba031888'
patches=[
('''  let l := List.ofFn (fun i : Fin (2 * k) => p i.castSucc)
''','''  let l := List.ofFn (fun i : Fin (2 * k) => p i.castSucc)
  have hllen : l.length = 2 * k := List.length_ofFn
  have hlprod : (l.prod : ℝ) = ∏ i : Fin (2 * k), (p i.castSucc : ℝ) := by
    simp only [l, List.prod_ofFn, Nat.cast_prod]
  have hltake (r : ℕ) : ((l.take r).prod : ℝ) =
      ∏ i : Fin (2 * k) with i.val < r, (p i.castSucc : ℝ) := by
    simp only [l, List.prod_take_ofFn, Nat.cast_prod]
  have hlget (i : Fin l.length) :
      (l.get i : ℝ) = (p (Fin.cast hllen i).castSucc : ℝ) := by
    simp only [l, List.get_ofFn]
'''),
('''    simp [l, actualRosserOddTail, List.mem_ofFn]
''','''    simp only [l, List.mem_toFinset, List.mem_ofFn, actualRosserOddTail,
      Finset.mem_image, Finset.mem_univ, true_and]
'''),
('''    · simp [l]
    · apply Nat.lt_ceil.mpr
      simpa [l, List.prod_ofFn, Nat.cast_prod] using htotalReal
    · intro i hi
      have hil : i.val < 2 * k := by simpa [l] using i.isLt
      apply Nat.lt_ceil.mpr
      simpa [l, List.prod_take_ofFn, List.get_ofFn, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_prod] using hprefixReal ⟨i.val, hil⟩ hi
    · apply Nat.ceil_le.mpr
      simpa [l, List.prod_ofFn, Nat.cast_prod, Nat.cast_mul, Nat.cast_pow] using hshellReal
''','''    · rw [hllen]
      exact ⟨k, by omega⟩
    · apply Nat.lt_ceil.mpr
      rw [hlprod]
      exact htotalReal
    · intro i hi
      apply Nat.lt_ceil.mpr
      rw [Nat.cast_mul, Nat.cast_pow, hltake, hlget]
      exact hprefixReal (Fin.cast hllen i) hi
    · apply Nat.ceil_le.mpr
      rw [Nat.cast_mul, Nat.cast_pow, hlprod]
      exact hshellReal
''')]
new=old
for a,b in patches:
    assert new.count(a.encode())==1
    new=new.replace(a.encode(),b.encode())
inv=new
for a,b in reversed(patches):
    assert inv.count(b.encode())==1
    inv=inv.replace(b.encode(),a.encode())
assert inv==old
before=declarations(old.decode());after=declarations(new.decode())
assert len(before)==len(after)==9 and sum(x['kind']=='def' for x in after)==2
for a,b in zip(before,after):
    assert (a['name'],a['kind'],a['private'],a['complete_source_header'])==(b['name'],b['kind'],b['private'],b['complete_source_header'])
    if a['kind']=='def':assert a['complete_definition']==b['complete_definition']
    if a['name']!='actualRosserOddBox_mem_boundary':assert a==b
assert imports(old.decode())==imports(new.decode())
run=root/'.lake/proof-continuation/runs/20261015T220413968149Z-ImbalancedChen.ActualRosserOddBox'
receipt=json.loads((run/'receipt.json').read_text());assert receipt['status']=='FAILED' and receipt['binding']['source_sha256']==old_sha and receipt['exit_code']==-6
stdout=(run/'stdout.log').read_text();assert 'memory_exception' in stdout and ': error:' not in stdout
pins={name:sha(root/name) for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']};assert pins==receipt['binding']['pins']
parents=[]
for imp in imports(new.decode()):
    if imp.startswith('ImbalancedChen.'):
        q=root/(imp.replace('.','/')+'.lean')
    else:q=Path('/home/slava/codex-lean-ve/native-packages/mathlib')/(imp.replace('.','/')+'.lean')
    assert sha(q)==receipt['binding']['direct_source_sha256'][imp]
    parents.append({'module':imp,'source_path':str(q),'current_sha256':sha(q),'same_as_actual_OOM_receipt':True})
new_sha=hashlib.sha256(new).hexdigest()
report={'schema':'source-only-owner-resource-proof-reconstruction-v1','status':'SOURCE_ONLY_OWNER_LOCAL_PROOF_RESTRUCTURE_AFTER_ACTUAL_OOM_PENDING_ROOT_INDEPENDENT_REVIEW','reviewer':'/root/lower_resume (author of this proof-only resource repair)','created_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':str(p.relative_to(root)),'old_actual_OOM_sha256':old_sha,'current_sha256':new_sha,
'actual_OOM_evidence':{'receipt_path':str((run/'receipt.json').relative_to(root)),'receipt_sha256':sha(run/'receipt.json'),'stdout_path':str((run/'stdout.log').relative_to(root)),'stdout_sha256':sha(run/'stdout.log'),'complete_stdout':stdout,'exit_code':receipt['exit_code'],'max_rss_kib':receipt['max_rss_kib'],'seconds':receipt['seconds'],'memory_mib':receipt['lean_memory_mib'],'actual_proof_diagnostic':False,'OOM_location_identified':False,'old_failed_receipt_preserved':True},
'old_exact_bytes_base64':base64.b64encode(old).decode(),'literal_byte_patches':[{'old':a,'new':b,'occurrences':1} for a,b in patches],'forward_exact_bytes':True,'inverse_exact_bytes':True,
'declaration_count':9,'definition_count':2,'type_extraction':'Theorems use actual := by marker; definitions use top-level assignment outside brackets; named (k := k) arguments retained.','all_complete_unchanged_types_and_definitions':[{k:v for k,v in d.items() if k not in ['start_line','complete_proof_body_after_by']} for d in after],
'full_main_proof_before':next(d for d in before if d['name']=='actualRosserOddBox_mem_boundary')['complete_proof_body_after_by'],'full_main_proof_after':next(d for d in after if d['name']=='actualRosserOddBox_mem_boundary')['complete_proof_body_after_by'],
'imports_before_and_after':imports(new.decode()),'exact_direct_parent_source_bindings':parents,'pins_fresh_unchanged':pins,
'precise_scope':'Only local proof from let l through hchain: four local length/product/prefix/get equalities, explicit finite membership simp only, and fixed cast rw plus original real inequalities. No global/private declaration added. Earlier real product/cube geometry, zero-tail case, all mathematical conditions and subsequent boundary insertion are unchanged.',
'resource_hypothesis':'Default simp/simpa in the dependent list/Fin/cast block may expand the full imported simp set and repeatedly normalize large dependent terms. Local exact equalities restrict rewriting and may lower elaboration/interpreter cost. The actual OOM log gives no proof line; this is a hypothesis, not a localized root cause or guaranteed memory improvement.',
'mathematical_review':['hllen is fixed List.length_ofFn; hlprod and hltake are fixed List.prod_ofFn/prod_take_ofFn plus Nat.cast_prod.','hlget is fixed List.get_ofFn with the same actual index cast from length equality; proof irrelevance preserves the original coordinate.','Parity is the exact witness k for 2*k; all active product and even-index prefix strict inequalities and terminal weak crossing use the same previously proved real bounds.','Only finite proof scripts changed. All9types/2defs/imports, cutoffs/beta/cap assumptions, actual target exclusions and literal ceil level are byte-identical in their complete signatures/definitions.'],
'fresh_source_DAG_change':{'new_local':[],'new_foreign':[],'graph_shape_unchanged':True,'foreign_closure_walk_performed':False},
'acceptance_boundary':{'lean_lake_or_build_invoked':False,'same_failed_bytes_retried':False,'memory_or_other_limits_changed':False,'imports_or_pins_changed':False,'linter_disabled':False,'objects_installed_or_rebound':False,'proof_pass_claimed':False,'owned_acceptance_claimed':False,'note':'Root specifically approved this local source repair only. Root independent full types/byte/math rebind precedes any sole-runtime-owner fair run of the new SHA at original M6144/j2/RSS6656. Old OOM is not reclassified.'}}
dest=out/'20261016-ActualRosserOddBox-local-list-cast-owner-rebind.json'
assert not dest.exists()
assert p.read_bytes()==old
p.write_bytes(new)
with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(p)==new_sha
print(json.dumps({'source_sha256':new_sha,'report':str(dest.relative_to(root)),'report_sha256':sha(dest),'declarations':9,'definitions':2},indent=2))