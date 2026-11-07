import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,base64
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');out=root/'.lake/proof-continuation/source-reviews'
helper_parser=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
wanted={'sha','uncomment','imports','assignment_at_top','declarations'};tree=ast.parse(helper_parser.read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in wanted],type_ignores=[]),str(helper_parser),'exec'))
p=root/'ImbalancedChen/ActualRosserOddBox.lean';old=p.read_bytes();old_text=old.decode();old_sha=sha(p)
assert old_sha=='1bc9376e2d9c96844ddf056ce667c9f8b41bf0e9e46d2763c1314e6a9cd9ea73'
main=old_text.index('theorem actualRosserOddBox_mem_boundary')
let_line='  let l := List.ofFn (fun i : Fin (2 * k) => p i.castSucc)\n'
let_index=old_text.index(let_line,main)
eq_start=let_index+len(let_line);eq_end=old_text.index('  have hlinj',eq_start)
local_eq=old_text[eq_start:eq_end]
assert local_eq.startswith('  have hllen') and local_eq.count('  have ')==4
chain_start=old_text.index('  have hchain :',eq_end);chain_end=old_text.index('  have hqnot',chain_start)
chain_block=old_text[chain_start:chain_end]
chain_header,chain_body=chain_block.split(':= by\n',1)
assert chain_body.startswith('    refine ⟨hlsorted')
extracted='\n'.join(line[2:] if line.startswith('  ') else line for line in chain_body.split('\n'))
new_helper='''private theorem odd_boundaryChain_of_realBounds
    {k : ℕ} (p : Fin (2 * k + 1) → ℕ) (R : ℝ)
    (hlsorted : (List.ofFn (fun i : Fin (2 * k) => p i.castSucc)).SortedGT)
    (htotalReal : (∏ i : Fin (2 * k), (p i.castSucc : ℝ)) < R)
    (hprefixReal : ∀ i : Fin (2 * k), Even i.val →
      (∏ j : Fin (2 * k) with j.val < i.val, (p j.castSucc : ℝ)) *
        (p i.castSucc : ℝ) ^ 3 < R)
    (hshellReal : R ≤ (∏ i : Fin (2 * k), (p i.castSucc : ℝ)) *
      (p (Fin.last (2 * k)) : ℝ) ^ 3) :
    LinearSieve.UpperRosserBoundaryChain (Nat.ceil R)
      (p (Fin.last (2 * k))) (List.ofFn (fun i : Fin (2 * k) => p i.castSucc)) := by
'''+let_line+local_eq+'''  change LinearSieve.UpperRosserBoundaryChain (Nat.ceil R) (p (Fin.last (2 * k))) l
'''+extracted
marker='/-- All prefix tests and the terminal crossing are verified at the same\n'
assert old_text.count(marker)==1
patches=[(marker,new_helper+'\n'+marker),
 (let_line+local_eq+'  have hlinj',let_line+'  have hlinj'),
 (chain_block,chain_header+''':=
    odd_boundaryChain_of_realBounds p ((N : ℝ) ^ beta)
      hlsorted htotalReal hprefixReal hshellReal
''')]
new=old
for a,b in patches:
    assert new.count(a.encode())==1
    new=new.replace(a.encode(),b.encode())
inverse=new
for a,b in reversed(patches):
    assert inverse.count(b.encode())==1
    inverse=inverse.replace(b.encode(),a.encode())
assert inverse==old
before=declarations(old_text);after=declarations(new.decode());assert len(before)==9 and len(after)==10 and sum(d['kind']=='def' for d in after)==2
byname={d['name']:d for d in after};new_names=set(byname)-{d['name'] for d in before}
assert new_names=={'odd_boundaryChain_of_realBounds'}
for d in before:
    x=byname[d['name']]
    assert (d['name'],d['kind'],d['private'],d['complete_source_header'])==(x['name'],x['kind'],x['private'],x['complete_source_header'])
    if d['kind']=='def':assert d['complete_definition']==x['complete_definition']
    if d['name']!='actualRosserOddBox_mem_boundary':
        assert {k:v for k,v in d.items() if k!='start_line'}=={k:v for k,v in x.items() if k!='start_line'}
assert byname['odd_boundaryChain_of_realBounds']['private'] and imports(old_text)==imports(new.decode())
run=root/'.lake/proof-continuation/runs/20261015T221702479672Z-ImbalancedChen.ActualRosserOddBox';receipt=json.loads((run/'receipt.json').read_text())
assert receipt['status']=='FAILED' and receipt['binding']['source_sha256']==old_sha and receipt['exit_code']==-6
stdout=(run/'stdout.log').read_text();assert 'memory_exception' in stdout and ': error:' not in stdout
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']};assert pins==receipt['binding']['pins']
parents=[]
for imp in imports(new.decode()):
    q=root/(imp.replace('.','/')+'.lean') if imp.startswith('ImbalancedChen.') else Path('/home/slava/codex-lean-ve/native-packages/mathlib')/(imp.replace('.','/')+'.lean')
    assert sha(q)==receipt['binding']['direct_source_sha256'][imp]
    parents.append({'module':imp,'path':str(q),'current_source_sha256':sha(q),'same_as_actual_failed_receipt':True})
new_sha=hashlib.sha256(new).hexdigest()
report={'schema':'source-only-owner-private-proof-extraction-resource-rebind-v1','status':'SOURCE_ONLY_OWNER_EXACT_PRIVATE_LIST_CHAIN_EXTRACTION_AFTER_SECOND_ACTUAL_OOM_PENDING_ROOT_INDEPENDENT_REVIEW','reviewer':'/root/lower_resume (author of approved resource proof extraction)','created_at_utc':datetime.now(timezone.utc).isoformat(),'candidate':str(p.relative_to(root)),'old_actual_failed_sha256':old_sha,'current_sha256':new_sha,'original_source_sha256':'2beffd8af22239e3a5428713c614e8e37bcbb300b16c950ff254d2c9ba031888',
'actual_second_OOM':{'receipt':str((run/'receipt.json').relative_to(root)),'receipt_sha256':sha(run/'receipt.json'),'stdout':str((run/'stdout.log').relative_to(root)),'stdout_sha256':sha(run/'stdout.log'),'complete_stdout':stdout,'exit_code':receipt['exit_code'],'memory_mib':receipt['lean_memory_mib'],'max_rss_kib':receipt['max_rss_kib'],'seconds':receipt['seconds'],'proof_diagnostic':False,'OOM_line_identified':False,'runtime_success_inferred_from_shorter_time':False},
'old_exact_bytes_base64':base64.b64encode(old).decode(),'literal_byte_patches':[{'old':a,'new':b,'occurrences':1} for a,b in patches],'forward_exact_bytes':True,'inverse_exact_bytes':True,
'declaration_count_before':9,'declaration_count_after':10,'definition_count_before_after':2,'original9_complete_types_definitions_unchanged':True,'all_original_nonmain_proof_bodies_unchanged':True,'one_added_private_theorem':byname['odd_boundaryChain_of_realBounds'],'all_complete_current_types_definitions_proofs':after,
'mechanical_extraction':{'original_local_equalities_exact_text':local_eq,'extracted_chain_proof_exact_text_before_indentation_shift':chain_body,'exact_chain_proof_indentation_shift_spaces':-2,'helper_body_is_only_original_let_local_equalities_plus_target_change_plus_original_chain_proof':True,'main_local_equalities_removed_and_same_chain_replaced_by_exact_helper_call':True,'main_original_real_geometry_proofs_unchanged':True},
'fixed_mathematical_scope':['New private helper is a finite real-product/ceil-natural/list-chain conversion. It has no N, beta, cap, Rosser density or analytic supplier parameter.','The original main proves its actual sorted list, total active bound, every even-index cubic-prefix bound and terminal weak shell exactly as before. Those already-proved facts instantiate the helper at R=N^beta.','No actual boundary/density/main term is supplied by the caller. Original9 full types,2 defs,imports,cutoffs,target exclusions and mathematical conditions remain unchanged.'],
'resource_hypothesis':'Isolating the existing dependent list/Fin/cast proof in one private theorem may release a smaller elaboration context than elaborating it under the large main proof. The two actual OOMs did not identify a proof line. No successful memory reduction, OOM location or runtime acceptance is claimed.',
'imports_before_after':imports(new.decode()),'exact_current_direct_parent_source_bindings':parents,'pins_fresh_unchanged':pins,'source_DAG':{'graph_shape_unchanged':True,'new_local_imports':[],'new_foreign_imports':[],'new_global_private_declaration_count':1,'foreign_closure_walk_repeated':False},
'evidence_boundary':{'lean_lake_build_invoked':False,'old_failed_bytes_retried':False,'limits_or_linter_or_pins_changed':False,'objects_installed_or_rebound':False,'new_source_strict_or_owned_pass_claimed':False,'old_two_OOM_receipts_modified':False,'note':'Root explicitly approved exactly this one private theorem type and mechanical extraction. Root full10types2defs independent review precedes a sole-runtime-owner new-SHA fair attempt at original6144/j2/RSS6656. No wider candidate or import/resource change.'}}
dest=out/'20261016-ActualRosserOddBox-private-real-chain-owner-rebind.json';assert not dest.exists() and p.read_bytes()==old
p.write_bytes(new)
with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(p)==new_sha
print(json.dumps({'source_sha256':new_sha,'report':str(dest.relative_to(root)),'report_sha256':sha(dest),'declarations':10,'definitions':2,'new_private':['odd_boundaryChain_of_realBounds']},indent=2))