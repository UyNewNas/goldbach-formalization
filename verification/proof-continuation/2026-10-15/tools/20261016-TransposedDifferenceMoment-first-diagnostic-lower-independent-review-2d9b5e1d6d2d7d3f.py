import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';tree=ast.parse(helper.read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','uncomment','imports','assignment_at_top','declarations'}],type_ignores=[]),str(helper),'exec'))
owner_path=out/'20261016-transposed-difference-moment-first-diagnostic-self-rebind.json';assert sha(owner_path)=='f0acca89f6f0eaac9a017c370736a25e8e79d17d63e2328efe4bff26844e352a';owner=json.loads(owner_path.read_text())
source=root/owner['candidate'];old_path=root/owner['old_snapshot'];old=old_path.read_bytes();new=source.read_bytes();old_sha='248f6371a93df223c875908e12263db6b20f95a18df758f892f4c0a4b5485908';new_sha='ad1d91a87458ce853ea35f6b05ecbf2d5f46195264de63b7b3abefccf23ba5e0'
assert sha(old_path)==old_sha and sha(source)==new_sha
patched=old;patch_records=[]
for i,patch in enumerate(owner['edits']):
    a=patch['old'].encode();b=patch['new'].encode();count=patched.count(a);assert count>=1
    if 'index' in patch:
        assert patch['index']==0;pos=patched.index(a);patched=patched[:pos]+b+patched[pos+len(a):]
    else:
        assert count==1;patched=patched.replace(a,b)
    patch_records.append({'old':patch['old'],'new':patch['new'],'old_occurrences_before_step':count,'replacements_at_step':1,'method':'first occurrence' if 'index' in patch else 'unique occurrence'})
assert patched==new
inverse=new
for patch in reversed(owner['edits']):
    a=patch['old'].encode();b=patch['new'].encode();assert inverse.count(b)==1;inverse=inverse.replace(b,a)
assert inverse==old
old_ds=declarations(old.decode());new_ds=declarations(new.decode());assert len(old_ds)==len(new_ds)==14 and not any(d['kind']=='def' for d in new_ds)
changes=[]
for a,b in zip(old_ds,new_ds):
    assert (a['kind'],a['name'],a['private'],a['complete_source_header'])==(b['kind'],b['name'],b['private'],b['complete_source_header'])
    if a['complete_proof_body_after_by']!=b['complete_proof_body_after_by']:changes.append(a['name'])
assert changes==['difference_row_le','cleanedAlpha_largeModulusW_bound','both_lengths_lower_bound','betaL2_mul_cleanedAlpha_largeModulusW_log_payment']
assert imports(old.decode())==imports(new.decode())==['ImbalancedChen.Part3TransposedModulusProgression']
prior_path=out/'20261016-TransposedDifferenceMoment-lower-independent-semantics.json';assert sha(prior_path)=='38a157de531d409f98d3d14936719e77748c2242300375a38298077f79d7b4c1';prior=json.loads(prior_path.read_text());prior_ds=prior['candidate']['all_complete_headers_and_proofs'];assert len(prior_ds)==14
for a,b in zip(old_ds,prior_ds):
    assert a['name']==b['name'] and a['complete_source_header'].replace('\r\n','\n')==b['complete_source_header']
    assert a['complete_proof_body_after_by'].replace('\r\n','\n')==b['complete_proof_body_after_by']
log_path=root/owner['failed_stdout'];assert sha(log_path)==owner['failed_stdout_sha256']=='20ebaf536ad3733275e9df73305f88cb9791a92d25149c149dde7b83228a1ee6';log=log_path.read_text();receipt_path=log_path.with_name('receipt.json');receipt=json.loads(receipt_path.read_text())
assert receipt['status']=='FAILED' and receipt['exit_code']==1 and receipt['binding']==receipt['binding_after'] and receipt['binding']['source_sha256']==old_sha
err_lines=[int(s) for s in re.findall(r'Part3TransposedDifferenceMoment\.lean:(\d+):\d+: error',log)];assert err_lines==[52,67,225,290,290,410]
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']};assert pins==receipt['binding']['pins']==owner['pins_fresh']
for name,value in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/name)==value
parent_name='ImbalancedChen.Part3TransposedModulusProgression';parent=root/'ImbalancedChen/Part3TransposedModulusProgression.lean';parent_sha='3605840b55a1c1c4e1b0cbddbaffeee18325d92006f62e30a6d70224d994c5a0';assert sha(parent)==parent_sha==receipt['binding']['direct_source_sha256'][parent_name]
parent_object=state/'lib/lean/ImbalancedChen/Part3TransposedModulusProgression.olean';assert sha(parent_object)==receipt['binding']['dependencies'][parent_name]=='9c0f0aa2a9693a120538a406c9739a08778fcb4c2a1cecd4af8ec7bd9e901143'
parent_rebind_path=out/'20261016-transposed-modulus-progression-first-diagnostic-independent-rebind.json';assert sha(parent_rebind_path)=='6e66b5d11c2e30ad8855b9b4bcf0db8f7278a183d32cd9e75d4d09ef01264fae';pr=json.loads(parent_rebind_path.read_text())
parent_old_path=out/'drafts/Part3TransposedModulusProgression.b9300cf15133a7ebcb9eb1efee9e8b86889425c1d1a4d860188bc7a5f28f1a53.lean';assert sha(parent_old_path)=='b9300cf15133a7ebcb9eb1efee9e8b86889425c1d1a4d860188bc7a5f28f1a53'
parent_old_ds=declarations(parent_old_path.read_text());parent_new_ds=declarations(parent.read_text());assert len(parent_old_ds)==len(parent_new_ds)==18
assert imports(parent_old_path.read_text())==imports(parent.read_text())
for a,b in zip(parent_old_ds,parent_new_ds):
    assert (a['name'],a['kind'],a['complete_source_header'])==(b['name'],b['kind'],b['complete_source_header'])
    if a['kind']=='def':assert a['complete_definition']==b['complete_definition']
parent_audits=[]
for ap in (state/'audits').glob('*/receipt.json'):
    ar=json.loads(ap.read_text())
    if ar.get('status')=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar.get('targets',{}).get(parent_name)==parent_sha:
        assert ar['inputs_before']==ar['inputs_after'] and ar['inputs_before']['pins']==pins
        assert ar['inputs_before']['owned_object_parts'][parent_name]['.olean']==sha(parent_object)
        parent_audits.append({'path':str(ap.relative_to(root)),'sha256':sha(ap),'declaration_count':ar['declaration_counts'][parent_name],'before_after_exact':True,'status':ar['status']})
assert parent_audits
manifest=json.loads((root/'lake-manifest.json').read_text());providers=Path('/home/slava/codex-lean-ve/native-packages');provider_checks=[]
for name in ['goldbach','mathlib']:
    p=providers/name;expected=next(x['rev'] for x in manifest['packages'] if x['name']==name);actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip();diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True);assert actual==expected and diff.returncode==0
    provider_checks.append({'name':name,'actual_HEAD':actual,'manifest_pin':expected,'git_diff_HEAD_tracked_exit_code':diff.returncode})
mathlib=providers/'mathlib';api_specs=[(root/'ImbalancedChen/Part3DistributionTargets.lean',36,53,'Actual MediumAtom and scale=U*V; no normalized replacement scale'),(root/'ImbalancedChen/Part3DistributionTargets.lean',124,133,'Actual MediumAdmissible includes U>=1 and V>=1, with the original moving signed residue and original monomials retained'),(mathlib/'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',113,119,'Real positive real powers at positive actual scale'),(mathlib/'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',160,166,'Real rpow_nonneg uses the explicit genuine scale nonnegativity'),(mathlib/'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',204,211,'Actual positive-base rpow_add identity used in the same multiplication inequality')]
apis=[{'path':str(p),'sha256':sha(p),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in api_specs]
forbidden=[]
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    forbidden.extend(m.group(0) for m in re.finditer(pat,uncomment(new.decode())))
assert not forbidden
report={'status':'SOURCE_ONLY_INDEPENDENT_ACTUAL_DIAGNOSTIC_EXACT_REBIND_PENDING_RUNTIME_NOT_LEAN_PASS','reviewer':'/root/lower_resume, non-author of /root/dispersion_resume repair','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':'ImbalancedChen.Part3TransposedDifferenceMoment','source_path':str(source.relative_to(root)),'old_source_sha256':old_sha,'new_source_sha256':new_sha,'old_snapshot_path':str(old_path.relative_to(root)),'source_author_report':{'path':str(owner_path.relative_to(root)),'sha256':sha(owner_path)},'prior_full_independent_review':{'path':str(prior_path.relative_to(root)),'sha256':sha(prior_path),'original_source_bytes_and_full_headers_proofs_rebound_to_snapshot':True,'preserved':True,'boundary':'Old source review was SOURCE_ONLY. Its candidate subsequently actually FAILED. It is not a Lean acceptance receipt and is not reused as acceptance for this new source.'},'actual_failure':{'receipt_path':str(receipt_path.relative_to(root)),'receipt_sha256':sha(receipt_path),'stdout_path':str(log_path.relative_to(root)),'stdout_sha256':sha(log_path),'stdout_lines':len(log.splitlines()),'full_stdout':log,'status':'FAILED','exit_code':receipt['exit_code'],'source_binding_before_after_exact':True,'actual_error_lines':err_lines,'command':receipt['command'],'guard_error':receipt['guard_error']},'literal_patches_independently_replayed':patch_records,'forward_bytes_exact':True,'reverse_bytes_exact':True,'declaration_count':14,'definition_count':0,'type_extraction':'Every theorem header ends only at the actual := by proof separator, retaining all binders, named arguments and complete result types. Raw old/new headers compare exactly.','all_complete_current_headers_and_proofs':new_ds,'full_current_source':new.decode(),'proof_sites_changed':changes,'all_other_10_proof_bodies_exactly_unchanged':True,'semantic_patch_review':['In both half-row injections the sole new change reduces the exact lambda equality to n-a=n-b or a-n=b. Actual a<n,b<n and n<a,n<b gates already present prevent Nat subtraction truncation. The source map, positive Ioc target and separate diagonal are unchanged. This directly addresses actual omega opaque-lambda counterexamples at52/67.','The largeModulusW multiplication uses explicit hC.le and rpow_nonneg. Actual admissibility already gives U,V>=1, so U*V>=0 and this is definitionally the same scale. No new positivity gate, distribution estimate, bound on coefficients or target estimate is assumed.','The both-length lower-bound proof explicitly forms the SAME inequality scale^(1-sigma)*scale^sigma<=scale^(1-sigma)*V. Its first equality is the same positive-base rpow_add algebra; the upper U bound and nonnegative V are unchanged. Existing hp>0 permits cancellation mathematically, and nlinarith is the local proof-script attempt replacing the overloaded wrong mul_le_mul_left API. No restriction on sigma or new geometry premise is inserted.','Only the ring tactic after rw[mul_pow] is deleted, matching the actual no-goals diagnostic. The preceding coefficient equality, p,N,E,Q constants and every fixed real-A logarithmic payment are unchanged.','All14 full types, imports and every byte outside these5 literal edits are unchanged. In particular the actual off-diagonal tau2 bound8U²HU, diagonal10X, original betaL2/C Xeps X² HV^p bracket20/U+64HU/D+16HU/V, original monomial-derived U,V>=Xsigma, arbitrary real A, epsilon=min(sigma,delta)/2, threshold before actual atom d/Y, and same-mask fullNZ=wholeW-rawZero scope remain. No both-small region or full target completion is claimed.'],'fixed_API_source_evidence':apis,'parent_binding':{'module':parent_name,'old_review_parent_sha256':sha(parent_old_path),'current_source_sha256':sha(parent),'current_object_sha256':sha(parent_object),'parent_type_proof_only_rebind_report_path':str(parent_rebind_path.relative_to(root)),'parent_rebind_report_sha256':sha(parent_rebind_path),'all18_parent_headers_and2defs_rechecked_unchanged':True,'parent_current_owned_receipts':parent_audits,'scope':'Actual sole direct parent owned23 gate, no imported-closure replay acceptance.'},'invariants':{'complete_14_headers_exactly_equal':True,'definitions':0,'sole_import_exactly_equal':True,'all_thresholds_constants_domains_unchanged_by_inverse_bytes':True,'no_import_or_foreign_delta':True,'pins_unchanged':True,'no_resource_linter_or_checker_change':True},'same_import_DAG_boundary':'No new full DAG walk is claimed for a pure exact proof-byte rebind. The sole import is unchanged; its current source/object/complete type rebind and actual own-object acceptance are fresh. New foreign delta is zero by exact imports.','pins':pins,'providers_current_pin_HEAD_and_clean':provider_checks,'forbidden_hits':forbidden,'old_failed_and_old_review_preserved':True,'no_Lean_or_build_invoked':True,'no_source_modified':True,'bytecode_writes_disabled':True,'findings':[],'acceptance_boundary':'Independent source semantics/API rebind only. The actual old candidate is FAILED; this new candidate still needs root authorized actual strict run and complete owned acceptance.'}
p=out/'20261016-TransposedDifferenceMoment-first-diagnostic-lower-independent-rebind.json'
with p.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(source)==new_sha and sha(parent)==parent_sha
print(json.dumps({'report_path':str(p.relative_to(root)),'report_sha256':sha(p),'old_sha256':old_sha,'new_sha256':new_sha,'all14types_unchanged':True,'defs':0,'exact_forward_inverse':True,'parent_owned':parent_audits,'no_Lean':True},indent=2))