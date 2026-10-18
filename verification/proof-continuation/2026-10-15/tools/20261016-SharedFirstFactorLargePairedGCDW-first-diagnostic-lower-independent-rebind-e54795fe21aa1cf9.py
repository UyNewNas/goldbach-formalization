import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,hashlib,re,subprocess,importlib.util
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews';module='ImbalancedChen.Part3SharedFirstFactorLargePairedGCDW';source=root/'ImbalancedChen/Part3SharedFirstFactorLargePairedGCDW.lean'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';tree=ast.parse(helper.read_text());exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','uncomment','imports','assignment_at_top'}],type_ignores=[]),str(helper),'exec'))
helper2=out/'drafts/20261016-SharedFirstFactorLargePairedGCDW-lower-independent-review.py';tree=ast.parse(helper2.read_text());exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'declarations','project_walk'}],type_ignores=[]),str(helper2),'exec'))
ownerp=out/'20261016-shared-first-factor-large-paired-gcd-W-first-diagnostic-self-rebind.json';assert sha(ownerp)=='71e9a8f787dda934570ca4171feaff39a0519f836df846b2b1369ef1db9bde1b';owner=json.loads(ownerp.read_text());oldp=root/owner['old_snapshot'].replace('\\','/');old=oldp.read_bytes();new=source.read_bytes();assert sha(oldp)==owner['old_sha256']=='645531ed78523f0c5e2be9ec8a8200fc24a2a30ad115766b020993330d278c1d' and sha(source)==owner['new_sha256']=='46a6defd68675b0be26a003d84fc735ac0a7720f51483e4d9e5dfa67b03ac58f'
x=old
for e in owner['literal_edits']:
 a=e['old'].encode();b=e['new'].encode();assert x.count(a)==1;x=x.replace(a,b,1)
assert x==new;x=new
for e in reversed(owner['literal_edits']):
 a=e['old'].encode();b=e['new'].encode();assert x.count(b)==1;x=x.replace(b,a,1)
assert x==old
for before,after,start,end,beforehex,afterhex in [(old,new,'old_start','old_end','old_bytes_hex','new_bytes_hex'),(new,old,'new_start','new_end','new_bytes_hex','old_bytes_hex')]:
 x=before
 for e in sorted(owner['offset_byte_patches'],key=lambda x:x[start],reverse=True):
  assert x[e[start]:e[end]]==bytes.fromhex(e[beforehex]);x=x[:e[start]]+bytes.fromhex(e[afterhex])+x[e[end]:]
 assert x==after
ods=declarations(old.decode());nds=declarations(new.decode());assert len(ods)==len(nds)==17 and sum(d['kind']=='def' for d in nds)==1;changed=[]
for a,b in zip(ods,nds):
 assert (a['name'],a['kind'],a['private'],a['complete_source_header'])==(b['name'],b['kind'],b['private'],b['complete_source_header'])
 if a['kind']=='def':assert a['complete_definition']==b['complete_definition']
 elif a.get('complete_proof_body_after_by',a.get('complete_term_proof'))!=b.get('complete_proof_body_after_by',b.get('complete_term_proof')):changed.append(a['name'])
assert changed==['cleanedAlpha_sharedLargePairedGCDW_bound'];assert next(d for d in nds if d['name']=='slice_gamma')['complete_term_proof']=='rfl'
assert imports(old.decode())==imports(new.decode())
priorp=out/'20261016-SharedFirstFactorLargePairedGCDW-lower-independent-semantics.json';assert sha(priorp)=='b28e8ef457decd71a561a591d6e73d6c8674e05050c2fe6075417660c0c380a8';prior=json.loads(priorp.read_text())
runp=state/'runs/20261015T235913820331Z-ImbalancedChen.Part3SharedFirstFactorLargePairedGCDW/receipt.json';receipt=json.loads(runp.read_text());logp=runp.with_name('stdout.log');log=logp.read_text();assert receipt['status']=='FAILED' and receipt['binding']==receipt['binding_after'] and receipt['binding']['source_sha256']==sha(oldp) and sha(logp)==owner['failed_stdout_sha256'] and sha(runp)==owner['failed_receipt_sha256']
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']};assert pins==owner['pins']==receipt['binding']['pins']
for n,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/n)==h
parents=[]
for n,h in owner['current_owned_direct_parents_source_binding'].items():
 p=root/(n.replace('.','/')+'.lean');assert sha(p)==h==receipt['binding']['direct_source_sha256'][n];obj=state/'lib/lean'/(n.replace('.','/')+'.olean');assert sha(obj)==receipt['binding']['dependencies'][n]==owner['actual_failed_object_binding'][n];audits=[]
 for ap in (state/'audits').glob('*/receipt.json'):
  ar=json.loads(ap.read_text())
  if ar.get('status')=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar.get('targets',{}).get(n)==h and ar.get('inputs_before',{}).get('owned_object_parts',{}).get(n,{}).get('.olean')==sha(obj):audits.append({'path':str(ap),'sha256':sha(ap)})
 assert audits;parents.append({'module':n,'source_sha256':h,'object_sha256':sha(obj),'actual_owned_audits':audits})
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');checks=[]
for n in ['goldbach','mathlib']:
 p=providers/n;head=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip();pin=next(v['rev'] for v in packages if v['name']==n);diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True);assert head==pin and diff.returncode==0;checks.append({'name':n,'actual_HEAD':head,'manifest_pin':pin,'tracked_diff_HEAD_exit_code':diff.returncode})
api=providers/'mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean';assert sha(api)==owner['actual_fixed_API']['sha256'];native=api.read_text().splitlines();excerpt='\n'.join(native[74:90]);assert excerpt==owner['actual_fixed_API']['literal_source_lines_75_90']
pinned=subprocess.check_output(['git','-C',str(providers/'mathlib'),'show',checks[1]['manifest_pin']+':Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean']);assert hashlib.sha256(pinned).hexdigest()==sha(api)
pp=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(pp)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914';spec=importlib.util.spec_from_file_location('wholeW_actual_repair_independent_parser',pp);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
cand,foreign,missing,findings=project_walk(module);base={};baseforeign=set()
for n in imports(new.decode()):
 g,f,m,fn=project_walk(n);assert not m and not fn;base.update(g);baseforeign|=f
assert not missing and not findings and set(cand)-set(base)=={module} and not foreign-baseforeign
report={'status':'SOURCE_ONLY_NONAUTHOR_ACTUAL_FIRST_DIAGNOSTIC_EXACT_REBIND','reviewer':'/root/lower_resume (not source author)','created_utc':datetime.now(timezone.utc).isoformat(),'module':module,'old_sha256':sha(oldp),'new_sha256':sha(source),'author_report':{'path':str(ownerp),'sha256':sha(ownerp)},'historical_complete_independent_scope':{'path':str(priorp),'sha256':sha(priorp),'preserved_unchanged':True},'full_new_source':new.decode(),'all_seventeen_complete_declarations':nds,'declaration_count':17,'definition_count':1,'complete_header_extraction':'All tactic declarations split at actual :=by; slice_gamma is the direct top-level :=rfl term, not dropped or misparsed.','all_seventeen_complete_headers_unchanged':True,'sole_definition_unchanged':True,'slice_gamma_complete_term_proof_unchanged':True,'other_fifteen_proofs_unchanged':True,'changedproof':changed,'literal_edits':owner['literal_edits'],'offset_byte_patches':owner['offset_byte_patches'],'both_literal_and_offset_forward_inverse_exact':True,'actual_failure':{'receipt_path':str(runp),'receipt_sha256':sha(runp),'stdout_path':str(logp),'stdout_sha256':sha(logp),'full_stdout':log,'old_status_preserved':'FAILED'},'direct_parents_actual_bindings':parents,'native_reverse_product_API':{'path':str(api),'sha256':sha(api),'current_equals_pinned_blob':True,'lines':[75,90],'literal_source':excerpt},'independent_proof_review':[
'The actual n2-zero branch first has beta(n1)*star(0)*weight. Existing star_zero and mul_zero turn the first product into0 but leave0*weight inside the norm. The added zero_mul removes exactly that remaining factor, so norm_zero is now used and the original hA/le_rfl branches have the actual real order goal. No coefficient nonzero condition or estimate changes.',
'The actual mask sum is curried in n1 and n2. Pinned Finset Sigma lines75–90 explicitly provide the sum_product-prime variant for this reverse direction. Replacing only the unprimed name restores the exact same ordered Cartesian product and same primitive/same-p/large-gcd filtered cardinal, including all diagonals.',
'The original full b28 mathematical review remains applicable because the only differences are these two literal proof/API sites and all17 headers/one definition/imports are equal. The original arbitrary-real kappa, signed residue, actual clean-alpha divisor deletion, full shared composite p, both unit gates, same-p congruence, original-beta-outside convention and exact16/4 wholeW bound remain unchanged. No rawzero/NZ/payment or final-target claim is added.',
'Current direct parent source and original-object SHA pairs match the real old failed run and their actual full-owned audit receipts. This new source is still uncompiled by this reviewer; old645 FAILED receipt and historical source review are retained.'
],'fresh_relative_project_DAG':{'parser_path':str(pp),'parser_sha256':sha(pp),'candidate_count':len(cand),'parent_union_count':len(base),'addedlocal':sorted(set(cand)-set(base)),'addedforeign':sorted(foreign-baseforeign),'missing':missing,'parser_findings':findings,'current_local_sources':cand,'scope':'project source header graph and foreign fringe only; not full foreign/cache acceptance'},'pins':pins,'provider_HEAD_tracked_clean':checks,'no_source_edit_Lean_build_install_cache_mutation_or_resource_change':True,'bytecode_writes_disabled':True,'not_strict_or_owned_acceptance':True}
rp=out/'20261016-SharedFirstFactorLargePairedGCDW-first-diagnostic-lower-independent-rebind.json';assert not rp.exists();rp.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8');assert sha(source)==owner['new_sha256'];print(json.dumps({'report':str(rp),'sha256':sha(rp),'source':sha(source),'counts':[17,1],'relativeDAG':[len(cand),len(base)],'changedproof':changed,'status':'SOURCE_ONLY'},indent=2))