import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,importlib.util,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
module='ImbalancedChen.CurrentChenUpsilon8TrueLiMass';source=root/'ImbalancedChen/CurrentChenUpsilon8TrueLiMass.lean';expected='9f009161174abeb734c21154ebc368a9ae3354b157fc2da42e199e76d307554c'
assert hashlib.sha256(source.read_bytes()).hexdigest()==expected
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';tree=ast.parse(helper.read_text());exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','uncomment','imports','assignment_at_top','declarations'}],type_ignores=[]),str(helper),'exec'))
parent_names=['ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget','ImbalancedChen.CurrentChenUpsilon9TrueLiMass'];parent_shas=['c4f5a801eadd6128f088b99cd8128602aeba1d0d8fa2a24906cd3e9cd387e761','0f49198775e261606e227e6de621a75f445a066ba851ef3a25748f3e86b65289'];assert imports(source.read_text())==parent_names
ds=declarations(source.read_text());assert len(ds)==3 and sum(d['kind']=='def' for d in ds)==1
assert [d['name'] for d in ds]==['currentChenUpsilon8LogTotientMass','currentChenUpsilon8LogTotientMass_nonneg','eventually_currentChenUpsilon8_liMainMass_le_logTotientMass']
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914';spec=importlib.util.spec_from_file_location('u8_trueli_author_header_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux');paths={};heads={};hashes={}
walk_helper=out/'drafts/20261016-U8CoprimeGateBudget-owner-review.py';wtree=ast.parse(walk_helper.read_text());exec(compile(ast.Module(body=[n for n in wtree.body if isinstance(n,ast.FunctionDef) and n.name in {'locate','read','walk'}],type_ignores=[]),str(walk_helper),'exec'))
baseline=set();parent_closures=[];parent_sets=[]
for name,expected_parent in zip(parent_names,parent_shas):
    seen,missing,findings=walk(name);assert hashes[name]==expected_parent and not missing and not findings;baseline|=seen;parent_sets.append(seen);parent_closures.append({'module':name,'source_sha256':expected_parent,'resolved':len(seen)})
candidate,missing,findings=walk(module);assert not missing and not findings and candidate-baseline=={module}
extra_owned_parent=parent_sets[1]-parent_sets[0];assert not [n for n in extra_owned_parent if not n.startswith('ImbalancedChen.')]
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for n,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/n)==h
provider_checks=[]
for name in ['goldbach','mathlib']:
    pr=providers/name;expected_head=next(x['rev'] for x in packages if x['name']==name);actual=subprocess.check_output(['git','-C',str(pr),'rev-parse','HEAD'],text=True).strip();diff=subprocess.run(['git','-C',str(pr),'diff','--quiet','HEAD','--'],capture_output=True,text=True);assert actual==expected_head and diff.returncode==0;provider_checks.append({'name':name,'actual_HEAD':actual,'manifest_pin':expected_head,'git_diff_HEAD_tracked_exit_code':diff.returncode})
parent_records=[]
for i,(name,expected_parent) in enumerate(zip(parent_names,parent_shas)):
    ap=state/('audits/20261015T225351728783Z/receipt.json' if i==0 else 'audits/20261015T201216595359Z/receipt.json');ar=json.loads(ap.read_text());assert ar['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar['targets'][name]==expected_parent and ar['inputs_before']==ar['inputs_after'] and ar['inputs_before']['pins']==pins
    obj=state/'lib/lean'/Path(name.replace('.','/')).with_suffix('.olean');assert sha(obj)==ar['inputs_before']['owned_object_parts'][name]['.olean']
    parent_records.append({'module':name,'source_sha256':expected_parent,'object_sha256':sha(obj),'owned_receipt_path':str(ap.relative_to(root)),'owned_receipt_sha256':sha(ap),'owned_declaration_count':ar['declaration_counts'][name],'status':ar['status'],'before_after_exact':True,'scope':'Actual own-object replay and complete types/axioms only, no imported-closure kernel replay claim.'})
public_specs={'CurrentChenUpsilon8ProductPan':['currentChenUpsilon8PrefixProducts_data','currentChenUpsilon8PrefixProducts_power_bounds','currentChenUpsilon8_li_argument_power_lower','currentChenUpsilon8_log_gap_lower'],'CurrentChenUpsilon8CoprimeGateBudget':['currentChenUpsilon8LiMainMass'],'CurrentChenUpsilon9TrueLiMass':['tendsto_currentChenUpsilon9_trueLi_normalized_real','eventually_currentChenUpsilon9_trueLi_real_le']}
public_apis=[]
for name,names in public_specs.items():
    p=root/'ImbalancedChen'/f'{name}.lean';byname={d['name']:d for d in declarations(p.read_text())};assert set(names)<=set(byname);public_apis.append({'path':str(p.relative_to(root)),'sha256':sha(p),'complete_actual_public_declarations':[byname[n] for n in names]})
api_specs=[(providers/'goldbach/MathlibNt/SieveTheory/Distribution/BombieriVinogradov.lean',22,29,'The fixed trueLogarithmicIntegral alias is exactly liuLogarithmicIntegral(2/log2), not a different integration constant or proxy'),(providers/'mathlib/Mathlib/Data/Nat/Totient.lean',57,75,'Genuine phi(a)<=a and phi(a)>0 iff a>0; reciprocal direction increases1/a to1/phi(a)'),(root/'ImbalancedChen/CurrentChenTrueLiNormalization.lean',1,30,'Existing actual real exact-remainder normalization source, reused through owned generic9 leading-one theorem')]
api_evidence=[{'path':str(p),'sha256':sha(p),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in api_specs]
claims=[
'Exactly one definition and two theorems are added. LogTotientMass8 is a literal finite sum over the actual U8PrefixProducts image, with the actual weight1/phi(a) and kernel1/(1-log a/log N). There is no modulus argument, artificial coefficient, replacement ninth source or assumed product support.',
'The owned literal U8 source proves a>0, a<N^(2/3), N/a>=N^(1/3), and logarithmic gap>=1/3 for N>=2. The new nonnegative-mass theorem uses exactly that positive actual gap and the genuine nonnegative reciprocal totient. No gap is a caller premise.',
'The only real-variable li estimate invoked is public eventually_currentChenUpsilon9_trueLi_real_le eta heta. That generic theorem has already been proved from the actual exact-remainder sqrt split on all large real arguments; it is not the ninth-specific product transport or an assumed leading-one law. The existing integration constant2/log2 is unchanged.',
'For each fixed eta>0 take the real threshold X from that genuine theorem. Since N^(1/3) tends to infinity, one natural-N threshold puts EVERY actual moving argument N/a above X. This threshold is chosen before any actual a; the theorem requests only eta>0 and has no asymptotic, count, density or harmonic supplier.',
'In the finite normalized sum, the true-log-integral alias is explicitly unfolded exactly as in owned0f49, retaining the same liuLogarithmicIntegral(2/log2) as LiMainMass8. Multiplication by log N/N is justified by N>=2. The identity log(N/a)=logN*(1-log a/logN) uses actual a>0 and positive log N.',
'The actual phi(a)<=a inequality is used in the correct upper-bound direction:1/a<=1/phi(a), with phi(a)>0 paid by actual a>0. It is multiplied only by nonnegative1/gap and1+eta. No incorrect phi reciprocal direction or unproved main-term positivity is used.',
'Finite summation proves the normalized mass inequality as an INTERNAL local have. Positive N and logN then permit exact division conversion to LiMainMass8<=(1+eta)*(N/logN)*LogTotientMass8. The final multiplication reorder is ring algebra; no normalized wrapper, additional definition or caller estimate is introduced.',
'The final type has only eta and eta>0 before an eventual natural N threshold. It preserves the actual eighth product image and one leading li constant. This is a one-sided transport, not a two-sided true-li mass limit, harmonic estimate, density factor8 assembly, complete ordinary U8 mean, hUpper/hLower or adopted K proof.'
]
for d,text in zip(ds,[claims[0],claims[1],' '.join(claims[2:])]):d['source_author_semantic_review']=text
forbidden=[]
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    forbidden.extend(m.group(0) for m in re.finditer(pat,uncomment(source.read_text())))
assert not forbidden
common={'status':'SOURCE_ONLY_AUTHOR_REVIEW_PENDING_NONAUTHOR_AND_RUNTIME','reviewer':'/root/lower_resume (source author)','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':module,'source_sha256':sha(source),'no_Lean_or_build_invoked':True,'bytecode_writes_disabled':True,'no_kernel_owned_or_cache_acceptance_claimed':True}
inventory=sorted((n,hashes[n]) for n in candidate)
dag={**common,'method':'Fresh full proper Lean header walk with pinned parser, all fixed manifest provider roots and Lean/Lake roots, implicit Init/public/meta/import-all. Source DAG only.','parser_path':str(parser_path),'parser_sha256':sha(parser_path),'direct_imports':parent_names,'parent_closures':parent_closures,'baseline_parent_union_resolved':len(baseline),'candidate_resolved':len(candidate),'new_project_vs_parent_union':sorted(candidate-baseline),'new_foreign_vs_parent_union':[],'extra_already_owned_project_from9TrueLi_vs_c4':sorted(extra_owned_parent),'extra_foreign_from9TrueLi_vs_c4':[],'unresolved':missing,'parser_findings':findings,'closure_module_sha_inventory_sha256':hashlib.sha256(json.dumps(inventory).encode()).hexdigest(),'pins':pins,'providers_current':provider_checks,'external_closure_kernel_replay':False}
sem={**common,'path':str(source.relative_to(root)),'declaration_count':3,'definition_count':1,'theorem_count':2,'type_extraction':'All theorem headers split only at actual := by and the definition at top-level assignment outside bracketed named arguments; all complete types, definition and proofs are attached.','all_complete_headers_definitions_and_proofs':ds,'full_current_source':source.read_text(),'parents':parent_records,'source_author_semantic_review':claims,'complete_public_API_source':public_apis,'fixed_native_API_source_evidence':api_evidence,'relative_DAG_delta':{'new_local':[module],'new_foreign':[]},'pins':pins,'providers_current':provider_checks,'forbidden_hits':forbidden,'findings':[],'scope_not_claimed':['density or factor8 bound','actual8 harmonic mean or numeric integral','two-sided actual li mass limit','full ordinary U8 mean','adopted upper K or full hUpper/hLower'],'acceptance_boundary':'Source-author review only. Both actual parent owned gates are freshly verified, but the new leaf still needs non-author complete review and exact root strict/owned authorization.'}
outputs=[]
for name,data in [('20261016-U8TrueLiMass-owner-semantics.json',sem),('20261016-U8TrueLiMass-owner-proper-dag.json',dag)]:
    p=out/name
    with p.open('x',encoding='utf8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
    outputs.append({'path':str(p.relative_to(root)),'sha256':sha(p)})
assert sha(source)==expected
print(json.dumps({'source_sha256':sha(source),'declarations':3,'defs':1,'reports':outputs,'parent_union':len(baseline),'candidate':len(candidate),'new_foreign':[],'all_direct_parents_true_owned':True},indent=2))