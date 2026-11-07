import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,importlib.util,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
module='ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget'
source=root/'ImbalancedChen/CurrentChenUpsilon8CoprimeGateBudget.lean'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
ns=ast.parse(helper.read_text());wanted={'sha','uncomment','imports','assignment_at_top','declarations'}
exec(compile(ast.Module(body=[n for n in ns.body if isinstance(n,ast.FunctionDef) and n.name in wanted],type_ignores=[]),str(helper),'exec'))
assert sha(source)=='c4f5a801eadd6128f088b99cd8128602aeba1d0d8fa2a24906cd3e9cd387e761'
parent=root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean';assert sha(parent)=='80621797c21adc263fc702e07a13c0b0b543a40f34ca2658a7fa281e1af12b11'
parent_audit=state/'audits/20261015T215816603875Z/receipt.json';audit=json.loads(parent_audit.read_text())
assert audit['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and audit['targets']['ImbalancedChen.CurrentChenUpsilon8ProductPan']==sha(parent)
ds=declarations(source.read_text());assert len(ds)==10 and sum(d['kind']=='def' for d in ds)==3
assert imports(source.read_text())==['ImbalancedChen.CurrentChenUpsilon8ProductPan']
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py'
assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
spec=importlib.util.spec_from_file_location('u8_gate_frozen_header_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux')
paths={};heads={};hashes={}
def locate(name):
    if name not in paths:
        rel=Path(name.replace('.','/')).with_suffix('.lean')
        choices=[root/rel] if name=='ImbalancedChen' or name.startswith('ImbalancedChen.') else [providers/p['name']/rel for p in packages]+[std/'src/lean'/rel,std/'src/lean/lake'/rel]
        paths[name]=next((p for p in choices if p.is_file()),None)
    return paths[name]
def read(name):
    if name not in heads:
        p=locate(name)
        if p is None:heads[name]=None
        else:
            b=p.read_bytes();hashes[name]=hashlib.sha256(b).hexdigest();heads[name]=parser.header_imports(b.decode())
    return heads[name]
def walk(name):
    seen=set();missing=[];findings=[]
    def visit(n):
        if n in seen:return
        seen.add(n);h=read(n)
        if h is None:missing.append(n);return
        if h['parser_findings']:findings.append({'module':n,'findings':h['parser_findings']})
        for item in h['imports']:visit(item['module'])
    visit(name);return seen,missing,findings
baseline,bmissing,bfindings=walk('ImbalancedChen.CurrentChenUpsilon8ProductPan');candidate,missing,findings=walk(module)
assert not bmissing and not bfindings and not missing and not findings and candidate-baseline=={module}
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for name,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/name)==h
provider_checks=[]
for name in ['goldbach','mathlib']:
    p=providers/name;expected=next(x['rev'] for x in packages if x['name']==name)
    actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip();diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert actual==expected and diff.returncode==0
    provider_checks.append({'name':name,'manifest_pin':expected,'actual_HEAD':actual,'git_diff_HEAD_tracked_exit_code':diff.returncode})
forbidden=[];clean=uncomment(source.read_text())
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    forbidden.extend(m.group(0) for m in re.finditer(pat,clean))
assert not forbidden
claims=[
'The sole parent is the genuinely owned actual U8 product/Pan leaf 80621797. The new definitions use its literal product image, exact modulus-independent zero-one coefficient and original Pan window. No ninth-source set or artificial coefficient replaces it.',
'Unfolding actual U8 product membership supplies its actual selector pair. The generic ordered-prime data theorem applies definitionally because chenY8PrimeSelector and chenY9PrimeSelector have the same predicate at these parameters. Actual p1>=N^(417/5000), strict p1<N^(1/3)<=p2 give both genuine primes the same positive lower bound. Their possible common divisor with d is retained, never equated with a presieve gate.',
'For positive moduli in any S subset Icc 1 Q, non-coprimality of p1*p2 with d forces p1|d or p2|d. The already owned generic prime-divisor reciprocal-totient bound is applied twice. It was proved with totient_super_multiplicative and does not assume a prime is coprime to its modulus cofactor. The local elementary reciprocal inequality uses p>=2 and p>=H. This proves the actual finite budget 16*N^(-417/5000)*(1+log(max1Q)).',
'LiMainMass8 is the literal ungated true-li sum on actual Products8. Defect8 is precisely its non-coprime part. Its same-coefficient window identity is the already proved U8ProductCoefficient_sum with the defect test; the original Coprime a d remains visible.',
'GateError8 contains the very same actual signed upper Rosser coefficient as a future count sieve. The proof bounds its absolute value using abs(actuallambda)<=1, nonnegativity of the actual true-li terms and finite Fubini. No individual lambda is assumed positive and no sign-sensitive term is dropped. The finite mass estimate is multiplied only by genuine nonnegative li values.',
'Every actual a satisfies N/a>=N^(1/3), by the owned literal U8 endpoint proof. The real power tends to infinity, uniformly putting every actual li argument above two beyond a threshold chosen before a. Thus li positivity is internally paid for the final theorem, although the intermediate finite estimates expose the natural argument>=2 condition.',
'Actual Products8 subset Icc 1 N follows from positivity and a<N^(2/3)<=N for N>=1. The generic proved crude true-li upper bound and phi(a)<=a in the correct inverse direction, plus the finite reciprocal-totient sum, give LiMainMass8<=(4/log2)*N*(1+log N). This is an error estimate only, not the leading-one asymptotic.',
'For S subset Icc 1 N, the absolute gate error is at most (256/log2)*N^(4583/5000)*(log N)^2 for large N. The identity 4583/5000=1-417/5000 is exact, and theta<1 is paid by norm_num. The existing genuine PowerErrorBudget proves arbitrary epsilon*singularNormalization; no core bound, current main term, parity, hLower/hUpper or adopted constant is a caller premise.',
'The final quantifier order is epsilon>0, eventually N, then every cap,z,L,S with only S subset positive moduli through N. It therefore allows the actual cap/roughness/level/modulus set to be chosen after N. The source-independent density factor8 and all finite-count/Pan/harmonic assembly obligations remain separate and are not claimed by this leaf.'
]
api_specs=[
(root/'ImbalancedChen/CurrentChenMeanLedger.lean',115,125,'The actual U8 selector and generic Y9 selector have identical predicates; original literal endpoints are supplied by U8ProductPan'),
(root/'ImbalancedChen/CurrentChenUpsilon9ProductCoefficient.lean',26,33,'Generic ordered-prime data, applied definitionally to the actual U8 selector'),
(root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean',99,144,'Actual U8 product power bounds and exact same zero-one coefficient identity'),
(root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean',218,229,'Actual U8 moving li argument lower bound N^(1/3)'),
(root/'ImbalancedChen/CurrentChenUpsilon9CoprimeGateBudget.lean',34,118,'Already proved generic true-li linear bound and actual prime-divisor reciprocal-totient sum, no arbitrary distribution premise'),
(providers/'mathlib/Mathlib/Data/Nat/Totient.lean',340,354,'Fixed actual Nat.totient_super_multiplicative; cofactor coprimality is unnecessary'),
(root/'ImbalancedChen/ActualSmallRosser.lean',117,125,'Actual signed upper Rosser absolute bound for all cap,z,L,d'),
(providers/'goldbach/MathlibNt/SieveTheory/Arithmetic/LiuLogarithmicIntegral.lean',69,81,'Genuine true-li nonnegativity at x>=2 and nonnegative actual normalization constant'),
(root/'ImbalancedChen/TotientReciprocalBudget.lean',235,241,'Finite actual reciprocal-totient subset bound'),
(providers/'mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',742,749,'Actual rpow<=self at N>=1, exponent2/3<=1'),
(root/'ImbalancedChen/PowerErrorBudget.lean',45,91,'Proved sublinear power/log error budget in the original normalization')]
apis=[{'path':str(p),'file_sha256':sha(p),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in api_specs]
gate_audit=state/'audits/20261015T190546514074Z/receipt.json';gate_ar=json.loads(gate_audit.read_text());gate_source=root/'ImbalancedChen/CurrentChenUpsilon9CoprimeGateBudget.lean'
assert gate_ar['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and gate_ar['targets']['ImbalancedChen.CurrentChenUpsilon9CoprimeGateBudget']==sha(gate_source)
common={'status':'SOURCE_ONLY_AUTHOR_REVIEW_PENDING_NONAUTHOR_REVIEW_AND_RUNTIME','reviewer':'/root/lower_resume (source author)','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':module,'source_sha256':sha(source),'no_Lean_or_build_invoked':True,'no_kernel_owned_or_cache_acceptance_claimed':True,'bytecode_writes_disabled':True}
inventory=sorted((m,hashes[m]) for m in candidate)
dag={**common,'method':'Fresh proper Lean header walk with pinned grammar, all manifest provider roots plus Lean/Lake, implicit Init/public/meta/import-all. Header/source DAG only.','parser_path':str(parser_path),'parser_sha256':sha(parser_path),'direct_imports':['ImbalancedChen.CurrentChenUpsilon8ProductPan'],'baseline_source_sha256':sha(parent),'baseline_resolved':len(baseline),'candidate_resolved':len(candidate),'new_project_vs_parent':sorted(candidate-baseline),'new_foreign_vs_parent':[],'unresolved':missing,'parser_findings':findings,'closure_module_sha_inventory_sha256':hashlib.sha256(json.dumps(inventory).encode()).hexdigest(),'pins':pins,'providers_current_pin_HEAD_and_clean':provider_checks,'external_closure_kernel_replay':False}
sem={**common,'path':str(source.relative_to(root)),'declaration_count':10,'definition_count':3,'theorem_count':7,'all_complete_headers_definitions_and_proofs':ds,'type_extraction':'Theorems split only at actual := by; definitions use top-level assignment outside all bracketed named arguments.','full_current_source':source.read_text(),'parent':{'path':str(parent.relative_to(root)),'sha256':sha(parent),'owned_receipt_path':str(parent_audit.relative_to(root)),'owned_receipt_sha256':sha(parent_audit),'status':audit['status'],'scope':'This is the parent own-object acceptance only, not full importedclosure replay.'},'reused_generic_gate_source':{'path':str(gate_source.relative_to(root)),'sha256':sha(gate_source),'owned_receipt_path':str(gate_audit.relative_to(root)),'owned_receipt_sha256':sha(gate_audit)},'relative_DAG_delta':{'new_local':[module],'new_foreign':[]},'semantic_review':claims,'fixed_API_source_evidence':apis,'explicit_existing_PowerErrorBudget_import_path':['CurrentChenUpsilon8ProductPan','CurrentChenUpsilon8PrimeSource','CurrentChenUpsilon9PrimeSource','CurrentChenMeanLedger','CurrentChenSummedBridge','PowerErrorBudget'],'pins':pins,'provider_current_checks':provider_checks,'forbidden_or_option_hits':forbidden,'findings':[],'evidence_boundary':'Source author review only. Independent full-source review, actual strict first compile and complete original owned types/inventory/axiom acceptance are separate gates. No count core, density, Pan budget, hLower/hUpper or adopted constant is a caller premise or claimed conclusion.'}
outputs=[]
for basename,data in [('20261016-U8CoprimeGateBudget-owner-semantics.json',sem),('20261016-U8CoprimeGateBudget-owner-proper-dag.json',dag)]:
    p=out/basename
    with p.open('x',encoding='utf8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
    outputs.append({'path':str(p.relative_to(root)),'sha256':sha(p)})
assert sha(source)==common['source_sha256'] and sha(parent)==dag['baseline_source_sha256']
print(json.dumps({'source_sha256':sha(source),'reports':outputs,'declarations':10,'definitions':3,'baseline_resolved':len(baseline),'candidate_resolved':len(candidate),'new_local':sorted(candidate-baseline),'new_foreign':[]},indent=2))