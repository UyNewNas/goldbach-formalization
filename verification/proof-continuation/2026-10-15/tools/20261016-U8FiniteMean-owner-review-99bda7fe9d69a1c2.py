import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,importlib.util,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
module='ImbalancedChen.CurrentChenUpsilon8FiniteMean';source=root/'ImbalancedChen/CurrentChenUpsilon8FiniteMean.lean'
assert hashlib.sha256(source.read_bytes()).hexdigest()=='da4d9c59126cc173e38182e4bcc060a6ad082b103906b7c17c8cbed363e2172b'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';tree=ast.parse(helper.read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','uncomment','imports','assignment_at_top','declarations'}],type_ignores=[]),str(helper),'exec'))
parent_names=['ImbalancedChen.CurrentChenUpsilon8CoprimeGateBudget','ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget','ImbalancedChen.CurrentChenUpsilon9FiniteMean']
parent_shas=['c4f5a801eadd6128f088b99cd8128602aeba1d0d8fa2a24906cd3e9cd387e761','9d6cb563579a743fd2d5bdcbef19714391d221648ffa3c1bf7b6a2b483b2d52e','5cb35f5ff5e3421ec9b2b662b8c60d99ce407e6e4d7a6620c183ae89976981ec']
assert imports(source.read_text())==parent_names
ds=declarations(source.read_text());assert len(ds)==16 and sum(d['kind']=='def' for d in ds)==3
assert [d['name'] for d in ds if d['kind']=='def']==['currentChenUpsilon8PrefixAPCount','currentChenUpsilon8PanError','currentChenUpsilon8PanRosserError']
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
spec=importlib.util.spec_from_file_location('u8_finite_frozen_header_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
packages=json.loads((root/'lake-manifest.json').read_text())['packages'];providers=Path('/home/slava/codex-lean-ve/native-packages');std=Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux');paths={};heads={};hashes={}
gate_script=out/'drafts/20261016-U8CoprimeGateBudget-owner-review.py';gtree=ast.parse(gate_script.read_text())
exec(compile(ast.Module(body=[n for n in gtree.body if isinstance(n,ast.FunctionDef) and n.name in {'locate','read','walk'}],type_ignores=[]),str(gate_script),'exec'))
baseline=set();parent_closures=[]
for name,expected in zip(parent_names,parent_shas):
    seen,missing,findings=walk(name);assert hashes[name]==expected and not missing and not findings
    baseline|=seen;parent_closures.append({'module':name,'sha256':expected,'resolved':len(seen)})
candidate,missing,findings=walk(module);assert not missing and not findings and candidate-baseline=={module}
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for name,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/name)==h
provider_checks=[]
for name in ['goldbach','mathlib']:
    pr=providers/name;expected=next(x['rev'] for x in packages if x['name']==name);actual=subprocess.check_output(['git','-C',str(pr),'rev-parse','HEAD'],text=True).strip();diff=subprocess.run(['git','-C',str(pr),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert actual==expected and diff.returncode==0
    provider_checks.append({'name':name,'manifest_pin':expected,'actual_HEAD':actual,'git_diff_HEAD_tracked_exit_code':diff.returncode})
parent_records=[]
for i,(name,expected) in enumerate(zip(parent_names,parent_shas)):
    ap=state/('audits/20261015T225351728783Z/receipt.json' if i<2 else 'audits/20261015T194819268649Z/receipt.json');ar=json.loads(ap.read_text());assert ar['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar['targets'][name]==expected
    assert ar['inputs_before']==ar['inputs_after'] and ar['inputs_before']['pins']==pins
    obj=state/'lib/lean'/Path(name.replace('.','/')).with_suffix('.olean');assert sha(obj)==ar['inputs_before']['owned_object_parts'][name]['.olean']
    parent_records.append({'module':name,'source_sha256':expected,'object_sha256':sha(obj),'owned_receipt_path':str(ap.relative_to(root)),'owned_receipt_sha256':sha(ap),'status':ar['status'],'before_after_exact':True,'scope':'Own-object stock replay and complete declaration/type/axiom acceptance; no full foreign closure replay claim.'})
forbidden=[];clean=uncomment(source.read_text())
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    forbidden.extend(m.group(0) for m in re.finditer(pat,clean))
assert not forbidden
claims=[
'Exactly three new definitions are supplied: APCount8 on actual U8 products, native PanError8 on the proved U8 Pan interval and actual modulus-independent zero-one coefficient at N mod d, and the full signed actual upper Rosser sum of that error. LiMass8, Defect8 and GateError8 are reused from the true owned U8 gate leaf; source-independent PanActive9 and SwitchedUpperDensity9 are reused without replacement definitions.',
'The exact AP identity reindexes native liuMainPanCoprimeIntervalSum with U8ProductCoefficient_sum. The source is the literal U8 product image, not the U9 image or an arbitrary bounded coefficient. The true multiplier gate Coprime a d stays present. For a non-coprime multiplier, public generic9_primesInAPBelow_eq_zero_of_not_coprime proves the actual AP count is zero from the actual primitive centre N. No equality with a presieve gate is asserted.',
'Canonical residue N mod d has the same actual AP count as residue N by Nat.mod_mod in the true native definition. Finite summation and sub_div give AP8=(LiMass8-Defect8)/phi(d)+PanError8. This identity is exact and requires only N>=1 for the actual coefficient window, plus true Coprime N d.',
'For any signed test G, the full actual lambda-weighted support sum equals its active truncation. Outside d<=Q, nonzero actual upper Rosser weight would force d<Q+1, a contradiction over natural d. This is an exact equality using strict active support, not monotone omission of signed summands. It applies identically to the gate correction and the Pan error.',
'On actual active support, d is positive and Coprime N d. Thus N mod d is a true unit residue, including the d=1 class0; the native finite MaxL bounds the absolute actual eighth Pan error. Actual |lambda|<=1 and MaxL nonnegativity extend the absolute weighted error to all positive moduli through Q without a multiplicity factor.',
'The owned U8ProductPan theorem at U=3 supplies its actual C,B,N0 before epsilon and without any caller window, coefficient or Pan budget. The proof uses C/logN<=epsilon*twinPrimeConstant for large N and the genuine singularNormalization lower bound, paying |PanRosserError8|<=epsilon*H uniformly in cap,z. No distribution supplier or current target main term is a premise.',
'The public generic PrefixPrimeFibre_divisor_card and prefix_sum_upperDivisorSum retain the literal closed a*q<=N endpoint with possible receiver0. The U8 product Fubini theorem sums that already proved generic bridge over every actual eighth product once. It does not substitute an open AP carrier or silently remove receiver0.',
'The exact full weighted AP identity is LiMass8*the original source-independent Density9 minus actual GateError8 on Active9 plus actual PanRosserError8. The actual support supplies the primitive centre condition. Individual signed coefficients are never assumed nonnegative.',
'The owned U8Product806 finite count bound retains the literal eighth source and unit fibres and maps to the generic strict switched prime fibres only after quotient primality. Each actual positive multiplier then uses public generic9_switchedPrimeFibre_card_le_upperDivisorSum_add_cap. The public theorem already proves total divisor-sum nonnegativity before enlarging its strict a*q<N source to the native closed source. Hence the actual finite inequality retains both the receiver ceiling loss and the literal unit fibres.',
'Actual U8 product cardinal<=PanUpper8<=N^(2/3) comes from the now-owned literal source-error leaf and product endpoint proof. At z=N^(1/5), ceil(z)<=2z for N>=1. Their true product is <=2*N^(13/15), without a caller count envelope, extra endpoint factor or weakened selector.',
'For each fixed B>=0, the already imported genuine conductor and log-power bounds give 1<Q+1, N^(1/5)<=Q+1, and Q<=N eventually. The lower cutoff uses exact exponents1/5+3/10=1/2 and the strict floor-add-one inequality. Therefore actual Active9 subset Icc1N is paid internally before the gate budget is invoked.',
'The final epsilon/4 threshold simultaneously pays the actual signed Pan error, the actual signed coprime gate, the true ceiling loss via PowerErrorBudget(c=2,theta=13/15,k=0), and literal units. The units are bounded by the owned sourceErrors epsilon/4 bound because the original small-Goldbach-prime cardinal is nonnegative. No unproved unit or small-prime count bound is supplied by the caller.',
'The final type chooses one B>=0 before every epsilon>0. Its eventual N threshold precedes every cap. It uses the unchanged currentChenUpsilon8 count, true LiMainMass8 and the unchanged explicit source-independent Density9 at z=N^(1/5). No parity is required in this finite statement; the later density8 value, true-li leading-one transport, actual harmonic integral, complete ordinary U8 mean and adopted K are not asserted by this leaf.'
]
api_specs=[
(root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean',127,171,'Exact actual U8 same-coefficient identity and original count upper bound by generic prime fibres plus literal units'),
(root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean',244,263,'Owned actual true-li Pan majorant, inclusive endpoint2/3, fixed C/B/N0 preceding all actual parameters'),
(root/'ImbalancedChen/CurrentChenUpsilon9FiniteMean.lean',33,75,'Public generic native closed prime/AP carrier and finite divisor Fubini, including receiver0'),
(root/'ImbalancedChen/CurrentChenUpsilon9FiniteMean.lean',96,145,'Public generic arbitrary-positive-multiplier switched fibre upper sieve, with proven complete divisor-sum nonnegativity before source extension'),
(root/'ImbalancedChen/CurrentChenUpsilon9FiniteMean.lean',181,196,'Unchanged explicit source-independent actual upper density definition'),
(root/'ImbalancedChen/CurrentChenUpsilon9PanAggregate.lean',51,66,'Public generic zero actual AP count for non-coprime multiplier at primitive centre'),
(root/'ImbalancedChen/CurrentChenUpsilon9PanAggregate.lean',181,188,'Source-independent active-modulus set definition'),
(root/'ImbalancedChen/CurrentChenUpsilon9PanAggregate.lean',213,219,'Public actual positive-modulus active subset'),
(root/'ImbalancedChen/ActualSmallRosser.lean',94,97,'Actual support supplies Coprime d N'),
(root/'ImbalancedChen/ActualSmallRosser.lean',123,137,'Actual signed upper coefficient has abs<=1 and strict nonzero support d<L'),
(root/'ImbalancedChen/CoprimeRecentering.lean',27,49,'True canonical reduced residue set and Nmodd membership iff primitive centre, for every positive d'),
(providers/'goldbach/AnalyticNumberTheory/Sieve/WeightedPan.lean',438,446,'Fixed native AP carrier really uses range(y+1), prime q, closed a*q<=y and product congruence'),
(providers/'goldbach/AnalyticNumberTheory/Sieve/WeightedPan.lean',527,533,'Fixed actual unit residues include class0 at modulus1'),
(providers/'goldbach/MathlibNt/SieveTheory/Liu/Weights/LiuWeight.lean',408,415,'Fixed native true-li-parametric scaled AP error, exact main/phi(d)'),
(providers/'goldbach/MathlibNt/SieveTheory/Liu/LogarithmicIntegral/LiuTrueLiPan.lean',44,49,'Fixed Ioc Pan window and true Coprime a d gate'),
(providers/'goldbach/MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanWangDingSource.lean',259,267,'Finite native unit-residue MaxL, nonempty branch and absolute value'),
(providers/'goldbach/MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanActualErrorEnvelope.lean',66,78,'Generic native MaxL nonnegativity, no analytic supplier'),
(providers/'goldbach/MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanPrimitiveLedgerAssembly.lean',51,87,'Proved genuine conductor bounds and every fixed positive-power log payment'),
(root/'ImbalancedChen/CurrentChenUpsilon8SourceErrorBudget.lean',35,50,'Actual product cardinal<=its true Pan upper endpoint'),
(root/'ImbalancedChen/CurrentChenUpsilon8SourceErrorBudget.lean',162,181,'True original small-plus-unit source error, with epsilon threshold'),
(root/'ImbalancedChen/CurrentChenUpsilon8CoprimeGateBudget.lean',216,274,'Uniform actual signed coprime correction budget, threshold before cap,z,L,S'),
(root/'ImbalancedChen/PowerErrorBudget.lean',45,91,'Actual singular-normalization sublinear power/log budget')]
apis=[{'path':str(p),'file_sha256':sha(p),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in api_specs]
common={'status':'SOURCE_ONLY_AUTHOR_REVIEW_PENDING_NONAUTHOR_REVIEW_AND_RUNTIME','reviewer':'/root/lower_resume (source author)','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':module,'source_sha256':sha(source),'no_Lean_or_build_invoked':True,'bytecode_writes_disabled':True,'no_kernel_owned_or_cache_acceptance_claimed':True}
inventory=sorted((n,hashes[n]) for n in candidate)
dag={**common,'method':'Fresh full proper Lean header walk with pinned grammar over all manifest fixed provider roots plus Lean/Lake; implicit Init, public/meta/import-all preserved. Source DAG only.','parser_path':str(parser_path),'parser_sha256':sha(parser_path),'direct_imports':parent_names,'parent_closures':parent_closures,'baseline_parent_union_resolved':len(baseline),'candidate_resolved':len(candidate),'new_project_vs_parent_union':sorted(candidate-baseline),'new_foreign_vs_parent_union':[],'unresolved':missing,'parser_findings':findings,'closure_module_sha_inventory_sha256':hashlib.sha256(json.dumps(inventory).encode()).hexdigest(),'pins':pins,'providers_current_pin_HEAD_and_clean':provider_checks,'external_closure_kernel_replay':False}
sem={**common,'path':str(source.relative_to(root)),'declaration_count':16,'definition_count':3,'theorem_count':13,'all_complete_headers_definitions_and_proofs':ds,'type_extraction':'Theorem headers end only at actual := by, retaining named arguments and complete types. Definitions end at top-level := outside all bracketed named arguments.','full_current_source':source.read_text(),'parents':parent_records,'relative_DAG_delta':{'new_local':[module],'new_foreign':[]},'semantic_review':claims,'fixed_API_source_evidence':apis,'pins':pins,'providers_current':provider_checks,'forbidden_hits':forbidden,'findings':[],'evidence_boundary':'Complete source-author review only. The three direct parent owned receipts are freshly bound, including both actual U8 leaves which just passed owned225351. This is not acceptance of the new leaf, imported-closure replay or a proof of the full ordinary U8 mean or adopted constants. Non-author full-source review and exact root runtime gate remain required.'}
outputs=[]
for basename,data in [('20261016-U8FiniteMean-owner-semantics.json',sem),('20261016-U8FiniteMean-owner-proper-dag.json',dag)]:
    p=out/basename
    with p.open('x',encoding='utf8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
    outputs.append({'path':str(p.relative_to(root)),'sha256':sha(p)})
assert sha(source)==common['source_sha256']
print(json.dumps({'source_sha256':sha(source),'declarations':16,'defs':3,'theorems':13,'reports':outputs,'parent_union':len(baseline),'candidate':len(candidate),'new_local':sorted(candidate-baseline),'new_foreign':[],'all_direct_parents_fresh_owned':True},indent=2))