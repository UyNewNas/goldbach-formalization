import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,importlib.util,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
module='ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget'
source=root/'ImbalancedChen/CurrentChenUpsilon8SourceErrorBudget.lean'
draft=out/'drafts/CurrentChenUpsilon8SourceErrorBudget.source-draft.txt'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
ns=ast.parse(helper.read_text());wanted={'sha','uncomment','imports','assignment_at_top','declarations'}
exec(compile(ast.Module(body=[n for n in ns.body if isinstance(n,ast.FunctionDef) and n.name in wanted],type_ignores=[]),str(helper),'exec'))
assert sha(draft)=='f8a7e49a7e802d1dfc6459ee5ef0df4086f53e24b05464be05ffc59545aa7d29'
assert source.is_file() and source.read_bytes()==draft.read_bytes(), 'Only run after publication release and installing the authorized exact single source leaf.'
parent=root/'ImbalancedChen/CurrentChenUpsilon8ProductPan.lean';assert sha(parent)=='80621797c21adc263fc702e07a13c0b0b543a40f34ca2658a7fa281e1af12b11'
parent_audit=state/'audits/20261015T215816603875Z/receipt.json';audit=json.loads(parent_audit.read_text())
assert audit['status']=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and audit['targets']['ImbalancedChen.CurrentChenUpsilon8ProductPan']==sha(parent)
ds=declarations(source.read_text());assert len(ds)==13 and sum(d['kind']=='def' for d in ds)==2
assert imports(source.read_text())==['ImbalancedChen.CurrentChenUpsilon8ProductPan']
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py'
assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914'
spec=importlib.util.spec_from_file_location('u8_source_error_frozen_header_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
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
'The two new finite selectors filter the literal actual U8 PrimeTriples. P=N-p1*p2*r is the ORIGINAL Goldbach prime, while r is its multiplicative prime quotient. All original first/second prime bands, inclusive p2 lower ownership, strict sqrt(N/p1) cap, r>=p2 roughness, target-prime exclusion and outer pair labels remain.',
'Every literal prefix product is positive and <=the already proved natural PanUpper8, hence PrefixProducts.card<=PanUpper8<=N^(2/3). The actual unit carrier maps injectively by its actual pair product into those products using the already proved U8 selector injection, proving its true finite cardinal<=N^(2/3).',
'The actual whole triple map x->(p1*p2,P) is injected using real product uniqueness only on the original pair selector, then actual strict a*r<N and a*s<N to undo Nat subtraction and a>0 to cancel multiplication. No opaque product equality or truncated subtraction is assumed.',
'Small original P is prime and therefore positive. The original inclusive cap P<=N^(1/5) places it in Ioc 0 floor(N^(1/5)), while the positive actual prefix is in Ioc 0 PanUpper8. The proved true map injection bounds actual small-triple card by PanUpper8*floor(N^(1/5))<=N^(2/3+1/5)=N^(13/15), with constant ONE and no caller count envelope.',
'The small and large P filters partition every actual PrimeTriple exactly, and the owned prime-or-unit equality gives literal currentUpsilon8=Large.card+Small.card+Unit.card for all N. This is an exact source dictionary, not a weakened surrogate count.',
'For every epsilon>0, the proved PowerErrorBudget at c=1, theta=13/15 and theta=2/3, k=0 supplies thresholds using epsilon/2. Adding those paid errors gives one eventual epsilon*singularNormalization bound. The threshold precedes N; no parity, main term or analytic supplier is a caller premise.',
'Eventual positive genuine singularNormalization and the arbitrary-positive epsilon budget prove the actual total error divided by that normalization tends to zero. The exact source partition gives the same zero limit for (original currentUpsilon8-Large.card)/normalization.',
'This pays the actual unit and small original Goldbach-prime finite source errors only. The U8 coprime gate, signed Pan/Rosser error, actual density and harmonic kernel, ordinary U8 upper mean, adopted constants and full hLower/hUpper remain separate obligations.'
]
api_specs=[(providers/'mathlib/Mathlib/Data/Finset/Card.lean',424,433,'card_le_card_of_injOn requires actual MapsTo plus actual source InjOn'),(providers/'mathlib/Mathlib/Order/Interval/Finset/Nat.lean',79,88,'Exact positive interval card #(Ioc0M)=M'),(providers/'mathlib/Mathlib/Algebra/Order/Floor/Defs.lean',136,144,'Nat.le_floor_iff preserves the inclusive small-prime cap'),(root/'ImbalancedChen/PowerErrorBudget.lean',40,93,'Proved arbitrary epsilon power-log error budget, not a caller supplier'),(root/'ImbalancedChen/SingularSeries.lean',130,156,'Actual normalization diverges and is eventually positive')]
apis=[{'path':str(p),'file_sha256':sha(p),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in api_specs]
common={'status':'SOURCE_ONLY_AUTHOR_REVIEW_PENDING_NONAUTHOR_REVIEW_AND_RUNTIME','reviewer':'/root/lower_resume (source author)','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':module,'source_sha256':sha(source),'no_Lean_or_build_invoked':True,'no_kernel_owned_or_cache_acceptance_claimed':True,'bytecode_writes_disabled':True}
inventory=sorted((m,hashes[m]) for m in candidate)
dag={**common,'method':'Fresh proper Lean header walk with pinned grammar, all manifest provider roots plus Lean/Lake, implicit Init/public/meta/import-all. Header/source DAG only.','parser_path':str(parser_path),'parser_sha256':sha(parser_path),'direct_imports':['ImbalancedChen.CurrentChenUpsilon8ProductPan'],'baseline_source_sha256':sha(parent),'baseline_resolved':len(baseline),'candidate_resolved':len(candidate),'new_project_vs_parent':sorted(candidate-baseline),'new_foreign_vs_parent':[],'unresolved':missing,'parser_findings':findings,'closure_module_sha_inventory_sha256':hashlib.sha256(json.dumps(inventory).encode()).hexdigest(),'pins':pins,'providers_current_pin_HEAD_and_clean':provider_checks,'external_closure_kernel_replay':False}
sem={**common,'path':str(source.relative_to(root)),'declaration_count':13,'definition_count':2,'all_complete_headers_definitions_and_proofs':ds,'type_extraction':'Theorems split only at actual := by; definitions use top-level assignment outside all bracketed named arguments.','full_current_source':source.read_text(),'parent':{'path':str(parent.relative_to(root)),'sha256':sha(parent),'owned_receipt_path':str(parent_audit.relative_to(root)),'owned_receipt_sha256':sha(parent_audit),'status':audit['status'],'scope':'This is the parent own-object acceptance only, not full importedclosure replay.'},'relative_DAG_delta':{'new_local':[module],'new_foreign':[]},'semantic_review':claims,'fixed_API_source_evidence':apis,'explicit_existing_PowerErrorBudget_import_path':['CurrentChenUpsilon8ProductPan','CurrentChenUpsilon8PrimeSource','CurrentChenUpsilon9PrimeSource','CurrentChenMeanLedger','CurrentChenSummedBridge','PowerErrorBudget'],'pins':pins,'provider_current_checks':provider_checks,'forbidden_or_option_hits':forbidden,'findings':[],'evidence_boundary':'Source author review only; independent full-source review, actual strict first compile and complete original owned types/inventory/axiom acceptance are separate gates. No caller count envelope, hLower/hUpper or adopted-constant statement is assumed or asserted.'}
outputs=[]
for basename,data in [('20261016-U8SourceErrorBudget-owner-semantics.json',sem),('20261016-U8SourceErrorBudget-owner-proper-dag.json',dag)]:
    p=out/basename
    with p.open('x',encoding='utf8',newline='\n') as f:json.dump(data,f,ensure_ascii=False,indent=2);f.write('\n')
    outputs.append({'path':str(p.relative_to(root)),'sha256':sha(p)})
assert sha(source)==common['source_sha256'] and sha(parent)==dag['baseline_source_sha256']
print(json.dumps({'source_sha256':sha(source),'reports':outputs,'declarations':13,'definitions':2,'baseline_resolved':len(baseline),'candidate_resolved':len(candidate),'new_local':sorted(candidate-baseline),'new_foreign':[]},indent=2))