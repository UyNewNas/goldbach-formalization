import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json, re, hashlib, subprocess
from datetime import datetime, timezone
root = Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
out = root / '.lake/proof-continuation/source-reviews'
providers = {'goldbach': Path('/home/slava/codex-lean-ve/native-packages/goldbach'), 'mathlib': Path('/home/slava/codex-lean-ve/native-packages/mathlib')}
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s):
    chars=list(s); i=0; depth=0; string=False
    while i<len(s):
        if depth:
            if s.startswith('/-',i): chars[i]=chars[i+1]=' '; depth+=1; i+=2
            elif s.startswith('-/',i): chars[i]=chars[i+1]=' '; depth-=1; i+=2
            else:
                if chars[i]!='\n': chars[i]=' '
                i+=1
        elif string:
            if s[i]=='\\': i+=2
            elif s[i]=='"': string=False; i+=1
            else: i+=1
        elif s.startswith('/-',i): chars[i]=chars[i+1]=' '; depth=1; i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i)
            if j<0: j=len(s)
            chars[i:j]=[' ']*(j-i); i=j
        elif s[i]=='"': string=True; i+=1
        else: i+=1
    assert depth==0
    return ''.join(chars)
def imports(p): return re.findall(r'(?m)^\s*(?:public\s+)?import\s+(\S+)', strip_comments(p.read_text()))
def identity(p, base=root): return {'path':str(p.relative_to(base)), 'sha256':sha(p), 'imports':imports(p)}
def headers(p):
    raw=p.read_text(); clean=strip_comments(raw)
    ds=list(re.finditer(r'(?m)^(private\s+)?(theorem|lemma|def|abbrev|axiom|opaque)\s+([^\s({:]+)',clean)); result=[]
    for i,m in enumerate(ds):
        stop=ds[i+1].start() if i+1<len(ds) else len(clean)
        assignment=clean.find(':=',m.end(),stop)
        assert assignment>=0, (p,m[3])
        body=clean[assignment+2:stop]
        body=re.split(r'(?m)^end(?:\s.*)?$',body,maxsplit=1)[0].strip()
        d={'name':m[3],'kind':m[2], 'private':bool(m[1]), 'line':clean[:m.start()].count('\n')+1, 'complete_header':clean[m.start():assignment].strip(), 'complete_proof_or_definition_body':body}
        if m[2]=='def': d['complete_definition']=clean[m.start():assignment+2]+ '\n'+body
        result.append(d)
    return result
manifest=json.loads((root/'lake-manifest.json').read_text())
pin_manifest=json.loads((root/'verification/proof-continuation/2026-10-15/pins/lake-manifest.json').read_text())
assert manifest==pin_manifest
provider_checks=[]
for name,p in providers.items():
    expected=next(x['rev'] for x in manifest['packages'] if x['name']==name)
    actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
    diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert actual==expected and diff.returncode==0, (name,actual,expected,diff.returncode)
    provider_checks.append({'name':name,'path':str(p),'expected_rev':expected,'actual_head':actual,'git_diff_HEAD_tracked_exit_code':diff.returncode,'head_matches_pin':True,'tracked_source_clean':True,'untracked_objects_not_used_as_acceptance':True})
pin_bytes=[]
for rel in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
    p=root/rel; archived=root/'verification/proof-continuation/2026-10-15/pins'/rel
    assert p.read_bytes()==archived.read_bytes()
    pin_bytes.append({'path':rel,'sha256':sha(p),'archived_pin_path':str(archived.relative_to(root)),'archived_sha256':sha(archived),'exact_bytes_match':True})
paths={
 'odd':['ActualExtendedThirdCompactResidualProfile','ActualPrimeBoxOwnCubeResidual','ActualRosserResidualDensity','ActualRosserCompactNormalization','ActualRosserCompactLimits','ActualRosserCompactBoxBounds','ActualRosserLocalBoxThreshold','ActualRosserBoxUnionUniformity','ActualRosserOddBoxUnion','ActualRosserOddBoxFamily','ActualRosserOddBox'],
 'even':['ActualExtendedThirdCompactResidualProfile','ActualPrimeBoxOwnCubeResidual','ActualRosserResidualDensity','ActualRosserCompactNormalization','ActualRosserCompactLimits','ActualRosserCompactBoxBounds','ActualRosserLocalBoxThreshold','ActualRosserBoxUnionUniformity','ActualRosserEvenBoxUnion','ActualRosserEvenBoxFamily','ActualRosserEvenBox'],
 'euler':['ActualExtendedThirdCompactResidualProfile','ActualPrimeBoxOwnCubeResidual','ActualRosserResidualDensity','ActualRosserCompactNormalization','ActualRosserCompactLimits','ActualRosserCompactBoxBounds','ActualRosserLocalBoxThreshold','ActualRosserBoxUnionUniformity','ActualPrimeBoxOuterUniformity','ActualPrimeBoxEulerLower']}
path_bindings={}
for key,mods in paths.items():
    entries=[identity(root/'ImbalancedChen'/f'{m}.lean') for m in mods]
    for a,b in zip(entries,mods[1:]): assert 'ImbalancedChen.'+b in a['imports'], (a['path'],b)
    path_bindings[key]={'direction':'target imports current frontier through each adjacent literal project import','path':entries,'scope':'Headers and current SHA only for intermediate path nodes; not a full source/kernel/closure audit of those intermediates.'}
api_specs=[
 ('goldbach','MathlibNt/SieveTheory/LinearSieve/RosserChains.lean',183,216,'LowerRosserBoundaryChain and lowerRosserBoundarySet_iff_sorted_chain'),
 ('goldbach','MathlibNt/SieveTheory/LinearSieve/RosserChains.lean',221,227,'UpperRosserBoundaryChain'),
 ('goldbach','MathlibNt/SieveTheory/LinearSieve/UpperRosserDensity.lean',280,311,'upperRosserBoundarySet_iff_sorted_chain'),
 ('mathlib','Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean',145,157,'Finset.prod_lt_prod_of_nonempty argument order'),
 ('mathlib','Mathlib/Algebra/BigOperators/Fin.lean',720,736,'List.prod_take_ofFn'),
 ('mathlib','Mathlib/Data/List/OfFn.lean',32,41,'List.get_ofFn'),
 ('mathlib','Mathlib/Data/List/OfFn.lean',116,126,'List.pairwise_ofFn'),
 ('mathlib','Mathlib/Data/Finset/Sort.lean',87,96,'List.toFinset_sort'),
 ('mathlib','Mathlib/Order/WellFounded.lean',231,243,'StrictAnti.range_inj'),
 ('mathlib','Mathlib/Order/Fin/Basic.lean',155,167,'Fin.antitone_iff_succ_le'),
 ('mathlib','Mathlib/Algebra/Group/Nat/Even.lean',34,43,'Nat.not_even_iff'),
 ('mathlib','Mathlib/Algebra/Ring/Parity.lean',252,271,'Nat.odd_iff'),
 ('mathlib','Mathlib/Algebra/Order/Floor/Defs.lean',146,164,'Nat.ceil_le and Nat.lt_ceil'),
 ('goldbach','MathlibNt/SieveTheory/Arithmetic/PrimeReciprocalLogScale.lean',199,225,'tendsto_primeReciprocalLogInterval proved from actual Mertens second theorem'),
 ('goldbach','MathlibNt/SieveTheory/Arithmetic/MertensTheorem.lean',60,80,'mertens_second_theorem definition bridge to proved ANT supplier'),
 ('goldbach','MathlibNt/SieveTheory/Arithmetic/MertensTheorem.lean',850,878,'mertens_product_formula definition bridge to proved ANT supplier'),
 ('goldbach','AnalyticNumberTheory/Mertens/Theorems.lean',1,41,'primeProduct_mertens_nat has no caller analytic premise')]
apis=[]
for prov,rel,lo,hi,role in api_specs:
    p=providers[prov]/rel; lines=p.read_text().splitlines()
    apis.append({'provider':prov,'path':rel,'file_sha256':sha(p),'lines':[lo,hi],'role':role,'literal_fixed_source_excerpt':'\n'.join(lines[lo-1:hi])})
expected={
 'ActualRosserOddBox':'2beffd8af22239e3a5428713c614e8e37bcbb300b16c950ff254d2c9ba031888',
 'ActualRosserEvenBox':'55287bfc6e22bfe8bb7f5d00a8698f4030c4c1cea23468c4edb72bea30a2bf52',
 'ActualPrimeBoxEulerLower':'adc0657ea574d58a0364423062c556119a06380b6edcdb31d6175ca3f99083cb'}
notes={
 'ActualRosserOddBox':{
 'key':'odd', 'claims':['The actual tuple carrier retains primality, non-divisibility by the same target N, lower-inclusive and upper-strict powers. Adjacent separated exponent boxes make p strictly decreasing even when exponent walls coincide.','Tail cardinality is exactly 2*k; injectivity uses the full coordinate range of strictly decreasing tuples. Equal tail sets across ranks imply equal ranks. No caller injectivity is assumed in the main boundary theorem.','Every selected prime is below N^u and thus belongs to the actual cap-covered prime carrier. hprod and every even-index hprefix pay the actual strict upper Rosser chain products. The k=0 empty tail uses beta>0 to pay 1<N^beta.','The terminal crossing is weak N^beta<=tail product*least^3; the active product and prefix conditions are strict. Nat.lt_ceil and Nat.ceil_le transfer exactly to ceil(N^beta), not floor+1.','The least prime is proved absent from the tail and below every tail prime. The native sorted-chain equivalence pays the actual upper boundary predicate, not a replacement tuple predicate.'],
 'connection':'ActualRosserOddBoxFamily injects the finite disjoint union of actual tuple boxes into the same positive actual upper boundary expansion. Its boundary weight agrees with actualPrimeBoxEulerMass by the exact tail product identity. Selected nonnegative terms give a LOWER bound on actualSmallRosserPlusDensity/V with constant 1 counted once. Subsequent box-union/local compact limits feed actual normalized residual densities used by OwnCube and Residual051.',
 'supplier':'No analytic estimate is an assumption or is called in this leaf. Its main theorem is finite geometry. Analytic lower mass is independently supplied downstream by ActualPrimeBoxEulerLower, not silently presumed here.',
 'checks':['Tail product/card/range identities including empty tail','Boundary-map injOn and cross-rank disjointness','All actual coordinate prime/target/cap memberships','Strict prefix products and weak terminal crossing','Canonical decreasing sort and exact natural ceiling level']},
 'ActualRosserEvenBox':{
 'key':'even', 'claims':['The actual tuple carrier retains the same target-prime exclusions and strict upper endpoints. Separated boxes make the tuple strictly decreasing; its singleton-tail k=0 case is genuine and needs no internal odd-index test.','Tail cardinality is 2*k+1; exact product, range, injOn and cross-rank results match the odd-tail native lower boundary. No caller injection certificate is substituted for the main finite proof.','The nonempty tail gives the strict active product. Odd-index exponent tests give each native lower chain prefix; native uses not-Even, and fixed Nat.not_even_iff plus Nat.odd_iff converts it to Odd.','The weak terminal shell and all strict active/prefix inequalities transfer to the same literal ceil(N^beta). The least-prime/tail distinction and strict order are paid before invoking lowerRosserBoundarySet_iff_sorted_chain.','The _hbeta argument is explicitly stronger than necessary in this nonempty-tail proof. It is not a hidden result being assumed and is not weakened or removed by this review.'],
 'connection':'ActualRosserEvenBoxFamily maps disjoint actual even-prime boxes into nonnegative terms of the exact actual LOWER Rosser boundary LOSS expansion. Because actualMinus/V=1-total_loss, selected positive losses yield an UPPER bound for the actual lower density. This is the even layer needed alongside odd layers for the downstream actual residual-density limit, OwnCube and Residual051.',
 'supplier':'No analytic estimate is assumed or called in this leaf. It proves a finite lower-boundary inclusion. Euler weighted mass is supplied downstream by the separately proved EulerLower threshold.',
 'checks':['All tail identities for odd tail length including singleton','Strict actual ordering and injection','Odd versus native not-Even prefix convention','Total/prefix strictness, terminal weak inequality, exact ceil','Correct LOSS sign in downstream actual lower-density estimate'],
 'unexecuted_tactic_risk':'Line 195 all_goals rfl follows convert in the dependent Fin/list index conversion. Whether convert leaves equality goals, and whether strict lint treats that line as unused, requires actual elaboration. No diagnostic has been produced or inferred here; this is not a confirmed API or mathematical blocker.'},
 'ActualPrimeBoxEulerLower':{
 'key':'euler','claims':['Covered actual Euler products are identified with finiteSieveDensity at Nat.ceil cutoff. Even N excludes prime 2 from the actual carrier and proves the required nonnegative/positive factors. This makes increasing-cutoff antitonicity valid.','actualPrimeBoxEulerMass sums genuine target-deleted prime tuples with product 1/(p_i-1), multiplied by actual V(p_j)/V(N^u). The strict numerator cutoff is at the actual coordinate p_j. The leaf does not assert that j is least or that the tuple is a boundary.','On each actual tuple p_j<N^(b_j), hence V(N^(b_j))<=V(p_j). The denominator is positive, and the reciprocal-prime weight nonnegative. Summation gives the endpoint-ratio lower bound with the correct direction.','The proved actual tuple mass tends to product log(b_i/a_i). Its one-prime parent explicitly pays target-divisor deletion, changing 1/p to 1/(p-1), and both half-open endpoint atoms against an o(1) power error.','The actual finite-sieve Euler ratio limit is u/b_j on positive even targets. It is derived from a fixed proved Mertens product formula and paid center Euler tail, then cancels the singular series and exp(-gamma), not from an assumed Rosser density.','Multiplying the two proved limits gives one N0>=2 before N, parity and every covering cap. The cap parameter occurs only after N0 and is eliminated by exact actual Euler identities; eta>0 gives the correct final lower inequality.'],
 'connection':'Both actual odd/even BoxFamily modules consume this weighted-box threshold at their terminal least coordinate after the finite boundary geometry is proved. ActualPrimeBoxOuterUniformity also extends the fixed-u threshold to larger outer exponents by denominator monotonicity. Those finite threshold estimates enter ActualRosserBoxUnionUniformity and then the actual compact residual density chain behind OwnCube and Residual051.',
 'supplier':'Analytic suppliers are explicit PROVED parent theorems: tendsto_actualPrimeBoxMass and tendsto_finiteSieveDensity_power_ratio. The latter uses MathlibNt.SieveTheory.MertensTheorem.mertens_product_formula, whose body invokes AnalyticNumberTheory.Mertens.primeProduct_mertens_nat inside the same pinned goldbach repository. The reciprocal-prime limit uses the corresponding proved mertens_second_theorem. No caller analytic asymptotic, current hLower/hUpper, or target Rosser estimate occurs in these four declarations. This source-only review does not replay the full ANT proof closure.',
 'checks':['Same actual carrier, target exclusions and endpoint conventions','Euler cutoff antitonicity and positive denominator','Nonnegative tuple weight and summed endpoint lower bound','Real leading constants and actual singular-series cancellation','Threshold quantifier order uniform in later even N and every cap']}}
parent_semantics={
 'ActualRosserBoundaryExpansion':'Exact actual plus-density/Euler ratio =1+sum of nonnegative native upper boundary terms, using ceil real level; selecting positive boundary terms gives a lower bound. Full direct parent source read.',
 'ActualLowerRosserBoundaryExpansion':'Exact actual minus-density/Euler ratio =1-sum of nonnegative native lower boundary terms; finite recurrence and signs are proved internally. Full direct parent source read.',
 'ActualPrimeBoxMass':'Literal Fintype.piFinset actual prime tuples; mass factorizes by finite distributivity, nonnegative weights, proved actual reciprocal-prime limit, strict separated-box order and injectivity/totient identities. Full direct parent source read.',
 'FullPowerEulerNormalization':'Actual strict endpoint ceil(N^a)-1, proved Mertens leading exp(-gamma), paid target-center Euler tail and singular-series normalization yield proved actual power ratio b/a along positive even targets. Full direct parent source read.',
 'RoughPowerParameters':'Actual Euler positivity follows from even N eliminating p=2 and actual prime membership. Unrelated rough-asymptotic statements are not premises of EulerLower. Full direct parent source read.',
 'SieveDimensionComparison':'Finite Euler product identities and nonnegative factors give finiteSieveDensity antitonicity for even N. No analytic supplier premise. Full direct parent source read.'}
all_results=[]
for module,expected_sha in expected.items():
    p=root/'ImbalancedChen'/f'{module}.lean'; assert sha(p)==expected_sha
    declarations=headers(p); assert len(declarations)==(4 if module=='ActualPrimeBoxEulerLower' else 9)
    direct=[]
    for imp in imports(p):
        if imp.startswith('ImbalancedChen.'):
            q=root/(imp.replace('.','/')+'.lean'); ent=identity(q)
            ent['review_of_relevant_parent_semantics']=parent_semantics[q.stem]
            ent['all_complete_parent_headers_and_definition_bodies']=headers(q)
        else:
            prov='mathlib' if imp.startswith('Mathlib.') else 'goldbach'; q=providers[prov]/(imp.replace('.','/')+'.lean')
            ent=identity(q,providers[prov]); ent['provider']=prov
            ent['review_scope']='Relevant imported APIs and precise argument conventions checked; not a review of every declaration in this whole Mathlib module.'
        direct.append(ent)
    scans={}
    scanned=[p]+[root/x['path'] for x in direct if x.get('provider') is None]
    for q in scanned:
        clean=strip_comments(q.read_text())
        hits=[]
        for pattern in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*axiom\b',r'(?m)^\s*unsafe\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
            for m in re.finditer(pattern,clean): hits.append({'line':clean[:m.start()].count('\n')+1,'token':m.group(0)})
        scans[str(q.relative_to(root))]={'sha256':sha(q),'uncommented_forbidden_or_option_hits':hits}
    assert all(not x['uncommented_forbidden_or_option_hits'] for x in scans.values())
    data={
      'schema':'independent-frontier-full-source-review-v1','status':'SOURCE_ONLY_FULL_INDEPENDENT_REVIEW_NO_CONFIRMED_MATH_OR_FIXED_API_BLOCKER',
      'reviewer':'/root/lower_resume (not the author of these three historical Rosser leaves)',
      'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
      'scope':'One of the three explicitly authorized current project frontier sources behind ActualPrimeBoxOwnCubeResidual dd140 and ActualExtendedThirdCompactResidualProfile 051. No whole-closure/foreign source walk performed.',
      'candidate':{'module':'ImbalancedChen.'+module,**identity(p),'declaration_count':len(declarations),'definition_count':sum(x['kind']=='def' for x in declarations),'all_complete_types_definitions_and_proofs':declarations,'full_current_raw_source':p.read_text()},
      'direct_parents':direct,'fixed_provider_HEAD_and_tracked_source_checks':provider_checks,'exact_config_pin_bytes':pin_bytes,
      'project_head_at_review':sys.argv[1],
      'literal_fixed_APIs_read':apis if module=='ActualPrimeBoxEulerLower' else apis[:13],
      'mathematical_review':notes[module],
      'actual_target_dependency_path':path_bindings[notes[module]['key']],
      'source_token_scan':scans,
      'hidden_supplier_review':'All complete candidate headers, definitions and proof bodies were read, as were the listed project direct parents. No sorry/admit/axiom/unsafe/native_decide or option override was found in these current sources. EulerLower explicit proved analytic dependencies are named above. Parent transitive axioms and unrelated imported closures were not kernel-replayed by this source-only review.',
      'findings':[],
      'acceptance_boundary':{'lean_executed':False,'lake_executed':False,'source_modified':False,'objects_installed_or_rebound':False,'foreign_bootstrap':False,'cache_acceptance':False,'owned_acceptance':False,'full_transitive_axiom_audit':False,'runtime_source_object_mismatch_resolved':False,'full_hLower_or_hUpper_proved':False,'note':'This independent source review cannot certify or repair the runtime-observed source/object mismatch. Every actual object/source gate, strict elaboration/lint, serialized/env inventory, complete owned types and transitive axiom check remains the sole runtime owner task.'}}
    dest=out/f'20261016-{module}-lower-independent-semantics.json'
    with dest.open('x',encoding='utf8',newline='\n') as f: json.dump(data,f,ensure_ascii=False,indent=2); f.write('\n')
    all_results.append({'module':module,'source_sha256':sha(p),'report':str(dest.relative_to(root)),'report_sha256':sha(dest),'declarations':len(declarations),'definitions':data['candidate']['definition_count']})
print(json.dumps(all_results,ensure_ascii=False,indent=2))