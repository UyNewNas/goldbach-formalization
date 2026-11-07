import sys
sys.dont_write_bytecode = True
from pathlib import Path
import json, re, hashlib, subprocess
from datetime import datetime, timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
out=root/'.lake/proof-continuation/source-reviews'
source=root/'ImbalancedChen/Part3TransposedDifferenceMoment.lean'
parent=root/'ImbalancedChen/Part3TransposedModulusProgression.lean'
author_report=out/'20261016-transposed-difference-moment-payment-self-scope.json'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(source)=='248f6371a93df223c875908e12263db6b20f95a18df758f892f4c0a4b5485908'
assert sha(parent)=='b9300cf15133a7ebcb9eb1efee9e8b86889425c1d1a4d860188bc7a5f28f1a53'
assert sha(author_report)=='39e4360d283987b1d38156e662873de1afb199188903f197a127b7be3da4426c'
def uncomment(s):
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
            if j<0:j=len(s)
            chars[i:j]=[' ']*(j-i);i=j
        elif s[i]=='"':string=True;i+=1
        else:i+=1
    assert not depth
    return ''.join(chars)
def imports(p):return re.findall(r'(?m)^\s*(?:public\s+)?import\s+(\S+)',uncomment(p.read_text()))
def identity(p):return {'path':str(p.relative_to(root)),'sha256':sha(p),'direct_imports':imports(p)}
clean=uncomment(source.read_text())
starts=list(re.finditer(r'(?m)^(private\s+)?(theorem|lemma|def|abbrev|axiom|opaque)\s+([^\s({:]+)',clean))
assert len(starts)==14 and all(m[2]=='theorem' for m in starts)
decls=[]
for i,m in enumerate(starts):
    end=starts[i+1].start() if i+1<len(starts) else len(clean)
    segment=clean[m.start():end]
    # Exact proof marker, deliberately NOT first ':=' (named arguments and let bindings are retained).
    proof=re.search(r':=\s*by\b',segment)
    assert proof is not None
    header=segment[:proof.start()].strip()
    body=segment[proof.end():]
    body=re.split(r'(?m)^end(?:\s.*)?$',body,maxsplit=1)[0].strip()
    decls.append({'name':m[3],'kind':m[2],'private':bool(m[1]),'start_line':clean[:m.start()].count('\n')+1,'complete_source_header':header,'proof_separator':proof.group(0),'complete_proof_body_after_by':body,'proof_body_sha256':hashlib.sha256(body.encode()).hexdigest()})
author=json.loads(author_report.read_text())
author_headers=author['candidate']['all_complete_headers']
assert len(author_headers)==14
for a,b in zip(author_headers,decls):
    assert a['name']==b['name'] and ' '.join(a['complete_header'].split())==' '.join(b['complete_source_header'].split()),(a['name'],b['name'])
assert imports(source)==['ImbalancedChen.Part3TransposedModulusProgression']
manifest=json.loads((root/'lake-manifest.json').read_text())
providers={'goldbach':Path('/home/slava/codex-lean-ve/native-packages/goldbach'),'mathlib':Path('/home/slava/codex-lean-ve/native-packages/mathlib')}
provider_checks=[]
for name,p in providers.items():
    expected=next(x['rev'] for x in manifest['packages'] if x['name']==name)
    actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
    diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert actual==expected and diff.returncode==0
    provider_checks.append({'name':name,'source_path':str(p),'manifest_pin':expected,'actual_head':actual,'git_diff_HEAD_tracked_exit_code':diff.returncode,'source_head_and_tracked_clean_match':True})
pins=[]
for rel in ['lean-toolchain','lakefile.toml','lake-manifest.json']:
    p=root/rel;pin=root/'verification/proof-continuation/2026-10-15/pins'/rel
    assert p.read_bytes()==pin.read_bytes()
    pins.append({'path':rel,'current_sha256':sha(p),'archived_pin_path':str(pin.relative_to(root)),'archived_pin_sha256':sha(pin),'exact_match':True})
api_specs=[
 ('core',Path('/home/slava/codex-lean-ve/lean-4.33.0-rc1-linux/src/lean/Init/Data/Int/Order.lean'),650,663,'Int.natAbs_sub_of_nonneg_of_le; pays actual nonnegative integer difference'),
 ('goldbach',providers['goldbach']/'MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuPrereqFouvryDivisorMean.lean',325,354,'sum_fouvryTau_le_real at k=2, x=2U; actual Ioc(0,floor x) and exact log exponent k-1'),
 ('mathlib',providers['mathlib']/'Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean',89,100,'Finset.sum_image is additive form of prod_image; Set.InjOn hypothesis and equality orientation'),
 ('mathlib',providers['mathlib']/'Mathlib/Algebra/Order/BigOperators/Group/Finset.lean',157,168,'sum_le_sum_of_subset_of_nonneg is additive form of product subset theorem'),
 ('mathlib',providers['mathlib']/'Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean',363,386,'isLittleO_log_rpow_rpow_atTop: arbitrary real log exponent r, only positive power exponent s')]
apis=[]
for prov,p,lo,hi,role in api_specs:
    apis.append({'provider':prov,'path':str(p),'file_sha256':sha(p),'lines':[lo,hi],'role':role,'literal_fixed_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])})
local_specs=[
 ('Part3DistributionTargets',35,60,'Actual MediumAtom fields, X=U*V, exact alpha interval and original beta carrier'),
 ('Part3DistributionTargets',123,150,'All original MediumAdmissible geometry/coefficient gates, including four monomials and signed moving residue'),
 ('Part3TransposedDispersion',32,66,'Actual transposition swaps U/V, preserves residue/physical labels, zero-pads only paired original alpha'),
 ('Part3TransposedDispersion',174,199,'Actual original beta-L2 bound at 2V with p=(2^B)^2-1'),
 ('Part3PairedAlphaDeletion',38,48,'cleanedAlphaAtom changes only alpha; original beta, residue and all physical parameters remain'),
 ('Part3PairedAlphaDeletion',71,101,'Genuine original admissibility survives alpha deletion; active paired beta is nondivisor of residue'),
 ('Part3PairedAlphaDeletion',435,472,'actual_geometry_bounds derives U>=X^sigma from original Q1 gate, no transposed admissibility'),
 ('Part3ActualLargeGCDBetaMass',173,184,'Positive actual beta carrier subset Ioc 0 floor(2V), reused after transposition for 2U'),
 ('Part3TransposedModulusGCDZero',33,85,'Literal same small paired-gcd and large physical-modulus-gcd masks in W, raw zero and signed full frequency sum'),
 ('Part3TransposedModulusGCDZero',127,152,'Exact same-mask W=rawZero+fullNonzero identity'),
 ('Part3TransposedModulusGCDZero',176,189,'Actual norm fullNonzero<=normW+normrawZero, no positivity of the signed Fourier term assumed'),
 ('Part3TransposedModulusGCDZero',485,505,'Actual original beta-L2 raw-zero arbitrary-log payment with x0 before d/Y'),
 ('Part3TransposedModulusProgression',462,497,'Direct candidate parent genuine whole-W divisor majorant; no row-cap/energy/strong distribution budget premise')]
local=[]
for mod,lo,hi,role in local_specs:
    p=root/'ImbalancedChen'/f'{mod}.lean'
    local.append({**identity(p),'lines':[lo,hi],'role':role,'literal_current_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])})
proof_reviews={
 'natAbs_difference_of_le':'Pinned core Int.natAbs subtraction identity applies because b>=0 and b<=a. Casting both naturals reduces to the actual Nat subtraction.',
 'difference_row_le':'Split actual finite N into m<n and n<m, excluding m=n before any divisor cost. Both maps n-m and m-n are injective on their true half, their images lie in positive Ioc 0 K by the given endpoint assumptions. Nonnegative tau values allow extension to the full Ioc. Integer natAbs matches each half, so row cost is twice the genuine tau sum; no zero difference is put into a divisor set.',
 'transposed_betaCarrier_card_le':'Original U>=1 means the actual transposed paired carrier lies in Ioc 0 floor(2U). Finite card monotonicity and floor(2U)<=2U give card<=2U, including exact dyadic integer endpoints.',
 'transposed_offDiagonal_tauTwo_sum_le':'Each actual paired index is <=floor(2U). Difference-row bound, true k=2 mean at x=2U, and card<=2U give (2U)*2*(2U*(1+log2U))=8U^2*(1+log2U), uniformly in the original residue and with diagonal zero.',
 'transposed_diagonal_weight_sum_le':'For each n1 the actual inner equality indicator selects exactly n2=n1. The diagonal cost is card(betaCarrier)*5V<=2U*5V=10X, not a tau cost at zero.',
 'cleanedAlpha_transposed_beta_norm_le_one':'Actual cleaned original admissibility supplies alpha norm<=1 on its original interval. Transposed beta is precisely this cleaned alpha on the interval, zero elsewhere. No one-bound or roughness is claimed for original beta or grouped physical Gamma.',
 'cleanedAlpha_pairDivisorBudget_le':'The Y mask is discarded only inside an explicitly nonnegative norm majorant. Both actual paired coefficient norms are <=1; diagonal 5V and off-diagonal (4V/D+1)*tau2 costs are nonnegative for V>=1,D>0. The resulting pair sum splits exactly into the independently bounded 10X and 8U^2*(4V/D+1)*HU.',
 'cleanedAlpha_largeModulusW_bound':'The precise parent b930 provides a genuine whole-W divisor majorant with C>0 before B,sigma,c0,d,Y,D and epsilon>0. This leaf pays its finite pair cost; no caller norm budget or analytic row cap is added. Parent remains source candidate until its own actual acceptance.',
 'betaL2_mul_cleanedAlpha_largeModulusW_bound':'Multiply by the actual ORIGINAL beta-L2 bound 2V*HV^p, p=(2^B)^2-1. Since X=UV, (2V)*(10X)=20X^2/U and (2V)*(8U^2)*(4V/D+1)*HU=X^2*(64HU/D+16HU/V). All factors are nonnegative, so both inequalities multiply in the valid direction. Original beta and geometry are not swapped.',
 'one_le_scale':'U,V>=1 from original MediumAdmissible yield X=UV>=1; this does not strengthen the original geometry.',
 'both_lengths_lower_bound':'Existing actual Q1 geometry yields U>=X^sigma. Original Q2,Q3>=1 and U^2*Q2*Q3^2<X^(1-8sigma) give U^2<=X^(1-8sigma)<=X^(2-2sigma), where the exponent comparison follows for every sigma>0. Positive real-power square identity gives U<=X^(1-sigma); multiplying with V and X=UV gives V>=X^sigma. No upper bound on sigma, balance premise, nu or kappa gate is introduced.',
 'log_bound_from_scale':'For x>0, log x>=1 and 0<z<=8x, monotonicity and log(8x)=log8+logx give 1+logz<=1+log8+logx<=(2+log8)logx. No assumption that log z is positive is needed here.',
 'betaL2_mul_cleanedAlpha_largeModulusW_log_payment':'Set z=min(sigma,delta)>0, epsilon=z/2, p=(2^B)^2-1, N=p+1, L=2+log8 and E=100*C*L^N. Original U,V<=X and logX>=1 yield HU,HV<=Q=LlogX, Q>=1. Since U,V,D=X^delta>=X^z, the exact reciprocal bracket is <=100Q/X^z. The fixed arbitrary-real exponent A+N log little-o theorem gives E(logX)^(A+N)<=X^(z/2) beyond a scalar threshold depending on B,sigma,kappa,c0,A,delta but preceding d and Y. This cancels the other X^(z/2) and X^z exactly, proving the original-betaL2 whole-W bound X^2/log^A X for every real A.',
 'betaL2_mul_cleanedAlpha_largeModulusNonzero_log_payment':'Use actual same-mask fullNonzero=W-rawZero norm inequality on the genuinely cleaned atom. Cleaning alpha leaves original beta, physical lengths, moving signed residue and complex labels unchanged. Parent raw-zero theorem applied to the cleaned atom and this leaf whole-W theorem each cost X^2/log^A X; max of their scalar thresholds still precedes d and Y. Adding gives the entire-frequency signed norm cost 2X^2/log^A X in this second gcd region only.'}
assert set(proof_reviews)=={d['name'] for d in decls}
for d in decls:d['independent_proof_review']=proof_reviews[d['name']]
scans=[]
for p in [source,parent]:
    text=uncomment(p.read_text()); hits=[]
    for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
        for m in re.finditer(pat,text):hits.append({'line':text[:m.start()].count('\n')+1,'token':m.group(0)})
    assert not hits
    scans.append({**identity(p),'uncommented_forbidden_or_option_hits':hits})
report={
 'schema':'independent-complete-source-semantic-review-v1',
 'status':'SOURCE_ONLY_FULL_NONAUTHOR_REVIEW_NO_CONFIRMED_MATH_OR_FIXED_API_BLOCKER',
 'reviewer':'/root/lower_resume (independent of author /root/dispersion_resume)',
 'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),
 'project_head_at_review':sys.argv[1],
 'candidate':{**identity(source),'declaration_count':14,'definition_count':0,'complete_type_separator_method':'For each of the 14 theorem declarations, use the actual := by proof marker, not the first :=; named arguments and any let expressions remain in the full type. Compare all full headers against author evidence and inspect complete source/proofs independently.','all_complete_headers_and_proofs':decls,'full_source_text':source.read_text()},
 'author_evidence':{'path':str(author_report.relative_to(root)),'sha256':sha(author_report),'role':'Source and full-header binding only; author findings were not treated as independent proof or runtime acceptance.'},
 'direct_parent':{**identity(parent),'acceptance':'SOURCE_CANDIDATE_ONLY; current b930 parent independent review is handled separately. This report does not imply owned acceptance or substitute for its full actual runtime gates.','full_current_source_text_read':True},
 'relative_source_import_delta':{'literal_imports':imports(source),'new_local':['ImbalancedChen.Part3TransposedDifferenceMoment'],'new_foreign':[],'local_delta':1,'foreign_delta':0,'method':'The only literal import is the exact parent. Thus the import closure differs from that parent only by this local leaf, subject to the separately checked parent DAG. No external closure traversal/bootstrap was run.'},
 'literal_fixed_API_evidence':apis,
 'actual_local_definition_and_interface_evidence':local,
 'fixed_provider_source_checks':provider_checks,
 'exact_archived_config_pins':pins,
 'source_token_scan':scans,
 'mathematical_scope':{'actual_object':'Original-beta L2 times norm of the actual cleaned-alpha transposed full Fourier contribution with pair gcd<=Y and physical-modulus gcd>X^delta. All original physical labels, moving signed residue and smoothing at original V remain.','paid_budget':'C X^epsilon X^2 (1+log(2V))^p (20/U+64(1+log(2U))/D+16(1+log(2U))/V), then whole W<=X^2/log(X)^A and same-mask full nonzero<=2X^2/log(X)^A.','quantifiers':'C from epsilon,kappa precedes B,sigma,c0,d,Y,D in the finite whole-W bound. For fixed B,sigma,kappa,c0,A,delta with sigma,delta>0, x0>1 precedes every admissible actual d (including moving residue) and arbitrary Y. A is any real, not only positive.','added_gates':'Only explicit hsigma>0,hdelta>0; no extra sigma upper bound, nu gate, kappa gate, transposed admissibility or balance premise.','hidden_core_budget_premise':False,'remaining_open':['Both-small gcd signed Fourier remainder and its actual slow/root/reciprocal phase.','Other analytic coordinates and actual composition/deletion/SW/primitive-term gates needed for the complete restricted medium theorem.','RestrictedMediumTarget, full hUpper/hLower and manuscript Theorem1.1/Cor1.2 remain open.']},
 'findings':[],
 'acceptance_boundary':{'source_only':True,'lean_invoked':False,'lake_invoked':False,'build_invoked':False,'objects_installed_or_rebound':False,'foreign_bootstrap':False,'source_modified':False,'pins_or_limits_modified':False,'strict_elaboration_lint_verified':False,'kernel_or_transitive_axioms_replayed':False,'owned_or_cache_acceptance':False,'note':'All proof-script/API conclusions are static source conclusions. Only the sole runtime owner can supply exact source-object binding, strict elaboration/lint, full owned inventory/types/flags and transitive-axiom acceptance. Direct b930 parent is still a candidate.'}}
dest=out/'20261016-TransposedDifferenceMoment-lower-independent-semantics.json'
with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(source)==report['candidate']['sha256'] and sha(parent)==report['direct_parent']['sha256']
print(json.dumps({'report':str(dest.relative_to(root)),'sha256':sha(dest),'source_sha256':sha(source),'parent_sha256':sha(parent),'declarations':14,'definitions':0,'complete_types_match_author':True,'findings':[]},indent=2))