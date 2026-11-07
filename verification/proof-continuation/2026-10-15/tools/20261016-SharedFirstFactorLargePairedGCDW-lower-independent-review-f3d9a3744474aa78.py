import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,subprocess,importlib.util
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation');state=root/'.lake/proof-continuation';out=state/'source-reviews'
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py';tree=ast.parse(helper.read_text())
exec(compile(ast.Module(body=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in {'sha','uncomment','imports','assignment_at_top'}],type_ignores=[]),str(helper),'exec'))
def declarations(raw):
    clean=uncomment(raw);matches=list(re.finditer(r'(?m)^(private\s+)?(def|theorem|lemma|abbrev|axiom|opaque)\s+([^\s({:]+)',clean));result=[]
    for i,m in enumerate(matches):
        segment=clean[m.start():matches[i+1].start() if i+1<len(matches) else len(clean)]
        if m[2] in {'theorem','lemma'}:
            marker=re.search(r':=\s*by\b',segment)
            if marker is not None:offset=marker.start();start=marker.end();style='tactic'
            else:offset=assignment_at_top(segment);start=offset+2;style='term'
        else:offset=assignment_at_top(segment);start=offset+2
        body=re.split(r'(?m)^(?:end(?:\s.*)?|namespace\s.*|noncomputable\s+section)\s*$',segment[start:],maxsplit=1)[0].strip()
        d={'name':m[3],'kind':m[2],'private':bool(m[1]),'start_line':clean[:m.start()].count('\n')+1,'complete_source_header':segment[:offset].strip()}
        if m[2]=='def':d['complete_definition']=segment[:offset+2]+'\n'+body
        else:d['complete_proof_body_after_by' if style=='tactic' else 'complete_term_proof']=body
        result.append(d)
    return result
module='ImbalancedChen.Part3SharedFirstFactorLargePairedGCDW';source=root/'ImbalancedChen/Part3SharedFirstFactorLargePairedGCDW.lean';expected='645531ed78523f0c5e2be9ec8a8200fc24a2a30ad115766b020993330d278c1d';assert sha(source)==expected
owner_path=out/'20261016-shared-first-factor-large-paired-gcd-W-self-scope.json';assert sha(owner_path)=='8610b4f83f47a3ad2c4e5c8b6bb9d1828172958f14db17b11384e64fba294eff';owner=json.loads(owner_path.read_text())
ds=declarations(source.read_text());assert len(ds)==17 and sum(d['kind']=='def' for d in ds)==1
assert 'namespace' not in ds[0]['complete_definition']
for a,b in zip(ds,owner['complete_declarations']):assert (a['name'],a['kind'],a['private'],a['complete_source_header'])==(b['name'],b['kind'],b['private'],b['complete_header'])
parent_names=['ImbalancedChen.Part3SharedFirstFactorDispersion','ImbalancedChen.Part3SharedFirstFactorPairCount'];assert imports(source.read_text())==parent_names
parent_expected=['6d86424370c150c89dd06ef1fb1c56c79caa4dc5474f4c3061eb64536ca1564d','44cdaf188f35435f8956d19c2701abbcf69101b4cfb491679761d19080f96fe7'];parents=[]
for n,h in zip(parent_names,parent_expected):
    p=root/Path(n.replace('.','/')).with_suffix('.lean');assert sha(p)==h;parents.append({'module':n,'path':str(p.relative_to(root)),'source_sha256':h,'direct_imports':imports(p.read_text()),'runtime_status':'Candidate parent; actual own-object gate must be checked by runtime, not inferred from this source review.'})
parser_path=state/'import_walker_v2.e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914.py';assert sha(parser_path)=='e2e7eeaa0c24ea5def16b0cfac5fb63c40f8587421a75a0a0be851d9b7386914';spec=importlib.util.spec_from_file_location('sharedW_independent_header_parser',parser_path);parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
def project_walk(name):
    seen={};foreign=set();missing=[];findings=[]
    def visit(n):
        if not (n=='ImbalancedChen' or n.startswith('ImbalancedChen.')):foreign.add(n);return
        if n in seen:return
        p=root/Path(n.replace('.','/')).with_suffix('.lean')
        if not p.is_file():missing.append(n);return
        b=p.read_bytes();hd=parser.header_imports(b.decode());seen[n]={'sha256':hashlib.sha256(b).hexdigest(),'imports':[x['module'] for x in hd['imports']]}
        if hd['parser_findings']:findings.append({'module':n,'findings':hd['parser_findings']})
        for x in hd['imports']:visit(x['module'])
    visit(name);return seen,foreign,missing,findings
cand,foreign,missing,findings=project_walk(module);baseline={};bforeign=set()
for name in parent_names:
    nd,nf,nm,np=project_walk(name);assert not nm and not np;baseline.update(nd);bforeign|=nf
assert not missing and not findings and set(cand)-set(baseline)=={module} and foreign-bforeign==set()
assert len(cand)==61 and len(baseline)==60
pins={n:sha(root/n) for n in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for n,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/n)==h
assert pins==owner['pins_fresh'] if 'pins_fresh' in owner else True
manifest=json.loads((root/'lake-manifest.json').read_text());providers=Path('/home/slava/codex-lean-ve/native-packages');provider_checks=[]
for name in ['goldbach','mathlib']:
    p=providers/name;expected_head=next(x['rev'] for x in manifest['packages'] if x['name']==name);actual=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip();diff=subprocess.run(['git','-C',str(p),'diff','--quiet','HEAD','--'],capture_output=True,text=True);assert actual==expected_head and diff.returncode==0
    provider_checks.append({'name':name,'actual_HEAD':actual,'manifest_pin':expected_head,'git_diff_HEAD_tracked_exit_code':diff.returncode})
copy_source=root/'ImbalancedChen/Part3TransposedLargeGCDFourier.lean';copy_ds={d['name']:d for d in declarations(copy_source.read_text())};byname={d['name']:d for d in ds};copy_checks=[]
for name in ['one_le_scale','actual_difference_le_polynomial','tauFour_difference_subpower']:
    a=byname[name];b=copy_ds[name];assert a['complete_source_header']==b['complete_source_header'] and a['complete_proof_body_after_by']==b['complete_proof_body_after_by']
    copy_checks.append({'name':name,'header_and_entire_proof_text_exact':True,'source_start_line':b['start_line'],'destination_start_line':a['start_line'],'proof_body_sha256':hashlib.sha256(a['complete_proof_body_after_by'].encode()).hexdigest()})
copy_audits=[]
for ap in (state/'audits').glob('*/receipt.json'):
    ar=json.loads(ap.read_text())
    if ar.get('status')=='PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS' and ar.get('targets',{}).get('ImbalancedChen.Part3TransposedLargeGCDFourier')==sha(copy_source):copy_audits.append({'path':str(ap.relative_to(root)),'sha256':sha(ap),'status':ar['status']})
reviews=[
('MediumAtom.sharedLargePairedGCDW','The definition is literally the complete primitive-first-factor sum of actual sliced transposed commonLargeBetaGCDW. It keeps every positive composite p and every actual complex weight, with no raw-zero subtraction or implicit beta normalization.'),
('absoluteRow_le_tauFour_of_not_dvd','The auxiliary record changes only beta to1 and B to0, preserving the original geometry, gamma gates and alpha gates. This is admissible because the actual beta-divisor bound at exponent0 is1. Its cleanedBeta is nonzero exactly under the already supplied n not dividing the signed residue. The public genuine tau4 row bound therefore applies to the same physical row, which is independent of beta. Original beta is not bounded by one.'),
('one_le_scale','Actual U,V>=1 directly give X=UV>=1.'),
('actual_difference_le_polynomial','Actual smooth support gives m<=3V and actual transposed beta carrier gives n<=2U; hence mn<=6X. The original signed residue has |a|<=X^(1+kappa). K=max(1,1+kappa) and X>=1 give |mn-a|<=7X^K for every real kappa, including0 and negative values. No new kappa gate is introduced.'),
('tauFour_difference_subpower','Cleanup n not dividing signed a guarantees mn-a nonzero, so the public all-positive-integers tau4 subpower theorem applies. With eta=epsilon/(2K)>0, the true7X^K polynomial bound gives C X^(epsilon/2). The constant depends on kappa and epsilon before all B,sigma,c0,d,m,n. No divisor bound at zero is invoked.'),
('p_pos_lower','Actual p belongs to the full dyadic Q1 carrier and Q1>=1, so p>0 and p>=Q1. No primality or squarefree assumption enters.'),
('p_coprime_residue','The true primitive filter is Coprime p |a|. Symmetry and Int.gcd give gcd(a,p)=1 for the original signed a, including a=0 whenever the filter allows p.'),
('slice_gamma','Slicing and transposition preserve all factor labels and change only gamma1 into the actual indicator r1=p. The displayed gamma identity is definitional.'),
('absoluteRow_eq_zero_of_not_product','Every nonzero sliced row label has first factor p; therefore p divides its actual product modulus. Its original product congruence descends to modulo p. If that product congruence is false at p the whole row is zero; labels with r1!=p have zero actual gamma. No signed term is omitted by a nonnegativity argument.'),
('coprime_of_product_congruent','Primitive original residue and the actual product congruence imply the product itself is a unit modulo p. Gcd product decomposition then supplies both individual unit gates. This holds for every positive composite p; primality is never used.'),
('shared_conditions_of_products','Two actual m*n_i congruences give a*n1 congruent a*n2. The original unit a and positive p allow cancellation by the fixed Int.ModEq.cancel_left_div_gcd API, yielding n1 congruent n2 modulo the SAME p. Both true n_i unit gates are derived independently from product congruences.'),
('sum_weight_product_le','The actual transposed smooth variable lies in Icc0ceil(3V), cutoff weight is at most1, and the real primitive n supplies the public quotient-block product-congruence count K/p+1. The ceiling<=4V at V>=1 gives4V/p+1, retaining m=0 and signed a.'),
('sum_weight_two_products_le','When both unit and same-p congruence conditions hold, dropping only one congruence inside a nonnegative smooth sum bounds it by the genuine one-product AP cost. Otherwise both product congruences are impossible by the previous proved implication, so the whole smooth sum is exactly zero.'),
('slice_factorPair_norm_subpower','The complete actual complex factor-pair norm is bounded before introducing nonnegative absolute rows. Smoothing/carriers are unchanged under p slicing. Nonzero smooth terms and cleaned n_i let each genuine tau4 row cost C X^(epsilon/2); multiplication costs C^2 Xepsilon. The actual product congruences stay as an inner condition and give the correct4V/p+1 cost only after summing the same m. No false independence or missing p multiplicity is assumed.'),
('cleaned_beta_norm_le_one','The transposed coefficient here is exactly original cleaned alpha, restricted to its actual interval. Original alpha already has norm<=1. This assertion does not apply to the original beta or the physical grouped Gamma.'),
('card_primitiveCarrier_le','The full primitive p carrier is merely embedded in Ioc0floor(2Q1); its true finite cardinal is at most2Q1. All composite and overlapping dyadic endpoint contributions remain.'),
('cleanedAlpha_sharedLargePairedGCDW_bound','Actual nonzero cleaned coefficients supply n_i not dividing a before any tau4 estimate. Triangle inequality and original alpha norm<=1 give the actual ordered primitive/same-p/large-gcd pair cardinal. The public PairCount at T=2U retains diagonal and all composite p, costing8U²/(pY)+2U(1+log2U). Since p>=Q1, positive Y>=1 and V>=1, the AP and pair costs are enlarged in valid nonnegative directions. Summing the complete p carrier and using cardinal<=2Q1 gives exactly (4V/Q1+1)*(16U²/Y+4Q1 U(1+log2U)). C(kappa,epsilon)>0 precedes every original atom and Y; no original beta one-bound, raw-zero/NZ estimate, centered energy or final target payment is claimed.')]
assert [n for n,_ in reviews]==[d['name'] for d in ds]
for d,(_,text) in zip(ds,reviews):d['independent_proof_review']=text
api_names={
'Part3SharedFirstFactorDispersion':['MediumAtom.q1SliceAtom','MediumAtom.primitiveFirstFactorCarrier','mediumAdmissible_q1SliceAtom'],
'Part3SharedFirstFactorPairCount':['sharedPrimitiveLargeGCDPairs','MediumAtom.card_sharedPrimitiveLargeGCDPairs_le'],
'Part3PairedAlphaDeletion':['MediumAtom.cleanedAlpha_transposedBeta_ne_zero_not_dvd','card_product_modEq_le'],
'Part3PolynomialResidueDivisorBound':['fouvryTau_le_const_rpow'],
'Part3CleanBetaLargeGCDMajorant':['MediumAtom.commonLargeBetaGCDW','MediumAtom.absoluteFactorModulusRow','MediumAtom.absoluteFactorModulusRow_nonneg','MediumAtom.absoluteFactorModulusRow_le_tauFour','MediumAtom.commonFactorPairWeight_norm_le'],
'Part3TransposedDispersion':['MediumAtom.transposedAtom']}
project_apis=[]
for mod,names in api_names.items():
    p=root/'ImbalancedChen'/f'{mod}.lean';b={d['name']:d for d in declarations(p.read_text())};assert set(names)<=set(b)
    project_apis.append({'path':str(p.relative_to(root)),'sha256':sha(p),'complete_actual_declarations':[b[n] for n in names]})
mathlib=providers/'mathlib';native_specs=[(mathlib/'Mathlib/Data/Int/ModEq.lean',125,134,'Actual product congruence descends along p dividing product modulus'),(mathlib/'Mathlib/Data/Int/ModEq.lean',210,224,'Actual positive-modulus cancellation removes gcd(p,a), which is proved to be1'),(mathlib/'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',113,119,'Positive real powers at actual X>=1'),(mathlib/'Mathlib/Analysis/SpecialFunctions/Pow/Real.lean',204,211,'Actual positive-base real power algebra')]
native_apis=[{'path':str(p),'sha256':sha(p),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(p.read_text().splitlines()[lo-1:hi])} for p,lo,hi,role in native_specs]
forbidden=[]
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    forbidden.extend(m.group(0) for m in re.finditer(pat,uncomment(source.read_text())))
assert not forbidden
report={'status':'SOURCE_ONLY_FULL_NONAUTHOR_REVIEW_NO_CONFIRMED_MATH_OR_FIXED_API_BLOCKER_PENDING_PARENT_AND_RUNTIME_GATES','reviewer':'/root/lower_resume, independent of author /root/dispersion_resume','created_at_utc':datetime.now(timezone.utc).isoformat(),'module':module,'source_path':str(source.relative_to(root)),'source_sha256':sha(source),'author_report':{'path':str(owner_path.relative_to(root)),'sha256':sha(owner_path)},'declaration_count':17,'definition_count':1,'type_extraction':'Tactic theorem types end only at actual := by; the single rfl term theorem uses top-level := outside bracketed named arguments. Def assignment is top-level outside bracketed named arguments. A completed definition body stops before top-level namespace/end commands; the initial definition therefore contains no later namespace declaration.','all_complete_headers_definitions_and_proofs':ds,'full_current_source':source.read_text(),'direct_candidate_parents':parents,'source_runtime_boundary':'Both direct parent own-object gates and exact root runtime authorization remain necessary. Current Shared6d86 and PairCount44cd are candidate parent source interfaces, not acceptance of this new leaf. No compiler was run in this review.','copied_span_provenance':{'source_path':str(copy_source.relative_to(root)),'source_sha256':sha(copy_source),'three_full_headers_and_proofs_exact':copy_checks,'matching_current_owned_receipts':copy_audits,'semantic_boundary':'These spans are independently rechecked for real kappa, genuine finite supports and nonzero differences. Exact copying is source provenance, not transfer of target or arithmetic payment acceptance.'},'complete_public_project_API_source':project_apis,'fixed_native_API_source':native_apis,'fresh_relative_project_DAG':{'method':'Fresh proper Lean-header walk of project nodes and named foreign import fringe, relative to the two current source parents. No full foreign closure or kernel replay claimed.','parser_path':str(parser_path),'parser_sha256':sha(parser_path),'candidate_local_nodes':len(cand),'parent_union_local_nodes':len(baseline),'new_local':sorted(set(cand)-set(baseline)),'new_foreign':sorted(foreign-bforeign),'project_inventory':cand,'foreign_named_fringe':sorted(foreign),'missing_project_nodes':missing,'parser_findings':findings},'pins':pins,'providers_current_pin_HEAD_and_clean':provider_checks,'forbidden_hits':forbidden,'findings':[],'scope_not_claimed':['raw-zero correction','full nonzero or same-mask W-minus-zero payment','small paired gcd region','logarithmic or ordinary mean payment','full restricted medium target','hLower/hUpper or adopted constant'],'no_source_modified':True,'no_Lean_or_build_invoked':True,'bytecode_writes_disabled':True,'no_kernel_owned_or_cache_acceptance_claimed':True}
for name,h in zip(parent_names,parent_expected):assert sha(root/Path(name.replace('.','/')).with_suffix('.lean'))==h
assert sha(source)==expected
p=out/'20261016-SharedFirstFactorLargePairedGCDW-lower-independent-semantics.json'
with p.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps({'report_path':str(p.relative_to(root)),'report_sha256':sha(p),'source_sha256':sha(source),'complete_declarations':17,'definitions':1,'relative_DAG':[len(cand),len(baseline)],'new_foreign':[],'copied_spans_exact':3,'matching_owned_copy_receipts':copy_audits,'source_only':True},indent=2))