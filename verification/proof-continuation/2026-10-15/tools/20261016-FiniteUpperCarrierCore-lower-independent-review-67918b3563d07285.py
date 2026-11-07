import sys
sys.dont_write_bytecode=True
from pathlib import Path
import ast,json,re,hashlib,subprocess
from datetime import datetime,timezone
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
out=root/'.lake/proof-continuation/source-reviews'
# Reuse only pure parsing functions from this reviewer's draft, never execute its report-producing module.
helper=out/'drafts/20261016-TupleNormalization-DistinctProduct-lower-independent-rebind.py'
tree=ast.parse(helper.read_text())
needed={'sha','uncomment','imports','assignment_at_top','declarations'}
nodes=[n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name in needed]
assert len(nodes)==len(needed)
exec(compile(ast.Module(body=nodes,type_ignores=[]),str(helper),'exec'))
p=root/'ImbalancedChen/FiniteUpperCarrierCore.lean'
assert sha(p)=='5bb08b49bf20551e996afbafd92a90ce6aa17941424fa55485d9fa9f69ce98b7'
ds=declarations(p.read_text());assert len(ds)==18 and sum(d['kind']=='def' for d in ds)==7
review={
'actualSmallRoughModuli':'The actual displayed modulus carrier is the multiplication image of the actual small Rosser support and literal fixed retained rough support. No factor multiplicity or analytic property is asserted.',
'actualSmallRoughRho':'One physical coefficient is the finite fibre sum of the sign-sensitive small/rough pair coefficient, fixed independently of the tested integer. The actual lower and upper small Rosser coefficients are the same functions throughout.',
'realHalfProductCongruenceMass':'Exactly the current arbitrary-real ordered half-product source filtered by Nat.ModEq d m N. The source keeps its inclusive upper product endpoint and strict ordered-bad power boundary. This definition is a finite count, not a distribution estimate.',
'realHalfProductCoprimeMass':'Exactly the same real source with Nat.Coprime m d. The primitive gate is retained, not equated to total source mass.',
'realPhysicalCoprimeCorrection':'The exact signed cost of replacing the coprime source mass by the total source mass, with the same rho and displayed modulus carrier. It remains a visible term.',
'realPhysicalDistributionError':'The full signed primitive-residue error using exactly the same fixed rho. It is not changed into a sum of absolute discrepancies or an assumed small budget.',
'smallRoughModuli_subset_of_rough_subset':'Literal raw-to-rough support inclusion is transported through the same product-image map. This does not need cutoff separation, unique product decomposition or a coprimality assumption.',
'smallRoughRho_eq_of_rough_enlargement':'Unfold the finite fibre sum, include each raw pair into the enlarged pair carrier, and show every new pair has second coordinate outside raw. Its rough coefficient is zero, hence signAttachedCoefficient=c*chosenBeta is zero regardless of either beta or sign branch. Equality holds as a full function at every modulus, including zero, without assuming any sign on rho.',
'sum_smallRoughRho_mul_eq_of_rough_enlargement':'First substitute full-function equality. Every extra physical modulus is outside the raw product support and the raw fibre sum is zero there. Finset.sum_subset therefore preserves every arbitrary SIGNED linear test F exactly; no absolute error is introduced.',
'fixedRoughCoefficient_eq_zero_of_not_mem':'Unfold the literal retained-tree coefficient and use its proved off-support-zero theorem at h=1. The fixed rough support is definitionally the very same retained modulus set; Int.cast_zero gives real zero.',
'actualUpperCommonRoughSupport':'The common rough carrier is the actual raw retained support union compilerSupport. This definition leaves the raw policy, target-prime deletions and cutoffs unchanged.',
'actualUpperCommonRoughSupport_roughPrimeSupportedAt':'Split membership in the explicit union. Raw support has the proved actual rough-prime support property; compiler-only elements require only the explicit finite hcompiler support hypothesis. That is not an analytic distribution or target-density supplier.',
'actualSmallRoughRho_eq_on_common_carrier':'Specialize the generic finite rough enlargement identity to the actual raw retained coefficient using its actual zero extension. Only hcover is assumed; it is a finite set inclusion, not a density bound.',
'sum_actualSmallRoughRho_mul_eq_on_common_carrier':'The generic signed functional identity applies to the exact actual small/rough supports and coefficient for every signed F. It retains the actual pair-indexed finite fibre sum.',
'actualSmallRoughRho_divisorSum_eq_on_common_carrier':'Choose F(q)=1 when q divides n, else 0. Finite rewriting recovers the identical physical divisor sum, including n=0, without a positivity or density premise.',
'actualSmallRoughRho_density_eq_on_common_carrier':'Choose F(q)=1/phi(q); total real division remains valid even at q=0. The same raw reciprocal-totient density is equal on both carriers; no numeric density estimate is asserted.',
'actualSmallRoughRho_coprimeCorrection_eq_on_common_carrier':'Choose the exact real-source coprime-minus-total mass test divided by phi(q). Thus the primitive correction is unchanged as a signed whole; the coprime gate is not dropped.',
'actualSmallRoughRho_distribution_eq_on_common_carrier':'Choose the exact congruence-minus-coprime/phi test. The full signed distribution error on the same real half-product source is unchanged. This is not payment of that error or of any physical gcd Fourier region.'}
assert {d['name'] for d in ds}==set(review)
for d in ds:d['independent_semantic_and_proof_review']=review[d['name']]
parents=[]
for imp in imports(p.read_text()):
    q=root/(imp.replace('.','/')+'.lean');parents.append({'module':imp,'path':str(q.relative_to(root)),'sha256':sha(q),'direct_imports':imports(q.read_text()),'scope':'Relevant actual definitions and theorems read; no kernel or whole transitive source-closure replay inferred.'})
local_specs=[('SmallRoughAttachment',72,145,'Actual product carrier, sign-sensitive pair coefficient, finite fibre sum and proved off-support zero'),('SignSensitiveAttachment',103,110,'signAttachedCoefficient = c * if c>=0 then betaPlus else betaMinus, so c=0 pays every added pair'),('FixedRoughCoefficients',53,68,'Literal fixed raw retained support and coefficient'),('FixedRoughCoefficients',91,105,'Proved actual raw rough-prime support property'),('RetainedModuli',89,105,'Möbius on actual retained support and exact coefficient zero outside'),('PhysicalUpperWeightBridge',22,27,'Literal physical divisor-sum definition'),('PhysicalUpperWeightBridge',45,50,'Literal physical reciprocal-totient density'),('RealHalfProductSource',125,146,'Actual arbitrary-real ordered source with inclusive product upper endpoint'),('ActualUpperCommonCarrier',22,63,'Actual downstream compiler target-density bound still charges coefficient error and invokes separate reserve; this core only supplies exact raw carrier identification')]
locals=[]
for mod,lo,hi,role in local_specs:
    q=root/'ImbalancedChen'/f'{mod}.lean';locals.append({'path':str(q.relative_to(root)),'sha256':sha(q),'lines':[lo,hi],'role':role,'literal_source_excerpt':'\n'.join(q.read_text().splitlines()[lo-1:hi])})
mathlib=Path('/home/slava/codex-lean-ve/native-packages/mathlib')
api_specs=[('Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean',185,201,'Finset.sum_subset is the additive form of prod_subset: a subset plus exactly zero on added indices, with no sign condition'),('Mathlib/Data/Finset/Prod.lean',55,65,'Finset.mem_product constructor/projections'),('Mathlib/Data/Finset/Image.lean',288,300,'Finset.mem_image and its equation orientation'),('Mathlib/Data/Finset/Filter.lean',123,130,'Finset.mem_filter iff membership and predicate')]
apis=[{'path':rel,'provider':'mathlib','file_sha256':sha(mathlib/rel),'lines':[lo,hi],'role':role,'literal_fixed_source_excerpt':'\n'.join((mathlib/rel).read_text().splitlines()[lo-1:hi])} for rel,lo,hi,role in api_specs]
pins={name:sha(root/name) for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']}
for name,h in pins.items():assert sha(root/'verification/proof-continuation/2026-10-15/pins'/name)==h
manifest=json.loads((root/'lake-manifest.json').read_text());provider_checks=[]
for name in ['goldbach','mathlib']:
    q=Path('/home/slava/codex-lean-ve/native-packages')/name
    actual=subprocess.check_output(['git','-C',str(q),'rev-parse','HEAD'],text=True).strip()
    expected=next(x['rev'] for x in manifest['packages'] if x['name']==name)
    diff=subprocess.run(['git','-C',str(q),'diff','--quiet','HEAD','--'],capture_output=True,text=True)
    assert actual==expected and diff.returncode==0
    provider_checks.append({'name':name,'manifest_pin':expected,'actual_HEAD':actual,'git_diff_HEAD_tracked_exit_code':diff.returncode})
forbidden=[];clean=uncomment(p.read_text())
for pat in [r'\bsorry\b',r'\badmit\b',r'(?m)^\s*(?:axiom|opaque|unsafe)\b',r'\bnative_decide\b',r'(?m)^\s*set_option\b']:
    for m in re.finditer(pat,clean):forbidden.append({'line':clean[:m.start()].count('\n')+1,'token':m.group(0)})
assert not forbidden
report={'schema':'independent-complete-source-semantic-review-v1','status':'SOURCE_ONLY_FULL_NONAUTHOR_REVIEW_NO_CONFIRMED_MATH_OR_FIXED_API_BLOCKER','reviewer':'/root/lower_resume (not author of the legacy FiniteUpperCarrierCore source)','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'project_head_at_review':sys.argv[1],
'candidate':{'module':'ImbalancedChen.FiniteUpperCarrierCore','path':str(p.relative_to(root)),'sha256':sha(p),'declaration_count':18,'definition_count':7,'type_extraction':'Theorems use the actual := by proof marker; definitions use top-level assignment outside parentheses/braces. No first-:= truncation.','all_complete_types_definitions_and_proofs':ds,'full_current_source_text':p.read_text()},
'direct_parents':parents,'actual_local_definition_and_consumer_evidence':locals,'literal_fixed_API_evidence':apis,'exact_archived_config_pins':pins,'fresh_provider_HEAD_tracked_clean_checks':provider_checks,'source_forbidden_or_option_hits':forbidden,
'mathematical_boundary':{'analytic_supplier_assumed_or_used_by_this_leaf':False,'actual_hLower_or_hUpper_used_as_premise':False,'finite_hypotheses':'Arbitrary raw subset rough plus off-raw coefficient zero in generic statements; actual specialization proves zero by the retained-tree definition. The explicit compiler support condition is finite rough-prime geometry only.','real_source_bridge_note':'RealHalfProductSource imports CurrentMainTheorem infrastructure, but the reviewed leaf uses only its literal finite carrier, not any main-theorem assumption or derived hLower/hUpper conclusion.','actual_target_connection':'ActualUpperCommonCarrier directly imports this leaf. Its compiler-density reserve theorem rewrites by this exact actual raw-density equality, preserving a separate explicit coefficient-error charge. Pointwise majorants, raw density, primitive correction and signed distribution error are tied to one unchanged raw physical rho.','not_proved':['No actual compiler coefficient-error smallness bound','No distribution estimate or signed Fourier payment','No final actual upper density budget or full hUpper/hLower']},
'findings':[],'acceptance_boundary':{'source_only':True,'lean_lake_build_invoked':False,'source_modified':False,'objects_installed_or_rebound':False,'foreign_bootstrap':False,'old_reuse_objects_installed':False,'pins_limits_or_imports_changed':False,'whole_chain_or_foreign_closure_scanned':False,'strict_or_owned_or_cache_acceptance':False,'transitive_axiom_replay':False,'note':'This is the explicitly requested ready-parent legacy source review only. Current object absence/source binding still requires the sole runtime owner and a concrete root gate; no compile/install of the eleven old reuse objects or wider chain is authorized or attempted.'}}
dest=out/'20261016-FiniteUpperCarrierCore-lower-independent-semantics.json'
with dest.open('x',encoding='utf8',newline='\n') as f:json.dump(report,f,ensure_ascii=False,indent=2);f.write('\n')
assert sha(p)==report['candidate']['sha256']
print(json.dumps({'report':str(dest.relative_to(root)),'sha256':sha(dest),'source_sha256':sha(p),'declarations':18,'definitions':7,'findings':[]},indent=2))