import sys
sys.dont_write_bytecode=True
from pathlib import Path
import json,hashlib,re,datetime
root=Path('/mnt/e/timot/Documents/FilesForGPT/Myath/goldbach-proof-continuation')
template=root/'.lake/proof-continuation/source-reviews/drafts/20261016-U8PrimeSource-owner-review.py'
prefix=template.read_text().split("headers=re.findall",1)[0]
prefix=prefix.replace('CurrentChenUpsilon8PrimeSource','CurrentChenUpsilon8ProductPan').replace('20261016-U8PrimeSource','20261016-U8ProductPan')
exec(compile(prefix,'<fresh-source-header-walk>','exec'),globals())
headers=re.findall(r'(?m)^(?:(?:private|noncomputable)\s+)?(?:theorem|lemma|def)\s+[\s\S]*?(?=:=)',code)
defs=re.findall(r'(?ms)^def\s+.*?(?=\n\n)',code)
assert len(headers)==18 and len(defs)==4
pan=providers/'goldbach/MathlibNt/SieveTheory/LiLiuPanBoundedAggregate.lean'
pans=pan.read_text();k=pans.index('theorem liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving');panheader=pans[k:pans.index(':=',k)]
sem=dict(common,reviewer='lower_resume full source self-review, not independent validation',
complete_declaration_count=len(headers),complete_declaration_headers=headers,complete_definition_count=len(defs),complete_definition_bodies=defs,findings=[],
actual_reused_generic_theorems=[
'chenY9PrimeSelector_multiplier_injOn N A C: its generic selector predicate is definitionally identical to the eighth selector at the actual eighth A,C; no injection premise or second prime-factor uniqueness proof.',
'chenY9PrimeSelector_ordered_prime_data at explicit eighth endpoints.',
'currentChenUpsilon9_prime_mem_iff: arbitrary N,a,q,z gives the actual prime quotient dictionary at the original z=p2.',
'currentChenUpsilon9SwitchedPrimeFibre N a: its definition depends only on arbitrary N,a, literal prime q, strict a*q<N and the actual additive-prime receiver carrier.',
'liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving: existing unconditional fixed provider with actual true li and inclusive A2<=N^(2/3). No cloned distribution proof, Pan error kernel or current ninth object is modified.'],
checked_semantics=[
'The actual eighth product set is literally the image of its original selector. The coefficient is its literal 0/1 indicator, has no sieve-modulus argument, and its absolute bound is proved by cases.',
'Actual prime carriers prove every image label positive and coprime to N. Prime-factor separation and injection come from the already proved generic selector theorem, instantiated at A=N^(417/5000), C=N^(1/3).',
'The actual product lower exponent is 417/5000+1/3=6251/15000. The actual strict sqrt(N/p1) cap gives (p1*p2)^2<N*p1<N*N^(1/3)=(N^(2/3))^2, paying the strict upper exponent 2/3 directly.',
'The actual Pan natural endpoints are ceil(N^(6251/15000))-1 and ceil(N^(2/3))-1, for the supplier Ioc convention. Membership in that same interval is proved from both actual strict/weak real endpoints. The upper natural endpoint itself is proved <=N^(2/3), including the exact endpoint power allowed by the provider.',
'Exact coefficient sums on the whole actual Ioc window equal sums over the literal actual product image. This is a real same-coefficient identity with no pair multiplicity or coefficient-bound premise.',
'Finite source reindexing first uses the actual prime/unit equality and the proved product injection. Only an already prime quotient is included in the broader generic switched prime fibre. The original p2 cutoff remains in the exact PrimeSource dictionary and is dropped only for this explicit finite upper bound. The outer selector, actual target prime and its center-coprimality mask remain unchanged; actual units stay as an explicit unbudgeted term.',
'For every fixed B, the actual positive lower exponent pays log(N)^(2B) below the actual rounded lower endpoint. The exponent B is subsequently selected by the fixed Pan theorem before N and before any source-window use.',
'The actual support implies N/a>=N^(1/3) and, for N>=2, 1-log(a)/log(N)>=1/3. These conclusions are proved from the actual product geometry rather than supplied as asymptotic premises.',
'The final actual bounded Pan majorant uses the literal current eighth coefficient and its exact endpoints, with exists C>0,B>=0,N0 before every N>=N0. It calls the fixed true-li aggregate only after its three actual gates A2<=N^(2/3), log^(2B)<=A1 and all-coefficient abs<=1 have been paid.'],
provider_binding={'path':str(pan),'source_sha256':sha(pan.read_bytes()),'complete_provider_header':panheader},
remaining=['U8PrimeSource parent 71fea remains separately subject to its own strict compile and complete owned audit.','This new leaf has no Lean elaboration or owned-object acceptance claimed; independent complete source review and exact first runtime authorization are separate.','The true coprime main-term gate, signed Rosser active error, small-target-prime and unit error payments are still open for U8.','The actual U8 ordinary upper mean and any harmonic logarithmic integral dictionary are not asserted here.','No hUpper, adopted K improvement, strong distribution premise, current target main term or changed selector is a caller hypothesis.'])
semout=state/'source-reviews/20261016-U8ProductPan-semantics.json';semout.write_text(json.dumps(sem,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'source_sha256':sha(source),'complete_declarations':len(headers),'complete_defs':len(defs),'dag':str(out.relative_to(root)),'dag_sha256':sha(out.read_bytes()),'semantics':str(semout.relative_to(root)),'semantics_sha256':sha(semout.read_bytes()),'candidate_count':len(candidate),'baseline_union_count':len(baseline),'new_modules':new}))
