# Exact prime-Weil source reuse and half-support bridge

This revision supplies six new, uncompiled adapter sources. The arithmetic provider is an actual upstream theorem, not a newly introduced hypothesis: `KloostermanWeil.prime_bound` at LeanPool/lean-pool commit `5dd712603d49049c7a5198e5dd725f768c5a510b`. The mathematical normalization and deduction below pass this author's static review. This is not a kernel-acceptance report for the project adapters; root owns that acceptance. Existing positive6, conditionalcritical5, T25, and their freezes are untouched.

The earlier parent-directory report of no provider applies to its then-designated reused sources. The subsequently supplied LeanPool candidate changes that source inventory. It must not be concealed by leaving the old no-provider conclusion as the current finding.

## Literal normalization

The project's `OriginalSmoothPoissonTail.kloosterman p m n` is the range-`p` sum, filtered by coprimality, of
`fourier 1 ((m*u+n*inverseResidue p u)/p)`.
Its existing theorem `Physical.kloosterman_eq_zmod` proves equality, with the positive sign, to
`sum x : ZMod p, if IsUnit x then stdAddChar(m*x+n*x⁻¹) else 0`.
Its proof uses `ZMod.stdAddChar_coe` and `fourier_coe_apply`, including the factor corresponding to exp(2*pi*i*t). This is a proved dictionary, not an informal appeal to convention.

[Upstream PrimeFoundation](https://github.com/LeanPool/lean-pool/blob/5dd712603d49049c7a5198e5dd725f768c5a510b/LeanPool/KloostermanWeil/Weil/PrimeFoundation.lean) defines
`kloostermanSumPrime p a b = sum_{x != 0} stdAddChar(b*x+a*x⁻¹)`;
its conventional `weilKloostermanPrime p m n` has `m*x+n*x⁻¹`.
At a prime, `IsUnit x iff x != 0`. Thus the new `physical_eq_prime` sends `(m,n)` to `(a,b)=(n,m)`, and `physical_eq_weil` sends `(m,n)` to the same conventional pair. Both are exact complex equalities. No conjugation, negative frequency, factor p, sqrt(p), or omitted residue is absorbed into an inequality.

The upstream scaling theorem proves `S(m,n)=S(1,m*n)` under `m != 0` by the actual bijection `x -> m*x`. Consequently a diagonal unit-twisted pair `(u*m,u*m)` has square parameter `(u*m)^2`. Our implementation does not need to reprove that scaling: the stronger upstream two-nonzero theorem is applied directly.

## All prime and mark cases

The type of `prime_bound` requires only `[Fact p.Prime]` and nonzero residues a,b. Its proof handles p=2 separately; there is no odd-prime restriction in the public theorem. For a good prime `p not dividing m`, the first physical coefficient is nonzero modulo p. If the second coefficient is nonzero, apply `prime_bound p n m`. If it is zero, `kloostermanSumPrime_zero_left p m hm` evaluates the sum exactly as -1; `1 <= sqrt(p)` pays it. Hence the new public prime estimate is uniform in **every** integer n, including n=0:
`norm(K_p(m,n)) <= 2*sqrt(p)`.

For p dividing the fixed nonzero integer m, use the project's original triangle bound p. The set of those primes is finite, bounded by natAbs(m). Every exponent k>=2 also uses only the triangle bound p^k. No missing prime-power Weil theorem, p-adic stationary-phase estimate, squarefree restriction, or coprimality of the full modulus with m is introduced. Moduli 0 and 1 retain T25's explicit branches; the summability price suppresses modulus 0.

## Actual upstream proof boundaries inspected

The 34-file custom import closure is recorded in `UPSTREAM_INDEX.json`. Each archived file is byte-for-byte the pinned Git blob: `UPSTREAM_SHA256.json` contains its SHA256, Git blob SHA1, and a successful comparison against `UPSTREAM_GIT_TREE.json`. There are 39 distinct direct Mathlib imports and no TauCeti edge in this closure. A scan for sorry/admit/axiom/unsafe/implemented_by/native_decide/reduction bypass tokens returned no hits. That scan alone is not a proof audit.

The substantive boundaries were read, including their bodies:

* `Carlitz.ExtensionDefinitions` defines `psiExt` as the actual standard prime character composed with `Algebra.trace`, and `Kext` as the sum over the nonzero elements of the actual `GaloisField p n`. `Kext_one_eq_kloostermanSumPrime` uses the degree-one algebra equivalence and trace identity, not a redefinition of the base sum.
* `DicksonFiniteAlgebra` defines the polynomial weight by `stdAddChar(-nextCoeff - t*coeff1/coeff0)`, extended by zero when coeff0=0. `ClassValue.trace_carlitz_arg` derives exactly these signs from traces of x and x inverse and their minimal polynomials. The first polynomial coefficient equals the base Kloosterman sum, the second equals p for t nonzero, and the higher coefficients vanish by shifting the last coefficient. `ClassGhost/IrreducibleGhost/NewtonSum` link the finite extension sum to the logarithmic-derivative identity. `GeneratingIdentity/RecurrencePackage` supply actual roots alpha,beta with alpha+beta=-Kext(p,1,t), alpha*beta=p and Kext(p,n,t)=-(alpha^n+beta^n) for positive n. No spectral-radius estimate is assumed at that boundary.
* `Stepanov.SpecializedCurve` uses the actual polynomial `(X^p-X)^2-4*c`, of degree 2p. Odd characteristic and c nonzero imply its nonzero constant coefficient, separability and non-square condition. `Auxiliary/Parameters/Defect` construct the nonzero coefficient vector by a strict dimension inequality, prove nonvanishing of the auxiliary polynomial and its Hasse-derivative multiplicities, and derive the high-extension point-count defect. The hypotheses include the explicit large-field inequality; they are discharged eventually in `SpectralBound`.
* `CurveTrace` exhibits the actual point bijection with `x^p-x=t+c/t`, computes Artin-Schreier fibers using trace zero and additive orthogonality, and proves the sum over scalar trace weights. `ScalarExtensionSum` turns a nonzero scalar m into parameter m^2*c by an actual multiplicative bijection. Thus `PointCountBridge` identifies the affine point count minus p^n with `-1+sum_{m!=0} Kext(p,n,m^2*c)`.
* At even degrees 2n, `SpectralBound` obtains a uniform-in-n bound on the power sums of the finite family alpha(m^2*c)^2/p and beta(m^2*c)^2/p. `PowerSumSpectral` proves that such bounded power sums force every root to have norm <=1 by Newton identities and polynomial root bounds. This explicitly addresses possible cancellation among roots. Therefore each alpha,beta has norm at most sqrt(p), and the exact degree-one sum gets the factor 2. The public bridge then supplies both nonzero coefficients by the already proved scaling.

The upstream comment that the Carlitz normalization has not been compared equation by equation to the original article is not a premise. Here its actual algebraic signs and actual extension sums were checked against the definitions above. Upstream kernel/axiom/CI review is assigned independently to s05; this note does not replace it or independently claim that CI was rerun.

## The complete T25 arithmetic deduction

Use
`B_m(p)=2*p^(1/2)` for p not dividing m,
`B_m(p)=p` for p dividing m,
and `B_m(p^k)=p^k` for k>=2, extending multiplicatively.

The copied CRT induction retains both canonical unit twists. It moves the first unit twist to the second mark using the project's proved `kloosterman_unit_scaling`; because the prime bound is uniform in the second mark, the fixed first mark m is preserved. This is stronger than a merely untwisted diagonal estimate. It yields `norm(K_d(m,n)) <= B_m(d)` for every n and d. Modulus-dependent unit multipliers of the first mark are covered too.

For any real delta<1/2, let r_p=p^(-1+delta), so r_p<1 for prime p. The local series is
`1 + price(m,delta,p) + r_p^2/(1-r_p)`.
The first prime term is p^(-1+delta) at the finitely many bad primes and 2*p^(-3/2+delta) otherwise. The higher-power tail is at most
`(1-2^(-1+delta))^(-1)*p^(-2+2*delta)`.
Both unrestricted p-series converge for every strict delta<1/2; the bad term is finitely supported. The original finite-smooth-number Euler argument bounds finite sums by exp(sum envelope), establishing actual `Summable (price m delta)`. Delta=1/2 is neither required nor claimed.

## Native consequence and quantifiers

For each fixed positive mark m and real delta<1/2 the geometry source gives one finite K(m,delta)>=0, chosen before q and Y, with
`norm(spectral q m m (single Y)) <= K(m,delta)*Y^(1-delta)`
for every positive integer level q and every real Y>0. Explicitly it uses
`K=(8*pi*m)^(1-delta)*sum'_{c:PNat} B_m(c)c^(-2+delta)`.
The cutoff support gives c<=8*pi*m*Y; the trace denominator is 1/c. No asserted spectral asymptotic is an input.

Now fix q,m,i with s=tau(q,i)>1/2. Choose v=(s+1/2)/2 and delta=1-v. Then 1/2<v<s, delta<1/2. The reviewed positive6 private theorem `others q m (0<v)` pays the complete principal, incoming and holomorphic singleton spectra by D(q,m,v)*Y^v for Y>=1. Its `slot_floor q m` first takes the maximum T<1 over the **whole finite exceptional family**, then gives c>0,Y0>=1 and nonnegativity for every other exceptional slot. This avoids discarding possibly negative exceptional test weights.

The actual trace split therefore gives
`c*norm(R(q,i,infinity,m))^2*Y^(s-v) <= K+D`
for every Y>=Y0. Since s-v>0, letting Y grow forces R=0. The existing exact normalization `basisR_eq_half_native` gives rhoK=2R, hence rhoK=0. The resulting `positive_half_support` is precisely the existing interface, with no new premise.

Only the positive Fourier coefficients at the original infinity coordinate are killed. This is not a theorem that all exceptional indices with s>1/2 disappear, not an eigenvalue lower bound, and not Kim-Sarnak's doubled 7/32 bound. The existing conditionalcritical5 consumes exactly these positive coordinates, so the sixth adapter simply applies its original-range theorem. Kernel acceptance of that composition remains pending; the main goal's current color/count is unchanged.

## Alternative candidate

[PLBY's PrimeKloostermanBound](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos387/PrimeKloostermanBound.lean) uses the same standard character via its `sum_eq_inverse_phase` dictionary. Its displayed proof changes variables x=t/(t+1), excludes t=0,-1 and adds back x=1, producing 3*sqrt(p)+1 for p>2 and both coefficients nonzero. Its rational extension theorem constructs, rather than assumes, `HasEvenExtensionSquareRootBound` from trace-fiber counting. These selected boundary files were read. Its full custom dependency closure and global compiled trust chain are not independently audited by this author and are not selected here. The bound would suffice with local price 4*sqrt(p), with p=2 paid separately and degenerate coefficients treated explicitly; there is no need to port both proofs.
