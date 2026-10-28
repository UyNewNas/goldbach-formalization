# PP / transfer independent source review

Reviewer: `/root/review_pp_transfer`. Six local results receive `SOURCE_REVIEW_PASS`; all six original tasks remain incomplete. `compiled=false`, `kernel_verified=false`, `formal_credit=0`, `ready_to_install=false`. The main theorem, whole signed PP insertion and lower/upper transfer remain `OPEN`.

The review read actual candidate source, final registries/reports, SourceReview-V2, manuscript anchors and necessary predecessors. It audited signs and same-rho use, domains and endpoint handling, quantifier order, occurrence multiplicity and honest scope. Candidate/dependency/manuscript hashes recorded in the registries were recomputed; all recognized explicit pairs match. No Lean/lake/compiler/checker, numerical replay, installation or quota check was performed. No `sorry`, `admit`, `axiom` or `unsafe` occurs in the six candidate files.

| Task | Source lines | Result | Original task complete |
| --- | ---: | --- | --- |
| `pp_twolong` | 449 | SOURCE_REVIEW_PASS | false |
| `pp_fourier` | 336 | SOURCE_REVIEW_PASS | false |
| `pp_derivatives` | 344 | SOURCE_REVIEW_PASS | false |
| `transfer_lambda` | 423 | SOURCE_REVIEW_PASS | false |
| `transfer_power` | 261 | SOURCE_REVIEW_PASS | false |
| `transfer_trace` | 284 | SOURCE_REVIEW_PASS | false |

## pp_twolong

Accepted scope: Actual fixed dyadic bump, literal Mellin long profiles and N2 bounds; same-amplitude finite mode core and pointwise two-long Fourier factorization.

Source: `goldbach-proof-continuation/docs/source-only/20261028-resume-30/pp_twolong/Part3TwoLongLiteralMellinModes.lean`. SHA-256 `2fce2a53febab40154a9e136882da2c334cbefb65fa662b7369fa7201f750e26`.

- The actual ContDiffBump has center 3/2, inner radius 1/2 and outer radius 1. Its plateau contains both closed dyadic endpoints, while support is enlarged to [1/2,5/2], exactly as the manuscript requires.
- twist_smooth handles x=0 by an actual zero neighborhood. The explicit second derivative has the correct chi-double-prime, 2*i*t*chi-prime/x, and ((i*t)^2-i*t)*chi/x^2 terms. Positivity of the support gives the fixed quadratic N2 frequency bound.
- The finite mode payment uses sum |alpha| times C^2(1+H)^4; it does not pay the number of frequencies, H^rank, or the number of short occurrences.
- The enlarged natural sampling window ceil(5A/2) contains the actual nonzero profile when A>0. The literal core keeps identical alpha in the AP count and exact coprime mean.
- owned_brun_ratio_mem uses positive d and literal original Owns(d*u); actual_owned_mode_identity therefore preserves the closed endpoints after U/d rescaling. selected_fourier_mode_exact is a true two-coordinate product identity with a q-independent amplitude of norm |A(xi)|.

Premise/scope audit: No P2 bound or final PP result is assumed. N2 constants come from the fixed bump. Positivity of Brun divisors and actual long-coordinate support are explicit. Pointwise equality on owned points is not claimed to be full sharp/smoothed-core equality.

The old Mode support [1,2] cannot contain a continuous cutoff equal to one on the complete closed rectangle. Replacing that receiver by manuscript support [1/2,5/2] is an implementation correction; it demonstrates no manuscript gap.

Still required:

- Construct the actual all-rank Family compact logarithmic chart, its D_T bounds and Fourier inversion.
- Prove continuous-integral mode mass, full three Brun-core reconstruction and smooth sandwich.
- Apply the precisely normalized external fixed-m P1/P2 primitive, bind the same signed physical rho and restore full E4.

## pp_fourier

Accepted scope: All-rank Cauchy omitted-cube union/Fubini estimate and physical-frequency normalized retained-cube synthesis error.

Source: `goldbach-proof-continuation/docs/source-only/20261028-resume-30/pp_fourier/P5AllRankCauchyCubeTail.lean`. SHA-256 `bca1b6c0aa92d67ac5e5d3f1d6d917ae46656209ca37eaa1e45133227b83b6db`.

- The outside-cube indicator is majorized by a finite sum of nonnegative coordinate slabs; no disjointness premise is used. Actual product Fubini reduces each normalized slab to the one-dimensional tail.
- The positive Cauchy tail follows from comparison to x^(-2) and its improper integral; reflection pays both signs, giving 2/H. Restoring pi^m and (2*pi)^(-m) yields the conservative m/H bound.
- The finite index set includes rank zero: outsideCube is empty, the omitted mass and synthesis error are zero. Strict outside cutoff and its complement retain the complete closed cube.
- physical_frequency_tail_le assumes the upstream mixed-IBP pointwise majorant and ordinary integrability, rather than a desired arithmetic discrepancy or tail estimate. normalized_synthesis_error_le derives integrability of A*phase and subtracts the actual complement integral; bounded measurable phases add no cube-volume cost.

Premise/scope audit: The physical frequency convention is internally coherent. The source explicitly leaves the normalized Euclidean frequency nu -> physical xi=2*pi*nu dilation/Jacobian open; it does not silently identify these measures or frequencies. The rank-dependent factor m is explicit.

Still required:

- Connect the actual Euclidean Fourier transform to physical A by dilation with the correct Jacobian.
- Construct actual independent W_N and its D_T derivative payment.
- Insert the tail after the full same-rho modulus count/mean sum, including exact-product and reciprocal-totient payments.

## pp_derivatives

Accepted scope: Genuine occurrence derivatives, arbitrary ordered-word four-factor Leibniz expansion and a uniform Family mixed-Euler specialization.

Source: `goldbach-proof-continuation/docs/source-only/20261028-resume-30/pp_derivatives/P5OccurrenceWordFourFactorLeibniz.lean`. SHA-256 `e6c864e011037d7b70f4aac6a4fa720010fbb8f3cb68c8152570b436ae1317ab`.

- occOne is identified with a genuine Frechet derivative in the coordinate tangent, and smoothness is propagated through derivatives. The proof is not based on an assumed abstract Leibniz operator.
- Finite list sums and the fourAlloc list retain repeated labels and allocation multiplicities. Its exact length is 4^r, total allocated word length is r, and induction gives the arbitrary-word four-product identity.
- The product bound is derived from four separate finite-order derivative bounds with explicit 4^r. The requested bound for the complete product is not supplied as a premise.
- family_four_chart_bound chooses one C,B from Family.mixedEuler before T, admissible ranks, group maps and occurrence words; it retains log(T+2)^B and all repeated owner coordinates. Smoothness of actual grouped family factors is derived.

Premise/scope audit: The real Family provides the geometric factor bound; E, P and Cut still require separate smoothness and derivative bounds. Those local factor inputs are declared rather than represented as a completed D_T or final PP estimate.

Still required:

- Establish concrete eta, grouped psi and plateau derivative constants at the required orders.
- Bind actual right-closed atom plateau and the full chart equality.
- Integrate the compact rectangle derivative bounds into D_T and perform the required Pi/EuclideanSpace measure transport.

## transfer_lambda

Accepted scope: All-k actual Family integer-bank Lambda/log proper-power correction: uniform amplitude, literal bad-occurrence box payment and exact atlas-to-prime identity.

Source: `goldbach-proof-continuation/docs/source-only/20261028-resume-30/transfer_lambda/Part3AllKFamilyLambdaCorrectionBound.lean`. SHA-256 `5f78dd9a9bdb228388e4b219845ab0d6a0385513695fff58dd27596f8fe703b6`.

- bankWeight is the actual Family listExtension on all integer words. Its coordinate/product support and a single C*log(T+2)^B amplitude are derived from the original Family, with constants chosen before T, k, charts or test kernels.
- The exact Lambda/log coefficient is bounded by one (1/e on a proper prime power). Rough and smooth tuple factors are bounded separately. A nonnegative covering sum preserves repeated bad occurrences by a valid overcount.
- The proper-power correction is charged to literal occurrence-indexed boxes using the actual sqrt/log cardinal budget, with no desired asymptotic error supplied as a premise.
- The all-slot rough projector is removed from the prime side only after the active lower coordinate scale exceeds z. roughWord_eq_product uses multiplicativity under z>=0.
- family_atlas_sub_primes_exact and family_atlas_to_primes_bound use the same arbitrary complex test kernel in the atlas, prime sum and correction. Thus count, exact mean or a signed q-sum can be substituted without changing coefficients; payment of that signed q-sum is still open.

Premise/scope audit: The actual manuscript W_N is not manufactured as a Family. The finite norm/cardinality bound is a real local result; chart-scale asymptotics and full same-rho signed modulus costs remain explicit obligations. No hPP or final power-saving envelope is assumed.

Still required:

- Construct the actual physical W_N/selected-test Family instance.
- Attach actual geometric chart scales, lower scale, power saving and the complete chart-label sum.
- Pay the same-rho signed modulus/divisor kernel, separate product=T from product!=T, and finish sorting/collision and whole-PP insertion.

## transfer_power

Accepted scope: Same-rho signed proper-power row cost, actual nonzero-distance divisor payment and separate complete-product collision budget.

Source: `goldbach-proof-continuation/docs/source-only/20261028-resume-30/transfer_power/P5ProperPowerSignedModulusPayment.lean`. SHA-256 `394b492b0a9acb06c788589e900ad7e117e3e397387a7c0f122028daea36afa4`.

- The complex signed row is exactly congruence count minus the exact coprime mean with the same rho. The mean cost is sum_Q |rho(q)|/phi(q), rather than a substituted positive coefficient.
- For b!=t the actual congruence moduli lie among divisors of the positive distance |b-t|. At b=t a separate physical #Q cost is used; divisors(0) is never used to justify that collision.
- q=1 cancellation is proved exactly. Total division at q=0 is harmless in the finite inequalities: it cannot enter the nonzero-distance congruence fibre and is included in the collision cardinal overbound.
- The marked signed proper-power source and its licensed HB atlas are bounded by the same explicit row budget. For nonzero t, coordinate divisibility injects ordered integer words of product t into (divisors t)^k, yielding tau(t)^k.
- The complete-product collision b=t remains distinct from the ordered prime-square diagonal r=q. No unweighted O(sqrt(N)) receiver count is used to pay this signed source.

Premise/scope audit: Amplitude is needed only on the original physical Q. An original Licence, actual word amplitudes and finite support are explicit. The finite row and collision bounds do not assume the final proper-power envelope, divisor-moment asymptotic or signed PP conclusion.

Still required:

- Supply the actual all-k original W_N licensed extension and Lambda/log prime/proper-power partition.
- Bound actual proper-power word amplitudes and noncollision reciprocal-tail sum.
- Establish divisor/tau and reciprocal-totient aggregate asymptotics at the full physical range, then finish ordered bad mass, r=1 and final transfer.

## transfer_trace

Accepted scope: Actual rounded finite compiler support, same-rho original-prime source lower identity and uniform correction payment, specialized to literal current first-row integer retention.

Source: `goldbach-proof-continuation/docs/source-only/20261028-resume-30/transfer_trace/P2CompiledCausalPrimeSourceLower.lean`. SHA-256 `fecc55f011fbacda448ffc99410984c69e7de0f3241b75d46cdab88b6b4b63ea`.

- The source uses the actual rounded compiler rho, not an asserted equality with a raw retained-tree coefficient. Enlarged rough-universe support is proved positive, squarefree and target-coprime; active support is precisely nonzero rho.
- Finite Fubini and the compiler pointwise minorant apply directly to the original prime receiver. The decomposition preserves one compiled rho in the physical main density, exact finitePrimitiveDiscrepancy and both prime corrections.
- Absolute correction cost follows from |rho|<=1, not rho>=0. Given a sublinear physical support exponent, one eventual threshold pays corrections uniformly before later plans, meshes and caps are chosen.
- The full-policy lower statement consumes the actual raw-density reserve and its defined roundingLoss and beta error. It assumes neither a numerical lower coefficient nor hLower. The current specialization uses retainEven and the literal Upsilon1 cutoff 417/5000.

Premise/scope audit: A physical support envelope is still supplied, and a sharp original-prime PP bound must be proved for exactly this compiled rho. The source does not equate Upsilon1 (which includes receiver one) to a completed D12/semiprime lower bound or construct a licensed causal CapPlan.

Still required:

- Construct the original licensed selected CapPlan and source-form branch gates.
- Prove vanishing roundingLoss, chamber coverage, row-integral convergence and the sharp full raw density.
- Prove the same-output physical support exponent and sharp original-prime PP discrepancy, then attach the other ten Chen entries, paired mask, D12 and final count subtraction.

## Acceptance boundary

These verdicts record independent source-level mathematical progress. They do not establish elaboration, kernel verification, an import/axiom closure, any full original task, or formal credit. The JSON records exact final registry/report hashes and every checked explicit dependency pair. No demonstrated new manuscript gap was found.
