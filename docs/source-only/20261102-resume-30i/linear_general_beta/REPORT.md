# I linear_general_beta: original physical LINEAR discard, arbitrary fixed B

Status: the focused source proof is complete, pending independent review and user compilation. `local_step_complete=true`; the broad original medium task remains `task_complete=false`. All four modules are uncompiled, kernel verification is false, and formal credit is zero. Assigned model/effort: `gpt-6-astra` / `xhigh`. No compiler, build, CI, finite mathematical execution, checker, quota inspection, subagent, commit, or edit outside this I directory was performed.

## Original obligation and source

The actual current manuscript is `../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex`, SHA256 `ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`. Proposition `prop:current-medium`, lines 126–164, has the original arbitrary fixed divisor order `B`, one-bounded alpha, `|beta_m| <= tau(m)^B`, separate one-bounded primitive gamma sequences, moving signed residue, physical modulus `q1*q2*q3`, and the original coprime mean. The current formal caller is `ImbalancedChen.Part3.RestrictedMediumObligation` in `ImbalancedChen/Part3DistributionTargets.lean`; this full caller is not proved here.

The internal completion note is `../chen-imbalanced-semiprimes/paper/source/modules/distribution-medium-completion-20261010.txt`, SHA256 `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`. Lines 94–111 derive the physical `x^(4/5)` cap and explain the collapsed divisor coefficient, primitive Shiu count-plus-mean and Rankin sum (8). Lines 126–136 discuss a separate beta normalization route for the full medium theorem. Lines 156–160 require deleting `nm=a` before Cauchy while leaving its mean unchanged. This delivery completes the earlier LINEAR deletion directly for the original beta using a higher Shiu moment, so it does not need that later truncation argument or its additional fixed kappa cap.

The frozen H count/payment and support modules were read. H has a real B=0 LINEAR proof, not a general-B one; its original physical carrier inclusion and original smooth-support proof already quantify arbitrary B. G's actual modulus reindexing and original signed S123 entrance were also read. No S2 squared-tail surrogate replaces the LINEAR source. All imported source-only modules require installation under their recorded `ImbalancedChen` names; no installed or compiled status is inferred from a file's existence.

## Proof and exact parameters

1. `Part3OriginalLinearDivisorMoment.lean` proves the genuine coefficient envelope. For an actual physical pair `(n,m)` with positive product `v=nm`, divisibility gives `m.divisors subset v.divisors`, hence `|alpha_n beta_m| <= tau(v)^B`. The actual product fibre injects into `v.divisors`, so its total absolute coefficient is at most `tau(v)^(B+1)`. The original Cartesian carrier lies in the existing actual-paperPsi carrier because that cutoff equals one on the original beta support. The product-image positive-support lemma excludes zero before any divisor argument. A nonnegative test-function theorem transports both the true progression count and the total mean mass to the independently defined physical product moment.

2. `Part3OriginalLinearHigherShiu.lean` applies the existing foundational `PrimitiveShiuTauBoundary C alpha kappa` at arbitrary fixed moment order C. Every actual product lies in the old four windows `X=H=2^j*floor(x/2)`, `j<4`; their lengths sum to `15*floor(x/2) <= 15*x/2`. The signed residue is converted to its genuine least nonnegative representative and its coprimality is proved using the old exact dictionary. Native X0, H positivity, `X^kappa <= H`, `H<=X`, and `ell<H^(1-alpha)` gates are proved. The existing Mertens theorem pays the displayed Euler exponential by `D_C*log(X)^(2^C)`. We bound `1/log(X)` by `1/log(2)`, losing one harmless log relative to the sharp exponent. The result is

   `moment_C(ell) <= K_C*x*log(8*x)^(2^C)*tau(ell)/ell`,

   where `K_C=(15/2)*hShiu.A*uniformEulerConstant(C)/log(2)`.

3. `Part3OriginalLinearGeneralBetaPayment.lean` takes `C=B+1`. The exact original deleted discrepancy is bounded by `moment_C(ell) + moment_C(1)/phi(ell)`. The q=1 Shiu instance supplies the ordinary moment; `1/phi(ell)<=tau(ell)/ell` pays the unchanged coprime mean after its norm is enlarged. Thus the count plus mean costs at most `2*K_C*x*log(8*x)^(2^(B+1))*tau(ell)/ell`. The original filtered gamma coefficient costs `tau(ell)^3`, and its nonzero support is primitive and lies in the exact H collapsed smooth filter, including boundary primes and repeated prime powers.

   **The required collapsed modulus order remains 4 for every B.** Primitive Shiu's original RHS has no extra `tau(ell)^B` factor: B increases its Euler/log exponent. We use the proved order 4 tail, not a pointwise divisor estimate and not an unjustified B-independent logarithmic exponent. Requesting Rankin precision `A + 2^(B+1)` absorbs this fixed loss. The explicit scalar multiplier is `2*K_(B+1)*8^(2^(B+1))`. One threshold includes the Rankin threshold, `3*X0`, `3^9+1`, `10^10`, and `exp(1)+1`, and is chosen before sigma, kappa, c0, every atom, its residue, and all moduli. The theorem is `original_general_beta_linear_discard_log_payment B hShiu A hA`.

4. `Part3OriginalS123GeneralBetaPaidLinearEntrance.lean` inserts the bound at precision A/2 into G's actual signed entrance at arbitrary B. The common threshold is `max (max Xe Xd) (exp 1)` and constant is `Ce+3*Cd^2`. The final theorem is `uniformAuxiliarySW_general_beta_original_signed_source_paid_linear_entrance F B C0 sigma kappa c0 hadmissible hSW hsigma hc0 hShiu A hA`. Its RHS is literally the H B=0 residual expression, now for the original general B: original key-bank cardinality, `outerL2`, factor two on S2 and every signed real part are preserved. Only the previously unpaid `3*norm(discardedSource)^2` is removed. Beta, alpha, all coefficients and the physical coprime mean are unchanged.

## Eliminated obligations

- General-B physical coefficient and actual product-fibre multiplicity, with positive support proved.
- Higher-moment primitive Shiu count, including its true moving-residue and native progression gates.
- The original LINEAR discarded coprime mean via the q=1 instance of the same genuine moment boundary.
- Actual gamma/support binding to the required collapsed Rankin order, with the B-dependent log exponent paid.
- Uniform arbitrary-log LINEAR discard payment for every fixed B and its exact original signed S123 consumer.

No conclusion-sized estimate, source equality, progression bound, residual bound, or abstract coefficient supplier is a hypothesis of any new theorem. The generic nonnegative test function in the finite fibre lemma is a reusable algebraic statement; the actual count-plus-mean consumer constructs it explicitly.

## Genuine external input and remaining gaps

The sole analytic boundary introduced into these theorems is the already existing `PrimitiveShiuTauBoundary (B+1) (1/10) (1/10)`, defined in the pinned `Part3MediumPrimitiveShiuWindowGate.lean`. Its documented source is Shiu (1980), Theorem 1, as restated in Wright, arXiv:2508.17217v1, Theorem 1.1. The exact existing interface asserts constants A>0 and X0>=2 before natural X,H,q,b, with `X0<=X`, `H>0`, `q>0`, `X^kappa<=H<=X`, `q<H^(1-alpha)`, and `q.Coprime b`, and bounds the tau^C sum on `[X,X+H)` by `A*H/phi(q)/log(X)` times `exp(2^C*sum_{p<=X,p not dividing q} 1/p)`. It is a genuine foundational input, not an externalized medium/error theorem. A kernel-verified supplier at order B+1 remains open, exactly as the prior order-one supplier did. Existing Mertens/divisor/Rankin source results are reused, not replaced by new external assumptions.

The final signed theorem still exposes actual retained Poisson source, S3 `remainingCorrectionKey`, `roughReplacementCorrection`, `genuineDiagonalZero`, S2 `actualS2NonzeroModes`, `otherRoughCorrection`, and `singleZeroCorrection`. Their estimates and full spectral/dispersion/P1/P2/internal-K/PP assembly remain internal. The general-beta truncation proof needed elsewhere in the full medium theorem is not claimed here. No suspected new manuscript mathematical gap was found in this LINEAR obligation; the gaps listed above are implementation, external-supplier, and assembly gaps, not a claim that the manuscript statement fails.

The interface was sent to `/root/i_medium_assembly`. That task froze its existing all-B correction payment and B0 signed consumer separately; no provisional I-to-I import is included here. Combining its frozen all-B S2/S3 arithmetic payment with this general-B entrance is a narrow remaining assembly step for root to schedule. H/current production files were read only.

## Frozen source hashes and installation

- `Part3OriginalLinearDivisorMoment.lean`: `c437cd3873fac710f6213a3d59ed335f0e8f5373af1f1ee83fca2aeb60fe2273`.
- `Part3OriginalLinearHigherShiu.lean`: `a7cc50182cea4e1b02589ec0f2bb8523702a1692173b4c76e2871124c394b643`.
- `Part3OriginalLinearGeneralBetaPayment.lean`: `07f1f1ac53130b9f2cb87474f2e21774075f78dd9cf93b9cd30c79bf3505fd19`.
- `Part3OriginalS123GeneralBetaPaidLinearEntrance.lean`: `512a0ad4e884d1c786c4dda4b52f2f7f62314a6d07a0f7ec337d19773b102b11`.

Install each under `ImbalancedChen/<same filename>`, in the order above, with the pinned predecessors in `REGISTRY.json`. The source revision observed was `25afcbff11562df51ef7ac5113c879123fcd64c6`; current working-file bytes, not that revision alone, are the dependency authority. Mathlib is pinned by the current manifest at `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; the local `.lake/packages` directory is absent, so no installed Mathlib source/compilation evidence is claimed. The registry pins the direct imports and relevant read upstream declarations, not a newly audited full transitive import graph. Final REGISTRY and REPORT hashes are delivered to root separately to avoid self-hashing cycles.
