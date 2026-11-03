# P3.6 — complete joint discarded payment and actual retained reduction

Base: `2638981ed317e4fa11fc1bf91d2ece442c41dd38`.
Frozen mathematical baseline underneath it: `124d09f9fc74e7b78261e2471a573f1657b5633e`.
Branch: `chatgpt/p3-joint-discarded-payment-20261103`.
Packet: `docs/source-only/20261103-p3-joint-discarded/`.

**SOURCE-WRITTEN / UNCOMPILED / KERNEL-UNVERIFIED. FULL P3.6 REMAINS OPEN.**
No Lean/Lake/compiler, proof guard, finite producer, numerical replay, CI dispatch or kernel replay was run. No independent mathematical review or transitive-axiom acceptance is claimed. Previous production and frozen packets, constants, manuscript, and the excluded full87 branch are unchanged.

## Scope advanced

The previous commit paid the actual outside-pair upper/order rejection. This continuation supplies the joint original low trim and enlarged lower rejection, assembles ALL discarded mechanisms, and proves an exact reduction of the ORIGINAL gammaDiscrepancy to directly defined retained rows. These are bounded actual-source proofs, not a claimed complete same-rho PP theorem.

The new source contains three modules:

- `P2GammaJointLowProductPayment`: joint low-label count, finite same-rho kernel bound, and power-cutoff logarithmic accuracy.
- `P2GammaJointDiscardedPayment`: actual combined low weight, literal original-source identity, occurrence-list assembly and all-discarded payment.
- `P2GammaJointRetainedReduction`: exact Cartesian reconstruction and a concrete chosen-width/grid/trim endpoint with no cutoff or grid-cover licence left as an input.

## Joint low-product argument

Write k for the mother-word length, L=1+log N, J>=(k+3)^2-1 and E=max(J+2,15). The two old primes are still separate labels inside R17's jointLabels. Let a_m be its ACTUAL complete-product fibre cardinality.

The existing joint divisor square moment, together with integer a_m<=a_m^2, gives

`card {z in jointLabels : jointProduct z <= Y} <= Y*L^J`, for 1<=Y<=N.

There is no product-map injectivity assertion, no division by fibre cardinality, and no multiplication by pairSupport.card. Unit quotients and every original word position are retained. The prior joint kernel energy is reused, not reproved:

`sum_z (tau(N-jointProduct z)+4L)^2 <= 34*N*L^E`.

Every source product lies strictly between 0 and N. Restriction to the low labels and the existing scaled Young inequality then give

`abs(jointError) <= u*Y*L^J + 34*N*L^E/u`, u>0.

For Y<=C0*N^(1-kappa), choose u=N^(kappa/2). The bound is at most

`(C0+34)*N^(1-kappa/2)*L^E`.

The existing `eventually_powerLog_le_logAccuracy` supplies arbitrary absolute logarithmic accuracy. Fixed parameters precede one N threshold, before all later words, cuts, moduli, rho and weights. The concrete weight's height and support are PROVED below rather than left as analytic licences.

## One actual weight pays both low terms

For s=smoothTrim(T,m), the new weight is

`lowDiscardedWeight = (1-s) + wordLowerRejectedWeight`.

For nonempty words this is `(1-s)+s*r`, where r is the EXISTING actual lower-rejected grid weight. The old partial-hat partition supplies 0<=r<=1, hence the combined weight lies in [0,1], not merely [0,2]. Empty words keep the original trim remainder and zero lower rejection.

With T>0, H>=2T and delta>=0, both terms vanish above the actual integer cut

`Y=ceil(H*exp(4*delta))`.

Q16's exact `eventually_enlargedCut_bounds` supplies Y<N and its uniform sublinear upper bound for H<=C0*N^(1-kappa), delta<=delta0. Positive H supplies Y>=1. No invented cutoff comparison or relative-mass assumption is introduced.

`originalJointLowError_eq_original` identifies the complete outside/mother sum with the existing gammaDiscrepancy-minus-smoothTrim expression PLUS the originalLowerRejectedKernel, using precisely the same rho and q-coprime mean. All mother repetitions remain list occurrences.

Combining this result with the previous upper/order source gives

`eventually_originalJointDiscardedError_height`.

For fixed C>0, 0<kappa<1, C0>0, delta0, A and eta>0, one threshold covers every later 0<=sigma(t)<=C, modulus family Q subset [1,N], |rho|<=1, legal T,H,delta,K and the existing common order mesh. Its conclusion is the absolute eta*N/(log N)^A bound on ALL discarded terms. C is fixed before N; no N-dependent selector-height maximum is used.

## Actual retained source, not a difference-defined object

`retainedWordKernel` is a direct finite Cartesian sum using the original headCarrier, rootComplementLabels, complexWeight and betaLabel. It is not defined as original-minus-an-error. Q16's exact complex reconstruction is specialized to the actual gammaKernel and then projected to real parts.

A possible EMPTY mother word is explicitly retained as its unchanged smooth-trimmed root-label sum. This avoids a hidden nonempty-word assumption. No claim that this lane is absent, or that all retained lanes already qualify for the prime-conductor theorem, is made.

The proved source identity is

`originalJointGammaError = originalJointRetainedError + originalJointDiscardedError`.

It preserves the literal original occurrence list, outside pair labels, quotient 1, coprime mean and rho. The nil lane is not silently dropped.

Finally take concrete analysis parameters

`T=N^(1-kappa), H=2*T`,
`delta=boundaryLogMesh(orderMeshExponent(jointListMomentOrder(originalMotherOccurrences), A), N)`,
`K=ceil(log(N)/delta+1)`.

Positive width, width<=1, sublinear H bound and grid cover are discharged. The final declaration is

`ImbalancedChen.P2GammaJointRetainedReduction.eventually_originalJointGamma_retained_reduction`.

For fixed C,kappa,A,eta it proves the absolute difference between the actual original joint error and these explicit retained rows is <=eta*N/(log N)^A. No Y, thin-source cardinality, kernel energy, cutoff-growth or grid-cover estimate is a premise of this final endpoint. These analysis choices do NOT identify the causal physical rootQ with a common Qphys.

## Reuse and source inspection

The previous three modules and receipt files were read from the mounted six-file archive, with the parent GitHub commit/tree checked. P/Q/R source bodies and registries were retrieved at the frozen baseline. In particular the original trim, lower split, actual Cartesian reconstruction, enlarged-cut bound, joint source, moments and joint upper/order proof are reused. The original PowerErrorBudget and BoundaryArbitraryLog suppliers were read; no new external analytic theorem was imported.

The S PP review was found at its ACTUAL nested path:

`docs/source-only/20261102-resume-30s/S/s29_review_actual_pp/REPORT.md`.

It accepts bounded R17/R18/R19 source claims but leaves full PP open and records missing S19/S24 completion. This is upstream review evidence only, not an independent review of the present files. No exhaustive search of private/unpublished local drafts is claimed. The original manuscript itself was not independently re-fetched; this continuation proves statements about the already defined original finite sources, and manuscript references remain inherited provenance.

## Remaining P3.6 obligations

1. Actual causal selected-family/mother/marks and a scalar-height supplier with the required quantifier order; identity between the t-dependent original rootQ and ONE common physical Q on the selected family.
2. Positive-Theta relative mass/error control. An absolute log-saving and mere positivity of Theta do not imply the required uniform relative error. The zero-Theta result remains separate existing work.
3. Retained chart/mother/conductor summation on the same actual rho, enhanced/high-rank covers, the full coupled profile norms and post-loss costs. The retained empty-word lane must also be handled if it occurs in the literal family.
4. Full same-rho PP assembly and the downstream hUniformPP/hLower/hUpper suppliers. P3.5 spectral prerequisites are not discharged by discarded-side reduction.
5. Dependency materialization, exact-source compilation, independent kernel replay, transitive-axiom inspection and independent mathematical review.

No complete P3.6 or unconditional Goldbach claim is made. No constants c/K or theorem endpoints were changed.

## Proposed tracker insertion

```text
黄｜P3.6 把估计实例化到同一rho和实际PP源族
    蓝｜完整外层joint低端trim/lower及upper/order统一绝对付款、原始Gamma到实际retained行的同rho精确还原与具体网格源码
    黄｜实际causal正标记族与共同物理Q、positive-Theta转换、retained全族同rho PP总装
```

This is a scoped source-coverage proposal, not a mutation of the user's external tracker. The blue line does not mean verified compilation or full parent closure.

## Verification handoff

`REGISTRY.json` records exact new bytes, Git blob hashes, declarations and direct-import locations. `VERIFY.lean` is an UNEXECUTED type/axiom inspection driver. The intended module paths must be materialized in the pinned environment before using the existing verification procedures. A docs-only commit does not join the production import closure automatically.

Completed local checks are source-text inspection, new-source admission/axiom/unsafe/native_decide/evaluation token scan, declaration inventory, JSON parsing and file hashes. These are not Lean elaboration or kernel evidence. There was no independent reviewer in this turn and no remote build dispatch.
