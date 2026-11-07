# K s3_large_shift: original cutoff deletion and reinstatement

Status: **the local original cutoff/reinstatement supplier is written, conditional only on the existing precise primitive Shiu boundary; the broad S3/medium target remains OPEN**. The four Lean files are static source candidates. `compiled=false`, `kernel_verified=false`, `formal_credit=0`. Independent review and elaboration are pending. Only this K task directory was written. No compiler, Lean/lake/build, CI, certificate or finite mathematical execution, Git operation, quota query, or subagent was used.

The task row and K README were read, together with the current original manuscript, its detailed medium completion, the I close-pair source and H restoration source, and the current J gcd and frozen-Cauchy code/metadata. The J shifted-S2 source was additionally inspected and reused for its actual primitive Shiu interface and signed translated-window theorem. REGISTRY records the actual selected paths and current raw hashes, including uninstalled drafts. The recorded model/effort comes from the assigned TASKS row; runtime identity was not separately queried.

## Original source and ranges

The manuscript body at lines 125–168 fixes theta=7/32, `0<sigma<1/100`, `0<=kappa<=sigma/100`, arbitrary fixed beta divisor order B, signed residue `c0*x<=|a|<=x^(1+kappa)`, and its four original medium monomial inequalities. Lines 191–236 retain exact-product deletion, principal variance and the later retained phase, and distinguish preliminary logarithmic errors from the spectral power return. Original global `c=49044063/25000000` and `K=8452171/1250000` are unchanged. The cutoff exponent below is a separate local parameter, not the global c.

The detailed `distribution-medium-completion-20261010.txt` is more explicit:

- Lines 114–124 define the actual independently labelled Lambda sum and occupied-key geometry.
- Lines 141–154 derive the translated signed divisor progression theorem (10) from primitive Shiu.
- Lines 156–168 delete exact products before Cauchy and keep the two zero-restoration orders separate.
- Lines 169–171 discard large coefficients or large `tau(m*n_i-a)`; lines 179–181 remove close pairs and then reinstate the coefficient cutoffs while both shifts remain nonzero.
- Lines 183–190 restore only the two single zeros before CRT/Poisson. A double-zero diagonal is expressly excluded.
- Lines 212–217 describe a later, distinct zero-mode restoration; lines 251–257 give the original outer Cauchy normalization.

Here `N=atom.U`, `M=atom.V`, `x=U*V`, `Y=Q1*2^k.d`, and `V(D)=M*N^2/Y`. The source is the exact `offDiagonalCarrier`/`PairIndex`, original `S3DeletedTerm`, common physical q,d,m, independently labelled r,n1 and s,n2, original `lambdaTrim`, alpha, primitive-q filter and `jointPsi`. The smooth m carrier reaches `5M/2`, so the product cap is **5x**, not 4x. Numeric z is converted by `strictReceiverCutoff`; the original instance is z=`roughZ x`, y=`roughY x`.

The earlier phrase “large shift” means failure of the two **divisor-count** cutoffs on nonzero shifts. It does not mean a new upper bound on `|m*n-a|`, and it is unrelated to J's later signed quotient `f=(n1-n2)/(q*d)`. No q-to-q*d renaming, smaller cutoff, extra kappa cap, new SW assertion, or frozen-source equality is used.

## Actual arithmetic localization

`Part3OriginalS3LargeShiftLocalization.lean` proves a positive-mass estimate strong enough for both deletion and later arithmetic-mask reinstatement. Let

```
Mass(H) = sum_{actual off-diagonal t, not ShiftCut(H,t)} norm(S3DeletedTerm(t)).
```

Active deleted terms force **both** shifts nonzero. Orient each pair so that the first shifted divisor count dominates the second. The literal flip of the two physical pair labels preserves the carrier and the norm. Ties are explicitly paid by a factor two. This norm symmetry concerns only the original physical product; no Hermitian property is asserted for J's independently polarized E3 packet.

In the dominant orientation, let `W=tau(|m*n1-a|)`. The existing exact coefficient extraction gives each Lambda norm at most W. The common primitive residue gives `n2=n1 (mod q*d)`. The alpha interval `[N,2N]` and `q*d>=Y/2` give at most `2N/Y+1` possible n2. The explicit inherited `closeCode` and decoder retain all original labels: q,d cost W squared, r and s cost at most W squared, and the two Lambda factors cost W squared. Thus

```
Mass(H) <= 2*(2N/Y+1) * sum_{actual (m,n), shift != 0, tau(shift)>H} tau(shift)^6
        <= 2*(2N/Y+1)/H * sum_{actual (m,n), shift != 0} tau(shift)^7.
```

The endpoint one is retained. There is no pointwise subpower estimate multiplied into a logarithmic error. The actual Lambda coefficient cutoff follows from the same divisor cutoffs, since `d*r` and `d*s` divide their respective nonzero shifts. The proof does not require an independent coefficient-support premise.

The arbitrary-mask theorem bounds the norm of the difference between a masked deleted source and its cutoff restriction by this same positive mass. It does **not** compare the norm of a masked oscillatory sum with the norm of its unmasked sum.

`Part3OriginalS3LargeShiftProductMoment.lean` then injects actual `(m,n)` into `(v=m*n,m)`. Positivity, the original smooth cap, and exact-product deletion prove `1<=v<=floor(5x)` and `v!=a`. Its explicit decoder and divisor carrier give

```
sum_{actual nonzero (m,n)} tau(|m*n-a|)^7
  <= sum_{1<=v<=floor(5x), v!=a} tau(v)*tau(|v-a|)^7.
```

The factor-pair multiplicity tau(v) remains inside its mean. There is no absolute-value reindexing of the signed product variable and no tau(0).

## Fixed-order Shiu payment

`Part3OriginalS3LargeShiftShiuPayment.lean` uses the elementary inequality

```
a*b^7 <= a^3+b^12  (a>=0, b>=1).
```

This permits the **same order-12 primitive Shiu boundary already used by J s2_shifted**. The ordinary tau-cube mean is derived from the existing Fouvry divisor-moment theorem. The shifted twelfth moment is transported through J's signed source at Shiu modulus one, on `[1-a, floor(5x)-a]`. Every polynomial-location, width, modulus and native-X0 gate is supplied. The threshold is J's existing

```
max(10^10, (2*Shiu.X0+32)^80).
```

The weak location condition kappa<=1 is deduced from the original kappa<=sigma/100 and sigma<1/100. No application-only elementary kappa cap is substituted. The sign split, translated cover, small branch, Euler conversion and overlapping-window costs are those of the actual existing TwoSigns source, pinned in REGISTRY.

With fixed `E=2^12`, the proof obtains a positive explicit constant `Cmom` independent of requested precision and all moving data such that

```
seventh actual moment <= Cmom*x*log(x)^E.
```

For local precision D, set the **original** logarithmic cutoff exponent `Ccut=D+E`. This is exactly the manuscript's instruction to choose Ccut after its fixed moment exponent. Before absorbing the endpoint, the arithmetic bound is

```
Cmom*(4*V(D)+2*x)/log(x)^D.
```

Original occupied-key geometry gives `x<=V(D)` at one uniform threshold, yielding `Mass <= 6*Cmom*V(D)/log(x)^D`. The original rough cutoff is not changed.

The external port is `PrimitiveShiuTauBoundary 12 (1/400) (1/400)`, with its primitive progression, native X/H/q/b ranges, initial threshold, totient and Euler exponential intact. I checked it against [Shiu's theorem as stated in Wright, Theorem 1.1](https://arxiv.org/html/2508.17217v1#S1). Fixed tau^12 satisfies its multiplicative-function conditions. This is the classical primitive theorem, not the manuscript's translated estimate (10), a shifted moment, a largeShift bound, or a final-medium estimate renamed external. A verified supplier of that boundary remains necessary. The inspected backup Mathlib NumberTheory text search found no Shiu declaration; this is not an exhaustive library-absence claim.

## Signed reinstatement and exact receiver

`Part3OriginalS3LargeShiftResidual.lean` independently defines `uncutCoprimeFarDeleted` with only the original far condition and r/s coprimality. Both shifts remain deleted. The exact identity is

```
uncutCoprimeFarDeleted = coprimeFarFull + coprimeFarReinstatement.
```

The reinstatement norm is at most Mass. Combining the actual I/J source identities gives

```
primitiveS3 = uncutCoprimeFarDeleted + badPairDeleted + closeDeleted
  + actualDiagonal + (largeShiftDeleted - coprimeFarReinstatement).
```

Here the two positive single-zero additions in `largeShiftFull` cancel their two negative occurrences in H's restoration correction. The genuine deleted diagonal remains. No double-zero diagonal is restored.

For the existing norm ledger, the proof conservatively pays

```
2*Mass + norm(actualFirstZero) + norm(actualSecondZero).
```

H's original component theorem supplies the two single-zero norms. For final precision A the local precision is the unchanged `D=outerPrecision(B,A)=A+betaMomentOrder(B)+12`; the cutoff exponent is therefore `D+E`. The outer receiver is literally

```
originalNumericKeys.card * sum_k outerL2(atom,k) * (the displayed correction).
```

The proof supplies `outerL2<=6*Y*betaL2`, the ordinary beta divisor-square mean and **both** key-bank multiplicities. With `L=12*Cmom+2`, its coefficient is

```
12*L*betaLogConstant^betaMomentOrder(B)*(2*keyLogConstant)^12.
```

The final theorem `exists_actualResidualFunctional_cutoff_paid` bounds the independently defined, unchanged `actualResidualFunctional` by an explicit `unpaidOriginalCutoffFreeLedger` plus `C*x^2/log(x)^A`. Fixed Shiu input, B, sigma, kappa and A precede constants and threshold; c0, atom, signed residue, receiver and key follow. The original z=roughZ instance is included. No estimate for the unpaid ledger is a premise.

## What remains open

The cutoff-qualified close and r/s-gcd payments remain the actual I/J suppliers. This delivery removes the earlier large-value cutoff and its reinstatement as internal estimate ports, subject to the genuine primitive Shiu boundary. The broader P3.5 leaf remains OPEN:

- Original n1/n2 and s/ell gcd exclusions; uncutCoprimeFarDeleted is not asserted to be clean E2.
- The final clean-source single-zero restoration, CRT/Fourier dictionary and close/gcd **zero-mode** restoration. Paying physical cutoff corrections does not identify a cleaned principal term.
- Omitted modes, retained Fourier diagonal, roughReplacementCorrection, genuineDiagonalZero and the four original S2 norm ports, all retained in the final unpaid ledger.
- J's frozen reciprocal masks, coefficient coloring, retained-phase Abel debit, Cauchy normalization, post-Cauchy enlargement, completed smooth-piece dictionary and spectral return; full S123, restricted-medium and same-rho PP assembly.
- A verified primitive Shiu supplier, exact dependency installation, independent source review and user-owned compilation/kernel verification.

No manuscript counterexample or mathematical obstruction was established. The earlier absent cutoff supplier was an internal arithmetic/source derivation, not a source-notation impossibility. The known inherited draft `Part3MediumLiteralS3DeletedCarrier.lean` still has the displaced second hmod branch following `deletedIndicator_norm_le_one` (lines 44–56); this is an inherited source/elaboration blocker, not a manuscript contradiction. It was not edited. The actual local Mathlib Tactic installation path is absent. Source hashes are provenance, not a claim of a resolved or verified import closure.

Install in Localization, ProductMoment, ShiuPayment, Residual order at the matching `ImbalancedChen/` filenames only after root review. Delivery bytes are frozen with REGISTRY; notify root before any later change.
