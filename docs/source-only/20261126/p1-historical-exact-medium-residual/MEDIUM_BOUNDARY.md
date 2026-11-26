# P1.5 literal historical medium: bounded source review

Status: READ-ONLY MATHEMATICAL/API REVIEW; SOURCE ONLY; NOT ELABORATED.
This review proves no new nonzero medium payment. No Lean file was added,
no Lean/cloud/Git operation was run, and no existing proof, frozen manuscript,
source manifest, acceptance record or prior draft was changed. The findings
are limited to the named local sources and already recorded P3 increments.

Baseline source root:
`/workspace/scratch/76f3bdb16a38/goldbach-p15`.
The exact-medium source previously reviewed and frozen remains at
`/tmp/p15-exact-medium/P1OriginalHistoricalExactMediumResidual.lean`.

## 1. Outcome and precise scope

There is no newly supplied estimate for a nonzero summand of the literal
`historyMedium` in the inspected chain. The existing singleton U06 result
does pay a specified short-head, low-first, rough-rank-three contribution,
but that result already existed and its channel is `products P / free P`.
It is not an estimate for arbitrary historical `Q / trueDDeltaRho`, and its
explicit remainder cannot be set to zero.

Two separate connections are required before that existing partial payment
can be promoted to a historical medium contribution:

1. Supply the original actual-policy coefficient/factorization dictionary,
   including its real complete-modulus filter and any physical/free collision
   correction, for the same source, N and signed coefficient.
2. For the complement of the already paid short-head rank-three subset,
   supply the full signed medium bound on that actual fixed family. Existing
   admissibility and auxiliary SW do not themselves supply that bound.

This is an unclosed source/provider chain, not a proof that the frozen
manuscript is false or that its actual physical family violates a scale gate.
The known FixedM/source-owner searches were not repeated.

## 2. The literal target and the existing coefficient boundary

The frozen exact-medium module defines

```lean
def mediumAtlasSum (kap zeta : ℝ) (K N : ℕ)
    (Q : Finset ℕ) (c : ℕ → ℝ) : ℂ :=
  ∑ js ∈ chartBank (2*N) 1,
    mediumAtlas (actualLicence kap 6 N) K (2*N) N kap
      (originalMediumLow zeta js) (originalMediumHigh zeta js)
      Q (fun q => (c q : ℂ)) js

def historyMedium (B kap zeta : ℝ) (K : ℕ)
    (old fresh : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : ℂ :=
  mediumAtlasSum kap zeta K N
    (historicalModuli B old fresh N cap w z)
    (trueDDeltaRho old fresh N cap w z L)
```

These are the existing definitions, not new compiled declarations.
The original history has kap in both its licence
and complete-product eta. The actual policy signs remain:

| Channel | old | fresh |
| --- | --- | --- |
| comparison | `S false` | `R false` |
| saving | `eight false` | `six false` |

Here `R/S` are the original two `eventPolicy` values; `six/eight` are the
original `sixthPolicy/policy` values. These have not been replaced by the
finite-fallback policy carried by `P4BOriginalCollisionWords.Params`.

The latter Params fixes

```lean
P.f   := P4AFiniteFallbackLowRankRho.retain ...
P.rho := P4BOriginalFiniteSmoothCount.coefficient ...
P.S   := P4BOriginalAllRankClassicalRange.wholeHigh ...
```

`wholeHigh` removes the original low rough-rank carrier. By contrast,
`historicalModuli` applies `remainingModuli` to the union of the two actual
physical supports; it retains exactly
`panModulusCutoff N B < d` and `d < N^(599/1000)`.
These are not definitionally the same carriers or coefficient functions.

`P4BOriginalCollisionTensor.difference` and the existing singleton collision
payment preserve their own Params. Neither allows that Params to be changed
to an arbitrary `old/fresh` pair. A new hypothesis asserting coefficient
equality or a missing collision/error budget would hide this first gap.

## 3. Actual available APIs, with their original conclusions

Paths in this table are relative to the baseline root.

| Source | Public API | Available conclusion / limitation |
| --- | --- | --- |
| `docs/source-only/20261120-resume/p1-singleton-medium-rectangles/ImbalancedChen/P1OriginalSingletonMediumRectangles.lean` | `source_to_actual_rectangles`, `original_medium_to_actual_rectangles` | Exact literal medium selector to HB rectangles for arbitrary Q/rho; retains signed HB coefficients and original firstMedium selector. Already proved; do not reprove. |
| `docs/source-only/20261115-resume/p1-singleton-medium-window/ImbalancedChen/P1OriginalSingletonMediumWindow.lean` | `eventually_original_medium_window` | Actual full-product scale, selected medium U, physical N and rough-cutoff geometry. |
| `docs/source-only/20261123-resume/ten-task-continuation/selected-api/ImbalancedChen/P1OriginalSingletonMediumAdmissible.lean` | `eventually_original_admissible`, `eventually_original_with_auxiliary` | Four medium length inequalities, actual coefficient gates and actual auxiliary SW for the existing Params/Index; no signedError bound. |
| `docs/source-only/20261121-resume/manuscript-distribution-and-receivers/ImbalancedChen/P1OriginalSingletonMediumFourier.lean` | `original_eq_fourier`, `retained_mode_reconstruction`, `amplitude_l1_budget` | Exact original fibre Fourier formula; retained mode reconstruction uses products/free of the same Params; L1 costs log(N+2)^72. |
| `docs/source-only/20261123-resume/ten-task-continuation/ImbalancedChen/P1OriginalSingletonShortMediumTriplePayment.lean` | `short_three_boundary`, `eventually_short_three_signed` | Proves the stronger shared-p boundary from actual low-first rank-three geometry and U <= x^(1/16), then pays that native signed atom. |
| `docs/source-only/20261123-resume/ten-task-continuation/ImbalancedChen/P1OriginalSingletonShortMediumSignedRow.lean` | `remaining_reconstruction`, `exists_mode_cost` | Pays the subtraction of the surviving-word mode; same products/free and signed modulus kernel. |
| `docs/source-only/20261123-resume/ten-task-continuation/ImbalancedChen/P1OriginalSingletonShortMediumLiveRow.lean` | `exists_live_row_cost`, `eventually_live_row_removed` | Pays `scalar * occurrenceAtom(products/free) - remainingRow`. Tail, other words and longer fibres remain explicit. |
| `ImbalancedChen/P1Full87TrueDPolicyDelta.lean` | `trueDDeltaRho_test` | Every real test of the signed delta is exactly the fresh test minus the old test on their own physical supports. It is linear algebra, not a physical-family licence or medium estimate. |

The real delta test can be applied to real and imaginary parts with the
original remaining-modulus indicator included in the test. Together with
linearity of the finite Atlas this gives the natural exact reduction to the
two individual policy medium sums. No new Lean proof of that routine
reduction was written here: it would not discharge either missing payment
and must not be advertised as one.

The current historical full-Q Fourier tail and L1 results already exist in
`/tmp/p15-native-followup/P1OriginalHistoricalSingletonFourier.lean`.
They can be reused once the same actual live source is supplied; no new
tail or Fourier-L1 proof is needed. They do not bound the retained medium
mode itself.

## 4. The exact unclosed analytical type

The original source
`docs/verification/20261123-blue-compilation/reindex-isolated/postimages/ImbalancedChen/Part3DistributionTargets.lean`
defines, but does not assert as a theorem:

```lean
def RestrictedMediumTarget {ι : Type*} (F : ι → MediumAtom) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
    ∀ i : ι, x0 ≤ (F i).scale →
      ‖(F i).signedError‖ ≤
        C * (F i).scale / (Real.log (F i).scale) ^ A
```

The exact `RestrictedMediumObligation` type includes fixed B/C0, positive
sigma/c0, the original kappa margin, `MediumAdmissible` for all members and
`UniformAuxiliarySW`. It remains a definition of an obligation. The existing
singleton admissibility/SW APIs provide inputs to this obligation for their
existing Index; they do not prove `RestrictedMediumTarget`.

For a concrete history, the next genuine target is the conclusion above
for the actual fixed family obtained from its original source factorization,
with C and x0 preceding the actual chart, row, complement, mode and owners.
Writing `RestrictedMediumTarget actualF` as a new premise would merely assume
the missing estimate. Nor can `actualF` be invented from a coefficient bound
`abs rho <= 1`; the original whole-atom factorization and its four geometric
gates must identify that exact signed coefficient first.

## 5. Why the existing stronger boundary is not automatic

The three existing `Part3OriginalShared*Family` signedError conclusions use
stronger geometric ranges. In particular the refined API requires

```text
Q1^3 * (Q2*Q3)^4 <= V^2 * x^(-delta),  delta > 0,
```

and the short-LCM API requires

```text
32 * Q1 * Q2^2 * Q3^2 <= V * x^(-delta).
```

Basic medium gates plus the physical .599 modulus ceiling do not imply
either extra inequality. As a scale-exponent check only, take N=x,
U=x^(1/16), V=x^(15/16), Q1=x^(1/32), Q2=x^(9/50), Q3=x^(17/50),
and sufficiently small positive sigma and permitted kappa. Then:

| Exponent | Value |
| --- | ---: |
| Q1*Q2*Q3 | 441/800 = .55125 < .599 |
| U^2*Q2*Q3^2 | 197/200 = .985 < 1 |
| N^(7/32)*U*Q1*Q2^5*Q3^2 | 757/400 = 1.8925 < 2 |
| U^(23/16)*Q1*Q2^(73/16)*Q3^(39/16) | 2267/1280 = 1.77109375 < 2 |
| Q1^3*(Q2*Q3)^4 | 1739/800 = 2.17375 > 2*(15/16) |
| Q1*Q2^2*Q3^2 | 857/800 = 1.07125 > 15/16 |

The first gate Q1 < U*x^(-sigma) also has a fixed positive margin.
This is not an occupied historical atom or a counterexample to the original
physical-policy theorem. It shows only that a caller cannot discard the
extra shared-boundary hypothesis by unpacking MediumAdmissible, even when
U <= x^(1/16). U06 proves that extra gate on its specified actual subset;
that proof has already been consumed and is not repeated.

## 6. hI / hkernel / full-phase: what the inspected results do

The local original APIs in
`ImbalancedChen/Part3ZActualPrimaryDyadicAssembly.lean` are exact identities:

- `actual_beta_energy_assembly` partitions the actual nonzero source energy;
  lambda and omega remain parameters.
- `common_phase_source_assembly` and `common_phase_beta_assembly` preserve
  a supplied `I : CommonCompletedVariable`, a supplied kernel K and the
  same phase in every finite block. They do not construct the actual I or
  prove that K equals the actual spectral kernel.

`ImbalancedChen/Part3ZActualPrimaryShortEndpoint.lean` supplies
`short_mode_mass_eq_beta` and `short_common_phase_packet`. Under U/nu < 1,
the latter reduces the packet to the n=1 expression

```text
sum m in M, I.weight m * signedCoefficient (...) 1 * K m 1.
```

It retains the full m-side sum and the same arbitrary I/K. Reduction to
n=1, or equality of coefficient norms with dyadicBeta, gives no full-phase
bound for that remaining sum.

The recorded P3 increment at source `97d5de82f2fd4e3d72fc86347ab40f00cc939a33`
explicitly keeps actual hI, pointwise hkernel, one consistent row/height
family, and the full-phase estimate on the same pure m-side array as
premises. Its named new-owner records have `source_body_read=false`;
this review does not fabricate or claim to verify their exact signatures.
The record is
`docs/p1/20261125/p15-remaining-original-distribution/P3_REGISTERED_HEAD_DELTA_20261126.json`.

The later local AFTER_N record, observing branch head
`2110a6170401bfc0dcaee46f689ee5f705507683`, adds only the original fixed-height
circle-Fourier / literal Fricke phase acceptance. Integrability remains;
DI/Whittaker coefficient identification, ABL dilation, actual medium-source
interfaces and continuous normalization remain outside that acceptance.
No new remote query was made in this review.

## 7. Minimal continuation boundary

For an actual original history family, provide its same-source
OriginalData/FixedBlock/factor-window data, a single genuine completed I,
the pointwise arithmetic-to-spectral kernel identification, and the required
full-phase bound for the same m-side array with uniform family constants.
These are genuine supplier obligations; they cannot be replaced by finite
reindexing, coefficient-norm identities, a fresh Family structure assuming
the target, or a claimed zero Fourier tail.

Once the coefficient dictionary exists, reuse the already proved U06
short-head low-first triple payment on precisely that subcomponent, retaining
the other component explicitly. The present reviewed sources do not yet
instantiate that dictionary for the literal historical channel, and do not
pay the full complement. Thus there is no new theorem to add without either
repeating existing work or introducing a prohibited missing-input premise.

Independent bounded read-only check by `/root/p15_manuscript_audit` reached
the same conclusion for the local common-phase, short endpoint and recorded
P3 increment interfaces. This is source review only, not compiler acceptance.
The prior exact-medium residual and actual-count u*singularNormalization
claims remain unchanged; no arbitrary-log physical-count upgrade is made.
