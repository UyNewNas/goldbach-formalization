# P exceptional_j_eta: additional-cost audit and original-parameter repairs

The full P3.5 uniform spectral node remains **OPEN / HOLD**. O's actual
fourth-weight caller, smaller eta, all-scale logarithm and retained-phase
budget are reused unchanged. They are not reproved here. This audit does
**not** certify that every remaining original Fourier/truncation cost has
already been covered by one pre-target threshold.

One new uncompiled source candidate is supplied:
`Part3OriginalAdditionalSpectralCosts.lean`, intended module
`ImbalancedChen.Part3OriginalAdditionalSpectralCosts`. It fills concrete
original-parameter conversions: the actual ceil cutoff, the exceptional
degree-two cutoff specialization, the additional unweighted Fourier mass,
the common-mask logarithm at original scales, and ONE preliminary D. It
does not assume an arithmetic-to-spectral identity or an energy bound.

`compiled=false`, `kernel_verified=false`, `formal_credit=0`. Finite guards
remain **UNEVALUATED**. No Lean/lake/compiler, CI, proof evaluator, numerical
replay/search, Git command or child agent was run. Only this assigned P
directory was written. All inherited HOLD states remain in force.

## Read sources and exact reuse

BRIEF, this task's PRIOR_TASK, all three O exceptional_j_eta files, the
complete O Lean source and REPORT, M all-scale Lean/REPORT, M original-scale
retained-phase Lean/REPORT, the original manuscript and original completion
note were read. `REGISTRY.json` gives raw SHA256, direct imports, declaration
locations and intended installation paths for every reused source below.
Hashes identify selected source bytes; they are not proof receipts.

* O `docs/source-only/20261102-resume-30o/exceptional_j_eta/Part3ActualExceptionalJSelectableEta.lean`,
  SHA256 `e30edb4d6e3ed9134a9f35a417cc2709b027e1ca99b7ca3ef54698bcc494e1f6`:
  `exists_physical_J_caller_constant` (286),
  `exists_selected_physical_J_caller` (382),
  `exists_selected_original_E3_threshold` (412),
  `combined_selectable_cost` (429), `original_two_saving_margins` (446).
  The real 28 eta and literal retained completedEnergy survive.
* M `docs/source-only/20261102-resume-30m/exceptional_j_large_scale/Part3ActualExceptionalJAllScaleBudget.lean`:
  `positivePhysical_all_scale_sq_le` (222),
  `exists_physical_positive_all_scale_smoothing_constant` (252).
  No Bessel or all-scale theorem is rewritten.
* M `docs/source-only/20261102-resume-30m/medium_retained_phase/Part3OriginalRetainedPhaseOriginalScale.lean`:
  `actual_E3_original_scale_epsilon` (182). Its original prefix envelope,
  actual profile, log^25 and once-only 5 kappa remain explicit.
* Production `ImbalancedChen/Part3ZRegularSpectralPolynomial.lean`:
  `regular_return_le_rpow_cutoff` (109) already proves the exact ordinary
  degree-two inflation. Production
  `ImbalancedChen/Part3ZExceptionalSpectralPolynomial.lean`:
  `exceptional_return_le_inflated_cutoff` (134) proves R^2 on its actual
  exceptional expression, with every D factor retained.
* Production `ImbalancedChen/Part3ActualWeightedSpectralBudget.lean`:
  `actual_uniform_xeta_weighted_budget` (108), at order zero, gives the
  actual unweighted coefficient mass at cost 12 eta. This is distinct from
  O/M's order-four 28 eta fee.
* Production `ImbalancedChen/Part3ActualCommonIntervalPhysicalLogBudget.lean`:
  `actual_same_mask_physical_norm_sq` (158) gives the genuine physical
  common-mask log^2 with one common frequency maximum; the empty carrier is
  already treated exactly. The period and logarithm are not assumed.
* Production `ImbalancedChen/Part3PrimaryNuUniformKappaSubpower.lean`:
  `actual_primaryKeys_uniform_kappa_subpower` (22) supplies both the raw
  primary-nu sum and the original ABL cost after 1/nu, uniformly over
  0 <= kappa <= fixed kappa0. Its constant precedes kappa, atoms, signs and
  finite source supports. The polynomial |a|^(7/32) is retained. The proof
  uses `Part3PrimaryNuEulerSubpower.finite_supported_sum_subpower` (139)
  and the genuine divisor supplier
  `Part3PolynomialResidueDivisorBound.fouvryTau_le_const_rpow` (87).
* G `docs/source-only/20261028-resume-30g/medium_s3/Part3MediumActualRestorationPayment.lean`:
  `occupied_keyD_le_trim_sq` (29) proves D <= roughY(x)^2 on the actual
  occupied `keyBank`; the new arbitrary-small-exponent conversion reuses
  this source theorem. B's exact dyadic ownership is not replaced.
* O `docs/source-only/20261102-resume-30o/medium_spectral_dictionary/Part3OriginalCommonPoissonLanes.lean`:
  `globalCutoff` (179), `commonMBlock` (114),
  `original_six_global_m_dictionary` (327). This supplies the actual common
  Poisson blocks, not a renamed earlier s-completion frequency.

## New obligations actually removed at source-candidate level

1. `exists_globalCutoff_common_scale_threshold` addresses a real missing
   conversion. The existing cutoff is ceil((C/D)*x^epsilon). Membership in
   a nonempty common block gives its natural V=2^j <= ceil(T), not V <= T.
   Here the literal original C/D is scaleS(key)=2^key.u >= 1. At cutoff
   epsilon=eta/2, T >= 1, ceil(T) <= 2T. One threshold, chosen before every
   OriginalData, x or block, supplies 2 <= x^(eta/2), hence

   `2^j <= x^eta * OriginalData.cScale / OriginalData.bScale`.

   This preserves the exact O globalCutoff definition and the exact clipped
   commonMBlock. It proves a bound for its actual natural scale and does
   not assert that a PacketData has already been constructed from it.
   The shared `commonMBlock_scale_le_twice_cutoff` proves the raw
   V<=2*x^epsilon*C/D bound. All six original smooth pieces also have
   M<=2*bScale and N>=cScale. The new
   `exists_globalCutoff_six_rho_threshold` explicitly pays the resulting
   further factor two: at the SAME eta/2 cutoff it uses the single stronger
   threshold 4<=x^(eta/2) to prove V*M/N<=x^eta for all six pieces.
   Thus the earlier threshold of two is not silently used to pay four.
   Changing a freely selectable cutoff from eta to eta/2 is allowed by the
   original source, but its omitted tail still needs the corresponding
   actual tail invocation; the identity alone does not pay that tail.

2. `exceptional_return_le_rpow_cutoff` instantiates the existing exceptional
   R^2 comparison at R=x^eta and proves the literal x^(2 eta) fee, matching
   the already existing ordinary theorem. It is algebra of the actual
   Eq24/Eq25 expressions, not a proof of Eq24.

3. `exists_unweighted_mass_and_cutoff_constant` invokes the actual
   order-zero Fourier supplier and proves

   `x^(2 eta) * actualW(rho,sign,0) <= K*x^(14 eta)`.

   K precedes x, eta, rho and sign. Consequently q=2 in O pays only the
   cutoff. If a valid later mode estimate leaves one unweighted Fourier
   mass to be summed, that additional operation has a proved 12 eta price;
   q=14 is a conservative allocation for these TWO specific fees. This is
   not a declaration that all remaining operations cost 14 eta, nor a
   bound for the retained completedEnergy.

4. `literal_cutoff_V_le_sq` uses the printed original C=NRS and D=NR,
   S<=x, eta<=1 to derive V<=x^2. `exists_original_mask_log_threshold`
   actually invokes the existing physical-mask completion and proves,
   uniformly before packets and masks,

   `|completedPacketSum(restrictM P a b,k)|^2`
   ` <= K*x^delta*maxShiftedPacketNormSq(P,k,physicalPeriod P)`.

   Its only geometric premise is P.V<=x^2. The proof derives
   log(2+P.V)<= (log 3+2)*(1+log x), then uses O's already proved logarithm
   payment. No interval-completion estimate is assumed. In the original
   range sigma<1/100, O's selected eta is below one. Supplying the actual
   packet geometry for every original source branch remains t18's boundary.

5. `exists_occupied_keyD_subpower_threshold` proves keyD<=x^delta on the
   actual occupied original key bank at roughY(x)=x^(1/loglog x), using the
   original retained smooth-factor trim. It chooses loglog x >= 2/delta
   before every atom, receiver and occupied key. This pays ONE extra D,
   as stipulated by completion-note lines 417-424. It does not create a
   second D or sum D arbitrary-logarithmic remainders.

`scaleS_one_le` is the source-geometric helper for item 1. The literal
roughY scalar definition is read at
`.lake/proof-continuation/source-reviews/drafts/20261028-Medium-Saving-Sol6/frozen/e790c1946a2380ec6a0eedf27b3e4efae831c1c26adf4415671fc309d0f4bf01/Part3OriginalS2PaperBlockEmbedding.lean:26`,
SHA256 `e790c1946a2380ec6a0eedf27b3e4efae831c1c26adf4415671fc309d0f4bf01`.
Only that scalar formula is reused; no historical S2 filter interpretation
is substituted for G's actual occupied-key smooth trim. No O proof is
copied or modified. The new file is an extension, not a repaired copy whose
old source must be removed.

## What a common threshold does and does not currently cover

For fixed finite orders and positive epsilon,sigma, O's hierarchy may be
reused at q=14: a=min(epsilon,sigma/10), eta=a/172 and delta0=a/4. The
already-proved O combined J/phase price is at most 3a/4. Taking the new
mask allowance, actual primary-nu allowance and ONE D allowance each to be
a/16 spends a further 3a/16, leaving a/16. This is an allocation of the
specific supplied fees; it is not a proof of the full original return.

All thresholds used by these suppliers have the right order of quantifiers:
after the fixed orders/parameters and before physical target, atom,
divisor, source support, mask, sign, common block or packet. The maximum of
O's J-log and E3 thresholds, the six-piece ceil/rho threshold, the mask threshold and the
occupied-D threshold is therefore one common local threshold. Primary-nu
has a uniform constant for every admissible scale >=1 and needs no extra
scale-dependent threshold. Fixed constants stay in the uniform implied
constant. The same original kappa<=sigma/100, or stronger global
kappa<=sigma/200, suffices for O's saving comparison; these extra three
fees fit within its unused sigma/10 allocation at the displayed rates.

This audit cannot honestly append the following missing operations to that
maximum and mark every original cost paid:

* The actual cross-coprime-class count at exp(O((loglog x)^4)), all
  post-polarization endpoint multiplicities, dyadic height/m-block counts,
  and all actual divisor-factor occurrences still need a complete
  source-bound catalogue and uniform instances. A generic divisor
  subpower theorem exists; merely naming a fixed q does not invoke it on
  all actual occurrences. The residual a/16 has not been claimed to pay
  an unspecified catalogue.
* Production `Part3PhysicalHardSchwartzTail.frequency_hard_window_tail`
  (20) supplies the genuine hard tail A_r*c/Z^(r-1). The precise original
  six-piece cutoff, c-support endpoints, narrowing to eta/2 and all source
  masses still need to be put into that theorem with a fixed sufficient
  derivative order. No power-small tail follows solely from the O split.
  The statement that all finite orders entering exponent fees precede eta
  must be preserved; this P file does not resolve a tail-order choice by
  silently reversing that ordering.
* The regular/exceptional A/J and Plancherel invocations, their polynomial
  input lengths and coefficient/cusp conventions have not been supplied
  by these scalar and mask conversions. Nor has the local common threshold
  been applied through every actual complete-product local-scale chart to
  a final global even-target N threshold. The manuscript's support
  x >= c*N^(1-kappa0) allows that later uniform transfer once every missing
  source-bound threshold has actually been constructed.

## Essential retained-energy object boundary

This is more than a missing name for a packet. Production
`Part3ActualCommonHeightKFactorizationFullGram.completedPacketSum` (47-50)
is the sum of a common completed m phase and signed arithmetic n
coefficients. It does not display automorphic R_j,infty(m) and R_j,1(n).
K's `Part3ActualExceptionalJPacketAdapter.withPositiveKernel` (64-68)
replaces the kernel by the positive Bessel kernel alone. Thus O/M's actual
physical J integral and its coefficient-weighted completedEnergy cannot be
identified with the automorphic Eq24 quadratic form merely by filling an
arbitrary PacketData kernel field. This audit supplies no such identity
as a hypothesis and no wrapper that assumes it.

The t18 arithmetic/Poisson/common-m construction and the genuine
Kuznetsov/ABL cusp and formal continuous association, actual spectral
spaces/gap, fixed-level A and common-interval/common-phase J norms, and the
actual arithmetic/automorphic energy estimate remain independent required
work. The new x^(14 eta) factor theorem remains useful as an actual scalar
cost supplier if that later justified route contains the corresponding
unweighted coefficient sum; it does not perform the missing route.

## Manuscript lines, classification and validation limits

Manuscript SHA256 is the pinned
`ee6aecc164cc59f2d1fed1ad9e48f18f98472ab1d77ab425d53d93bc41ce56bd`.
Relevant lines: 207-254 (retained phase, two saving exponents and normalized
spectral inputs), 343-354 (moment order, global kappa and finite chart log
payments), 318-322 (complete-product local scale). Completion-note SHA256
is `93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7`;
relevant lines 114-135, 305-319, 349-420, 421-432 and 468-481.

The ceil, exceptional specialization, true mask logarithm and arbitrary D
payment are **(2) fillable omitted deductions**, with **(1) uncompiled Lean
expression/API risk**. No substantive contradiction with the manuscript
parameter range was found. The absent exhaustive source-cost catalogue,
tail instances and automorphic object association are unresolved formal
source obligations; they are not replaced by stronger hypotheses and are
not reported as mathematical counterexamples. Broad node P3.5 stays OPEN.

Validation was static source reading, import/declaration extraction,
forbidden-token inspection and raw SHA256 only. The pinned local Mathlib
pow/asymptotics and Nat ceiling APIs were read, not executed. An independent
source reviewer identified two missing namespace opens for completedPacketSum
and restrictM; both were added explicitly in P. No claim of elaboration,
kernel verification, recursive dependency closure or inherited PASS is made.
The t18 owner is reusing this P file's shared raw-cutoff and six-rho
declarations; its actual level/n-row and discrete-c Poisson construction
is not duplicated here.
