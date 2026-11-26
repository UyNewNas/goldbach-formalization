# R17 below-mesh supplier: source review checkpoint

2026-11-26; frozen when the parent reprioritized the actual round6
Full87Ownership failure. No compilation or formal acceptance is claimed.

## Exact reusable suppliers

The November 23 selected API is under
`docs/source-only/20261123-resume/ten-task-continuation/selected-api/ImbalancedChen/`:

1. `P4AOrderedThirdSameCoefficient.joined_below` has a complete proof body.
   With positive `meshMax`, it constructs beta, one aligned mesh k below that
   bound, and one N0. It proves the quantitative compilerExpense payment,
   reciprocal-totient density comparison, strict support below `N^(599/1000)`
   and a RealB majorant retaining the actual distribution error. There is no
   hPP premise, and no claimed smallness of that distribution error.
2. `P4AOrderedThirdCommonSchedule.common_schedule_below` has a complete proof
   body. It joins the preceding result to the original four-positive root
   bound, using the same beta/k and the maximum of the two N thresholds.
3. `P4AOriginalR17PaidIntegral.original_signed_density_and_count_below` has a
   complete proof body. It additionally supplies the ordinary full87 integral
   gain and common history, retaining the same Q/rho and one compiler expense.
   Both count inequalities still include `realPhysicalDistributionError`,
   `ceil z` and `T+1`.

The payment consumed by `joined_below` is
`P4AOrderedThirdRectanglePayment.paid`, in
`docs/source-only/20261110-yellow-closure-10t/t04_compiler_physical_payment/successor_transport/`.
It derives compiler/density reserve from the existing rectangle wall rate.
This is a genuine quantitative estimate for that reserve, not a premise
renamed as a theorem. It is also a different estimate from signed PP error.

## Existing PP consumers and their explicit remaining premises

- Production `ImbalancedChen/P4BDirectPPUpperAssembly.lean`,
  `eventually_realPhysicalDistributionError_le_of_uniformPP`, accepts arbitrary
  functions Q and rho and an explicit rank-two, Unit-indexed
  `Part3.UniformPrimeProductTarget` for the exact labelled ordered band.
  It uses that input at A=3 to derive arbitrary small singular-normalized
  error. Therefore a new error-normalization wrapper is unnecessary.
- `docs/source-only/20261123-yellow-node-owners/y07_uniform_upper/ImbalancedChen/P4BOriginalFineAttachedRetained.lean`,
  `uniformPP_of_remainingRows`, has a proof body but requires
  `hRows : forall p, exists D >= 0, eventually N, Even N ->
  norm(remainingRows ...) <= D*N/(log N)^p`.
  Its `exists_attached_recovery` already pays the Fourier tail, trim, and
  rough-prime removal in the difference between PP error and those retained
  rows. It does not pay the retained arithmetic row sum itself.
- The same package's `P4BOriginalFineAttachedUpper.upper_of_attached_PP`
  retains an explicit all-width `hPP` assumption.
- `y06_same_rho_pp/ImbalancedChen/P4BOriginalFineRetainedCalibration.lean`
  proves small *differences* between retained sums (`eventually_proper_removed`,
  `retained_to_reported`), not the required bound on either sum.
- These FineAttached statements concern their exact attached coefficient;
  they must not be silently substituted for the R17 rectangular coefficient.
  The generic DirectPPUpperAssembly adapter can already take R17 Q/rho once
  the actual UniformPrimeProductTarget instance is supplied.

Thus the below-mesh supplier is already proved in source; it is not an
unconnected proof of signed PP smallness. A current exact R17 PP instance
would close the remaining input to the generic error adapter. No such closed
instance was found in the examined source selection.

## Manuscript classification

Frozen 1106 local source was read at
`/workspace/scratch/e5f883a2215a/reference/paper/release-20261106/en/`.

- `argument.tex`, `eq:current-PP`, explicitly states the same signed
  coefficient in the congruence and coprime-mean terms and the
  `O_A(N/(log N)^A)` conclusion for admitted finite families.
- `coefficient-appendix.tex`, `coef:prime-product-insertion`, gives a separate
  proof: complete-product trim, smooth dyadic/HB decomposition, same tensor
  coefficient, Fourier norm and tail payment, rough SW, medium theorem,
  one/two-long branches and low-rank BV, then one eventual family threshold.
- `argument.tex`, `prop:current-medium`, and `analytic-appendix.tex`,
  `app:medium`, contain the nontrivial medium/spectral estimate that this
  insertion invokes.
- `sieve-appendix.tex`, near `sv:upper-projection`, chooses the compiler
  parameters before N and then invokes current-PP for the **same coefficient**.

Consequently this is a separate substantive analytic formalization obligation,
not a missing algebraic step in the G16 Jensen calculation. The manuscript
does contain an argument for it. This review does not identify a concrete
contradiction or establish a substantive gap in that mathematical argument;
it cannot replace the missing formal actual-family input by its definition.

## Search scope and limits

Searched production and stored source-only Lean files for
`UniformPrimeProductTarget`, `realPhysicalDistributionError`, remainingRows,
the below-mesh names, and candidate PP suppliers. Inspected Git histories of
R17, SameCoefficient, PPSchedule, FineAttached and UpperModesRoughPrimePaid.
The R17 selected API was introduced at `7f5330ca`; the FineAttached consumer
appears at `410d13f5`; older transport/payment revisions include `62af0da0`.
An all-ref Git content-history search for `UniformPrimeProductTarget` was
started but interrupted (exit130) when the actual round6 failure took priority.
It had found the same FineAttached and older source entries; it was not an
exhaustive all-history negative search. No claim of absence from all Git
objects or all external environments is made.
