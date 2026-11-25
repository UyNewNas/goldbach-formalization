# Actual rounded beta reserve — source-only checkpoint

**SOURCE ONLY / UNCOMPILED / INDEPENDENT REVIEW PENDING / NO FORMAL CREDIT.**

This checkpoint was saved before switching back to the higher-priority P1
acceptance-archive review. The three theorem bodies have been written. No Lean
process, kernel replay, remote task, canonical installation, manifest change,
staging or commit was performed for this packet. Syntax/elaboration and the
complete imported declaration inventory have not been verified.

## Three bounded statements

`ImbalancedChen/P3OriginalU5RoundedBetaReserve.lean` contains three theorems:

1. `exists_absolute_density_le_powerParameters` compares the absolute value of
   the actual rounded coefficient with the already-defined complete residual
   mass, using `coefficient_abs_le_one`. It directly invokes the old
   `P2ActualResidualUniverseMass.exists_mass_logRatio_bound`; it does not
   reprove the Euler expansion or Mertens theorem.
2. `exists_beta_error_le_normalized_reserve` uses the actual small-Rosser
   density sandwich and the generic **lower** sign-sensitive attachment error
   theorem. The existing normalized scalar absorption and small Euler
   normalization pay the resulting absolute-mass bound. It asserts
   `0 <= V * roundedRoughDensity - roundedPhysicalDensity <= eta * S(N)/log D`.
3. `exists_beta_error_le_target_reserve` substitutes `D = N^nu`, including the
   exact logarithmic factor `nu`. For original U5, `nu = 34/125` and
   `r = 417/1360` preserve its cutoff `N^(417/5000)`.

The last two statements choose epsilon, then a threshold, before the target,
cap, retention policy and fine mesh. Epsilon can lie below any prescribed
positive `epsilonMax`. The real-D statement requires the cap to cover the
small cutoff; the target statement requires it to cover the rough cutoff.
Both use the same actual rounded coefficient and compiler rho throughout.
They do not represent that output as a new raw policy.

Only the beta attachment error is paid. The raw-to-rounded `roundingLoss`,
actual U5 mixed-fibre wall coverage, full policy density evaluation, marked
mean recentering, whole-word tensor, admission and PP remain outside the
conclusions. The code adds no final density or PP hypothesis. The scalar
Rosser error has a positive exponential floor at fixed epsilon; the proof
therefore chooses epsilon before taking the large-target threshold.

## Fixed sources and corrected deduplication

All old Lean inputs inspected for this checkpoint were read from fixed Git
objects, never selected from a moving donor HEAD:

- donor `d6a9d76c56621992a8445c9628d4a2058db72eb6`;
- p15 `c6b89774822580c731a236ac66dcd7466ac8a0e6`.

`SOURCE_INDEX.json` records the exact source bytes, SHA-256 and Git blob.
In particular, the compiler and rounding inputs are the p15 source versions
identified by the parent as having prior compile/replay repair evidence.
This checkpoint binds those source bytes; it does not itself audit or grant
that prior acceptance credit. The quoted identifier `«universe»` matches
those repaired source interfaces.

The broader p15/transfer-trace search found additional existing interfaces
which were outside the earlier main/donor-canonical search. They must be
reused rather than rewritten:

- `P2RoundedCausalFibreLossAndLevel.roundingLoss_le_two_mixedMass` already
  proves the finite rounding-loss comparison. Its same-fibre raw witness,
  rank-times-mesh bound and uniform physical-level mesh are also existing.
- `P2ActualResidualUniverseMass` already defines the entire residual mass,
  proves its exact Euler product, its log-ratio bound and its eventual bound
  uniform over all enumeration caps. The new first theorem only adds the
  rounded coefficient's finite one-bound comparison and power substitution.
- `P2CanonicalWallFullResidualPayment` already proves canonical prefix/tail
  splitting, totient-weight reindexing and full-residual wall payment. Thus
  the remaining rounding-loss obligation is narrower than the earlier
  canonical-only search indicated: actual U5 mixed complete-history fibres
  must be covered by a fixed finite family of genuine proper wall sets.
- `P2RoundedU6NativeJointLedger.rounded_quotient_sum_le_sifted` already gives
  the arbitrary-multiplier rounded quotient minorant. The earlier new U5
  count caller should call this existing lemma on subsequent integration.
  Its old frozen source was not changed by this checkpoint.

`P5LowerPolicyDensityStability` bounds differences of two raw policies by a
literal first-disagreement budget. It cannot be applied directly to a rounded
output which need not be a raw-policy coefficient, and does not itself pay
the actual U5 mixed-fibre mass.

## Manuscript alignment and remaining loss chain

The fixed 1106 sieve appendix uses the lower presieve projection plus absolute
beta and box errors in `sv:physical-lower`. Its `sv:finite-realization` proof
fixes a finite coarse policy, chooses small parameters and mesh before N, and
records the beta/fine-box error
`O(exp(-c/eta) * eta0^(-2) + C_policy * tau * eta0^(-5))`.
The coefficient appendix's finite-approximation and parameter-order passages
keep inherited identities, require proper affine walls and preserve the same
coefficient between count and exact mean.

The actual existing raw-density reserve is

`rawFullDensity - V * roundingLoss - V * E * absoluteRoundedMass
  <= roundedPhysicalDensity`.

This checkpoint addresses only the second error through existing analytic
suppliers. For the first error, use the existing `roundingLoss <= 2*mixedMass`
and full-residual wall payment. The still-required source-specific statement
must cover every mixed canonical history of the **chosen actual U5 policy**,
including all ancestor tests and original masks. Neither a generic caller
assumption `mixedMass <= eta` nor a replacement by an unimplemented coarse
policy supplies that statement. Proper-wall small mass is already available
in `AffinePrimeWallReserve`; moving affine slabs also have actual arithmetic
envelopes. These existing results should not be reproved.

This source packet has no integration preflight or cache-reuse licence.
Future integration must choose a compatible exact import closure and complete
strict owned compilation, bundled kernel replay, full declaration/type
inventory and transitive-axiom checking. The checkpoint is paused pending
independent review and the higher-priority P1 archive audit.
