import ImbalancedChen.P4BSmoothPhysicalMassReserve
import ImbalancedChen.P4BSmoothPrimeVariableProfile
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget

/-!
# A concrete fixed-width actual smooth family for the P3 interface

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The width is selected once from the actual arithmetic mass reserve, below
both the caller's cap and the actual exponent gap. The same width is then
used in the prime-variable profile, common support, prime lower bound and
every directional derivative budget. Constants are chosen after a finite
derivative order and before the varying target and prime variables.

These are genuine prerequisites for a concrete family. The record contains
no PP, spectral, density, upper-count or whole-policy licensing field.
Directional profile bounds are not asserted to be mixed Euler bounds.
The missing P3 estimate must refer to this very selected physical width
and the caller's literal attached coefficient; none is manufactured here.
-/

namespace ImbalancedChen.P4BActualSmoothFamilyWitness

noncomputable section
open scoped BigOperators
open Part3
open P4B P4BLabelledLogGeometry P4BOuterRampRoughness
open P4BSmoothProfileCommonCompactSupport

/-- A single actual smooth family, with its arithmetic and continuous
parameters synchronized before P3 chooses any discrepancy constant.
The normalized-log cube is independent of N. -/
structure ActualSmoothFamilyWitness
    (b kappa theta eta widthMax : ℝ) where
  width : ℝ
  width_pos : 0 < width
  width_le : width ≤ widthMax
  margin_gap : 2 * width ≤ baseline b kappa - theta
  threshold : ℕ
  threshold_two : 2 ≤ threshold
  mass : ∀ N : ℕ, threshold ≤ N → Even N →
    (∑ t ∈ labelledPrimeTuples 2 N,
      smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width t) ≤
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
        eta * ((N : ℝ) / Real.log (N : ℝ))
  common_support : ∀ N : ℕ, 2 ≤ N →
    tsupport (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width) ⊆
      commonCube theta width
  compact_support : ∀ N : ℕ, 2 ≤ N →
    HasCompactSupport
      (smoothPhysicalProfile b N (manuscriptHalfProductCutoff kappa N) width)
  smooth_prime_variables : ∀ N : ℕ, ∀ n : ℕ∞,
    ContDiffOn ℝ n
      (smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N) width)
      positivePrimeOrthant
  prime_lower_support : ∀ N : ℕ, 2 ≤ N → ∀ p : Fin 2 → ℝ,
    p ∈ positivePrimeOrthant →
    smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N) width p ≠ 0 →
    ∀ i : Fin 2, (N : ℝ) ^ theta < p i
  directional_budget : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ x h : Fin 2 → ℝ,
      |iteratedDeriv k (smoothPhysicalProfileLine b N T width x h) 0| ≤
        (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k * ‖h‖ ^ k

/-- The actual four-wall mass theorem produces the synchronized family.
No estimate at a point or at a sampled prime tuple substitutes for the
displayed all-space compact support and positive-variable regularity. -/
theorem nonempty_actualSmoothFamilyWitness
    {b kappa theta eta widthMax : ℝ}
    (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (htheta : 0 < theta) (heta : 0 < eta) (hwidthMax : 0 < widthMax)
    (hgap : theta < baseline b kappa) :
    Nonempty (ActualSmoothFamilyWitness b kappa theta eta widthMax) := by
  have hb : 0 < b := by linarith only [hbLower]
  let effectiveMax : ℝ := min widthMax ((baseline b kappa - theta) / 2)
  have heffectiveMax : 0 < effectiveMax := by
    dsimp only [effectiveMax]
    apply lt_min hwidthMax
    linarith only [hgap]
  obtain ⟨width, hwidth, hwidthEffective, N0, hN0, hmass⟩ :=
    exists_smooth_physical_ramp_mass_reserve
      hbLower hbUpper hkappa hkappaOne eta effectiveMax heta heffectiveMax
  have hwidthMaxLe : width ≤ widthMax :=
    hwidthEffective.trans (min_le_left _ _)
  have hwidthGap : 2 * width ≤ baseline b kappa - theta := by
    have hhalf : width ≤ (baseline b kappa - theta) / 2 :=
      hwidthEffective.trans (min_le_right _ _)
    linarith only [hhalf]
  refine ⟨{
    width := width
    width_pos := hwidth
    width_le := hwidthMaxLe
    margin_gap := hwidthGap
    threshold := N0
    threshold_two := hN0
    mass := hmass
    common_support := ?_
    compact_support := ?_
    smooth_prime_variables := ?_
    prime_lower_support := ?_
    directional_budget := ?_ }⟩
  · intro N hN
    exact tsupport_smoothPhysicalProfile_subset_commonCube
      hb htheta hN hwidth hwidthGap
  · intro N hN
    exact hasCompactSupport_smoothPhysicalProfile hb htheta hN hwidth hwidthGap
  · intro N n
    exact contDiffOn_smoothPrimeVariableProfile b N
      (manuscriptHalfProductCutoff kappa N) width
  · intro N hN p hp hn
    exact smoothPrimeVariableProfile_nonzero_above_rpow
      hb htheta hN hwidth hwidthGap hp hn
  · intro k
    obtain ⟨C, hC, hbudget⟩ :=
      exists_smoothPhysicalProfile_directional_derivative_budget k b
    exact ⟨C, hC, fun N hN T x h => hbudget width hwidth N hN T x h⟩

/-- The discrete weight used by PP is literally evaluation of the
positive-real-variable profile of the selected family. -/
theorem selected_weight_eq_prime_profile
    {b kappa theta eta widthMax : ℝ}
    (F : ActualSmoothFamilyWitness b kappa theta eta widthMax)
    (N : ℕ) (t : Fin 2 → Fin (N + 1)) :
    smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) F.width t =
      smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff kappa N)
        F.width (primeTuplePoint N t) := by
  rfl

end
end ImbalancedChen.P4BActualSmoothFamilyWitness
