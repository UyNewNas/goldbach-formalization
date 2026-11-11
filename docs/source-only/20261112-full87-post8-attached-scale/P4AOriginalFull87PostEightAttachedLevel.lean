import ImbalancedChen.P4AOriginalFull87AllEighthFrontierTerminal
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import ImbalancedChen.ActualSmallRosser
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Exact small-beta attachment to the ORIGINAL post-eight retained continuation.
For the frozen small sieve scale L = N^epsilon, with a FIXED epsilon
at most 1/500, the actual rank-eight rough terminal bound 299/500
pays the complete a*b exponent 3/5. A nonzero sign-selected small
Rosser beta is necessary: mere displayed membership in the small
support does NOT imply a < L.

The finite high-q test vanishes termwise, then in the literal signed
continuation with the same parent, mass, sign and leaf multiplicities.
This is NOT the full physical sixth/eighth coefficient bound: original
stopped leaves before depth eight and the sixth predecessor still
need their own accounting. The choice of small epsilon compatible with
the complete original reserve is also not supplied here.
No external PP theorem is called.
-/

namespace ImbalancedChen.P4AOriginalFull87PostEightAttachedLevel
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P1Pair12RetainedSignedSource (signedTest attachedLeafTest)

/-- For one literal post-eight retained leaf and one genuinely nonzero
ORIGINAL sign-selected small beta, the complete physical modulus has
exponent 3/5. The small level is the actual N^epsilon specialization,
not an independently assumed L * N^(.598) budget.
All parameters are fixed before the target N and source occurrence. -/
theorem actual_post8_live_full_modulus_lt_three_fifths
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (hsupply : FilteredSourceSupply s r n e q om)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ) ^ mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight state.selectedPrefix state.positive state.mass state.remaining)
    (a : ℕ)
    (hbeta : (if leaf.positive then
        actualSmallRosserPlus N cap w ((N : ℝ) ^ epsilon) a
      else actualSmallRosserMinus N cap w ((N : ℝ) ^ epsilon) a) ≠ 0) :
    ((a * leaf.selected.prod : ℕ) : ℝ) <
      (N : ℝ) ^ (3 / 5 : ℝ) := by
  have hsmall : (a : ℝ) < (N : ℝ) ^ epsilon := by
    cases hp : leaf.positive with
    | false =>
        have hm : actualSmallRosserMinus N cap w ((N : ℝ) ^ epsilon) a ≠ 0 := by
          simpa [hp] using hbeta
        exact (actualSmallRosserMinus_active hm).2.1
    | true =>
        have hp' : actualSmallRosserPlus N cap w ((N : ℝ) ^ epsilon) a ≠ 0 := by
          simpa [hp] using hbeta
        exact (actualSmallRosserPlus_active hp').2.1
  have hrough :=
    P4AOriginalFull87AllEighthFrontierTerminal.
      actual_all_eighth_frontier_terminal_product_lt_fixed_power
        s r n e q om N cap w z weight hsupply he hN
        hw hz hzcap state hstate leaf hleaf
  have hNpos : (0 : ℝ) < (N : ℝ) :=
    lt_trans (by norm_num) hN
  have hexp : epsilon + (299 / 500 : ℝ) ≤ (3 / 5 : ℝ) := by
    linarith
  calc
    ((a * leaf.selected.prod : ℕ) : ℝ) =
        (a : ℝ) * (leaf.selected.prod : ℝ) := by push_cast; ring
    _ ≤ (a : ℝ) * (N : ℝ) ^ (299 / 500 : ℝ) :=
      mul_le_mul_of_nonneg_left hrough.le (Nat.cast_nonneg a)
    _ < (N : ℝ) ^ epsilon * (N : ℝ) ^ (299 / 500 : ℝ) :=
      mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hNpos _)
    _ = (N : ℝ) ^ (epsilon + (299 / 500 : ℝ)) := by
      rw [Real.rpow_add hNpos]
    _ ≤ (N : ℝ) ^ (3 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN.le hexp

/-- The ORIGINAL high-q test of one post-eight leaf is identically zero
above the complete-modulus threshold. All small carrier elements are
enumerated, but zero beta coefficients contribute literally zero; there
is no extra mask or per-occurrence absolute payment. -/
theorem actual_post8_attached_highq_zero
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (hsupply : FilteredSourceSupply s r n e q om)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ) ^ mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight state.selectedPrefix state.positive state.mass state.remaining) :
    attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
      (highQTest X F) leaf.positive leaf.selected = 0 := by
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hbeta :
      (if leaf.positive then
        actualSmallRosserPlus N cap w ((N : ℝ) ^ epsilon) a
       else actualSmallRosserMinus N cap w ((N : ℝ) ^ epsilon) a) = 0
  · simp [hbeta]
  · have hmod := actual_post8_live_full_modulus_lt_three_fifths
      s r n e q om N cap w z weight hsupply he hN hw hz hzcap
      epsilon hepsilon heps state hstate leaf hleaf a hbeta
    have hsmall : a * leaf.selected.prod ≤ X := by
      have hle : ((a * leaf.selected.prod : ℕ) : ℝ) ≤ (X : ℝ) :=
        (le_of_lt hmod).trans hX
      exact_mod_cast hle
    have hnot : ¬X < a * leaf.selected.prod := Nat.not_lt.mpr hsmall
    simp [highQTest, hnot]

private theorem sum_map_zero_of_each_zero {α : Type*}
    (xs : List α) (f : α → ℝ)
    (hzero : ∀ x ∈ xs, f x = 0) :
    (xs.map f).sum = 0 := by
  induction xs with
  | nil => simp
  | cons x tail ih =>
      have hx : f x = 0 := hzero x (by simp)
      have ht : ∀ y ∈ tail, f y = 0 := by
        intro y hy
        exact hzero y (by simp [hy])
      simp [hx, ih ht]

/-- The actual signed post-eight continuation has zero high-q mass at
this threshold. Uses the literal original first-exit terminal list and
its original occurrence sum; it is not the unprocessed stoppedTest. -/
theorem actual_post8_signed_highq_zero
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (hsupply : FilteredSourceSupply s r n e q om)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ) ^ mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    signedTest
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon)
        (highQTest X F))
      state.selectedPrefix state.positive state.mass state.remaining = 0 := by
  rw [P1Pair12RetainedSignedSource.signedTest_eq_leaves]
  apply sum_map_zero_of_each_zero
  intro leaf hleaf
  have hterm := actual_post8_attached_highq_zero
    s r n e q om N cap w z weight hsupply he hN hw hz hzcap
    epsilon hepsilon heps X hX F state hstate leaf hleaf
  rw [hterm]
  ring

end
end ImbalancedChen.P4AOriginalFull87PostEightAttachedLevel
