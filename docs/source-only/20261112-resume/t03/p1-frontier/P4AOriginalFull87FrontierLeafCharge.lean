import ImbalancedChen.P4AOriginalFull87RawFrontierTerminalLevel
import ImbalancedChen.P4AOriginalFull87PostEightAttachedLevel

/-! Zero the original absolute high-modulus charge before summing over leaves.
The beta used below is the sign of the leaf on its own side. -/
namespace ImbalancedChen.P4AOriginalFull87FrontierLeafCharge
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalCompleteSixthChronology (data)
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier)
open P4AOriginalFull87UnmatchedPhysicalLeaves (rawRetainedLeaves licensedRetainedLeaves)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (leafHighQCharge)
open P4AOriginalFull87LicensedOutsideThreeInvoices (licensedFrontier)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)

private theorem charge_zero_on_live (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hlive : ∀ a : ℕ, (if leaf.positive then actualSmallRosserPlus N cap w L a
      else actualSmallRosserMinus N cap w L a) ≠ 0 → a * leaf.selected.prod ≤ X) :
    leafHighQCharge N cap w L X F leaf = 0 := by
  unfold leafHighQCharge
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro a _
  by_cases hb : (if leaf.positive then actualSmallRosserPlus N cap w L a
      else actualSmallRosserMinus N cap w L a) = 0
  · simp [hb]
  · simp only [if_neg (Nat.not_lt_of_ge (hlive a hb)),mul_zero]

/-- Stronger exponent on the raw side, kept visible before using the integer
strict cut. It requires no membership condition on the displayed beta support. -/
theorem raw_live_full_modulus_lt (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (w z epsilon : ℝ) (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (u : FirstExitDepthState ℕ)
    (hu : u ∈ actualRawFrontier e q om N cap w z (fun _ => (1 : ℝ)))
    (leaf : FirstExitLeaf ℕ) (hl : leaf ∈ rawRetainedLeaves e q om N u) (a : ℕ)
    (hb : (if leaf.positive then actualSmallRosserPlus N cap w ((N : ℝ)^epsilon) a
      else actualSmallRosserMinus N cap w ((N : ℝ)^epsilon) a) ≠ 0) :
    ((a * leaf.selected.prod : ℕ) : ℝ) < (N : ℝ)^(epsilon+299/500 : ℝ) := by
  have hsmall : (a : ℝ) < (N : ℝ)^epsilon := by
    cases hp : leaf.positive with
    | false =>
        apply (actualSmallRosserMinus_active (N := N) (cap := cap) (w := w)
          (L := (N : ℝ)^epsilon) (d := a) (by simpa [hp] using hb)).2.1
    | true =>
        apply (actualSmallRosserPlus_active (N := N) (cap := cap) (w := w)
          (L := (N : ℝ)^epsilon) (d := a) (by simpa [hp] using hb)).2.1
  have hrough := P4AOriginalFull87RawFrontierTerminalLevel.raw_frontier_leaf_product_lt
    e q om N cap w z he hN u hu leaf hl
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN
  push_cast
  rw [Real.rpow_add hNpos]
  exact (mul_le_mul_of_nonneg_left hrough.le (Nat.cast_nonneg a)).trans_lt
    (mul_lt_mul_of_pos_right hsmall (Real.rpow_pos_of_pos hNpos _))

theorem raw_charge_zero (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (w z epsilon : ℝ) (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (heps : epsilon ≤ 1/500) (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ) (u : FirstExitDepthState ℕ)
    (hu : u ∈ actualRawFrontier e q om N cap w z (fun _ => (1 : ℝ)))
    (leaf : FirstExitLeaf ℕ) (hl : leaf ∈ rawRetainedLeaves e q om N u) :
    leafHighQCharge N cap w ((N : ℝ)^epsilon) X F leaf = 0 := by
  apply charge_zero_on_live
  intro a hb
  have hm := raw_live_full_modulus_lt e q om N cap w z epsilon he hN u hu leaf hl a hb
  have hscale : (N : ℝ)^(epsilon+299/500 : ℝ) ≤ (N : ℝ)^(3/5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)
  exact_mod_cast (hm.le.trans (hscale.trans hX))

/-- The published licensed post-eight theorem bounds each actually nonzero
beta before its absolute value is charged. -/
theorem licensed_charge_zero (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z epsilon : ℝ) (hsupply : FilteredSourceSupply s r n e q om)
    (he : 0 ≤ ((data e q om).e : ℝ)) (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ)^(53/13824 : ℝ)) (hz : (N : ℝ)^mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (he0 : 0 < epsilon) (heps : epsilon ≤ 1/500)
    (X : ℕ) (hX : (N : ℝ)^(3/5 : ℝ) ≤ (X : ℝ)) (F : ℕ → ℝ)
    (u : FirstExitDepthState ℕ) (hu : u ∈ licensedFrontier (width r) n e q om N cap w z)
    (leaf : FirstExitLeaf ℕ) (hl : leaf ∈ licensedRetainedLeaves (width r) n e q om N u) :
    leafHighQCharge N cap w ((N : ℝ)^epsilon) X F leaf = 0 := by
  apply charge_zero_on_live
  intro a hb
  have hmod := P4AOriginalFull87PostEightAttachedLevel.actual_post8_live_full_modulus_lt_three_fifths
    s r n e q om N cap w z (fun _ => (1 : ℝ)) hsupply he hN hw hz hzcap
    epsilon he0 heps u hu leaf hl a hb
  exact_mod_cast (hmod.le.trans hX)

end
end ImbalancedChen.P4AOriginalFull87FrontierLeafCharge
