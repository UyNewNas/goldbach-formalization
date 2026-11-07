import ImbalancedChen.P5All16ActualInnerWallReconstruction
import ImbalancedChen.P5OriginalJointPresievedArithmeticSupport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact absolute-mass accounting for ALL original marked prefixes and ALL
small beta factors together, via the proved unique full-q pushforward.
This closes no marked sum by a fixed-prefix/e estimate.  The wall mask
identity is DERIVED from independently defined wall fibre sums and the
actual joint coefficient, not made true by defining both sides alike.

The final bound is the genuine modulus-domain bound O(N^(153/256)), not a
fixed/polylog total tensor-scalar budget.  The distinction is essential:
normalizing the marked raw convolution and absorbing small beta in gamma3
must still be linked to the actual finite geometric atom dictionary before
a fixed restoring-scalar mass can be claimed.
-/

namespace ImbalancedChen.P5Z.All16CompleteMarkedBetaMass
noncomputable section
open Classical
open scoped BigOperators
open ImbalancedChen
open U1011OriginalSixteenArithmeticProducts
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open OriginalJointPresievedArithmeticSupport OriginalJointCommonBetaModel
open All16ActualInnerWallReconstruction

/-- The complete physical carrier is the full-q image of ALL true
marked/small/rough pairs, including the displayed zero rows. -/
theorem pair_modulus_image_eq_joint (n N : ℕ) (eta : ℚ) (w : ℝ)
    (E : ℕ × ℕ → Prop) :
    (pairMarks n N eta w E).image pairModulus = jointSupport n N eta w E := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨pairToJoint a, pair_to_joint_mem ha, rfl⟩
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ht, hr⟩ := Finset.mem_sigma.mp ha
    obtain ⟨⟨e, d⟩, hed, hprod⟩ := Finset.mem_image.mp hr
    refine Finset.mem_image.mpr ⟨⟨a.1, e, d⟩, Finset.mem_sigma.mpr ⟨ht, hed⟩, ?_⟩
    exact congrArg (fun r => fullPrefix a.1 * r) hprod

theorem joint_rho_eq_pair {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t)
    {a : PairMark} (ha : a ∈ pairMarks n N eta w E) :
    jointPresievedSigma n N eta w B E (pairModulus a) = pairWeight n N eta w B a :=
  jointSigma_eq_row hN heta hw (pair_to_joint_mem ha)

/-- Complete absolute mass identity: original marked and small-beta
summations are included before any bound is taken. -/
theorem complete_marked_beta_abs_mass {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    (∑ a ∈ pairMarks n N eta w E, |pairWeight n N eta w B a|) =
      ∑ q ∈ jointSupport n N eta w E, |jointPresievedSigma n N eta w B E q| := by
  rw [← pair_modulus_image_eq_joint n N eta w E,
    Finset.sum_image (pair_modulus_injective hN heta E hw)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [joint_rho_eq_pair hN heta E hw ha]

/-- This is an actual modulus-carrier cardinality bound, not a claim
that the complete marked/raw tensor-scalar budget is fixed. -/
theorem complete_marked_beta_mass_le_carrier {n N : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) :
    (∑ a ∈ pairMarks n N eta w E, |pairWeight n N eta w B a|) ≤
      ((jointSupport n N eta w E).card : ℝ) := by
  rw [complete_marked_beta_abs_mass hN heta E hw]
  calc
    _ ≤ ∑ _q ∈ jointSupport n N eta w E, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => jointSigma_abs_le_one hN heta E hw q)
    _ = _ := by simp

/-- The wall coefficient is exactly the original joint rho on its true
wall q's, zero elsewhere. Both sides were independently constructed. -/
theorem wall_rho_eq_joint_mask {n N m : ℕ} {eta : ℚ} {w B : ℝ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop)
    (hw : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      w ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) (q : ℕ) :
    wallRho n N eta w B m E q =
      if q ∈ wallSupport n N eta w m E then jointPresievedSigma n N eta w B E q else 0 := by
  by_cases hq : q ∈ wallSupport n N eta w m E
  · rw [if_pos hq]
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    rw [wall_rho_eq_pair hN heta E hw ha,
      joint_rho_eq_pair hN heta E hw (Finset.mem_filter.mp ha).1]
  · rw [if_neg hq, wall_rho_zero_off_support n N m eta w B E hq]

/-- The complete true marked/small-beta absolute coefficient mass has
its genuine physical support-size payment. No fixed tensor-scalar mass
or polylogarithmic full-coefficient mass is inferred. -/
theorem actual_complete_marked_beta_mass_bound {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (nu0 epsilon : ℝ)
    (hnu : 0 < nu0) (he : 0 < epsilon)
    (hbudget : epsilon < OriginalCommonBetaActualParameters.epsilonBudget n eta nu0)
    (E : ℕ × ℕ → Prop) :
    (∑ a ∈ pairMarks n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E,
      |pairWeight n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) ((N : ℝ) ^ (nu0 * epsilon)) a|) ≤
      (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) + 1 : ℕ) := by
  let w := (N : ℝ) ^ (nu0 * epsilon ^ 2)
  let B := (N : ℝ) ^ (nu0 * epsilon)
  have hw (t : Four) (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :=
    (parameters_on_joint_row hN heta hnu he hbudget ht).1
  let active := (jointSupport n N eta w E).filter
    (fun q => jointPresievedSigma n N eta w B E q ≠ 0)
  have hmass : (∑ q ∈ jointSupport n N eta w E, |jointPresievedSigma n N eta w B E q|) =
      ∑ q ∈ active, |jointPresievedSigma n N eta w B E q| := by
    rw [active, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hz : jointPresievedSigma n N eta w B E q = 0 <;> simp [hz]
  have hsub : active ⊆ Finset.range (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) + 1) := by
    intro q hq
    have hnz := (Finset.mem_filter.mp hq).2
    have hcap := (actual_joint_arithmetic_support hN heta hnu he hbudget E hnz).2.2.2.2
    have hfloor : q ≤ Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) := Nat.le_floor hcap.le
    exact Finset.mem_range.mpr (by omega)
  rw [complete_marked_beta_abs_mass hN heta E hw, hmass]
  calc
    _ ≤ ∑ _q ∈ active, (1 : ℝ) :=
      Finset.sum_le_sum (fun q hq => jointSigma_abs_le_one hN heta E hw q)
    _ = (active.card : ℝ) := by simp
    _ ≤ ((Finset.range (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = _ := by simp

end
end ImbalancedChen.P5Z.All16CompleteMarkedBetaMass
