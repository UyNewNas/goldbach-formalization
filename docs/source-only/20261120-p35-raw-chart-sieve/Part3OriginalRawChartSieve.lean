import ImbalancedChen.Part3OriginalPositiveProfileBudget
import ImbalancedChen.Part3OriginalRawNSieve

/-! SOURCE ONLY / UNCOMPILED / UNEVALUATED.
Sum the fixed-level raw n sieve over the actual physical chart and
compose it with the original positive exceptional Cauchy bound. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRawChartSieve20261120
open Finset
open scoped Classical BigOperators MatrixGroups
open P3NativePeriod64SamplingSourceOnly (D4)
open OriginalCompletedReciprocalSource20261102 OriginalSimultaneousPrefixCompletion20261102
open OriginalPrimaryPacketRows20261102 OriginalTwoZSourceAssembly20261102
open OriginalTwoZFourierAssembly20261102 OriginalNativeCuspFunctionals20261102
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau pascadiJ classicalLevels)
open OriginalExceptionalPostRemovalPair20261113 (levels Slots rowMass rowLength)
open OriginalRawNSieve20261120 (raw_original_row_square)
open OriginalPositiveProfileBudget20261120 (inverseWeightedRawN profileBudget raw_chart_profile_to_pascadi)
open OriginalPositiveRawCauchy20261120 (rawSlot)
open OriginalExceptionalCosinePair20261120 (cosineCost)
open OriginalFixedLevelExceptionalSieve20261113 (sieveConstant sieveConstant_pos)
open ImbalancedChen.P3ZActualPrimaryDyadicAssembly (dyadicScale dyadicScale_pos)
open ImbalancedChen.P3ZExceptionalThresholdGeometry (threshold threshold_pos)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

private theorem chart_mem (D : OriginalData) (k : BlockKey) (upper : Bool)
    (z : ↥(levels D k upper)) : z.val.val ∈ chartLevels D k upper := by
  rcases Finset.mem_union.mp z.property with h | h <;> exact (Finset.mem_filter.mp h).2

private def originalRow (D : OriginalData) (k : BlockKey) (upper : Bool)
    (z : ↥(levels D k upper)) : Row D k :=
  ⟨z.val.val, chartLevels_subset D k upper (chart_mem D k upper z)⟩

/-- The raw inverse-weight n energy, paying the unremoved G L/Z cost. -/
theorem inverse_raw_energy_le (D : OriginalData) (r : ZMod (prefixPeriod D.key))
    (k : BlockKey) (upper negativeM : Bool) (j : ℕ) (ell : D4 → ℤ)
    (ha : D.block.atom.residue ≠ 0) :
    (∑ a : Slots D k upper, (inverseWeightedRawN D r k upper negativeM j ell a)^2) ≤
      (2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/fixedZ D upper)) *
        ∑ z : ↥(levels D k upper), rowMass D r k z.val := by
  classical
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  let G : ℝ := (((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)
  have hz : 0 < Z := fixedZ_pos D upper
  have hv : 1 ≤ V := by
    dsimp only [V]
    exact_mod_cast (Nat.succ_le_iff.mpr (pow_pos (by norm_num : (0:ℕ)<2) j))
  have hw : 1 ≤ W := hv.trans (le_max_left _ _)
  have hL : 0 ≤ rowLength k := div_nonneg (dyadicScale_pos _).le (Nat.cast_nonneg _)
  have hG : 0 ≤ G := mul_nonneg (Nat.cast_nonneg _) hL
  rw [Fintype.sum_sigma,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  have zq : Z ≤ (z.val.val : ℝ) := by
    simpa only [one_mul] using
      (le_div_iff₀ hz).mp (chartLevels_normalized D k upper (chart_mem D k upper z)).1
  have hmass : 0 ≤ rowMass D r k z.val := by
    unfold rowMass
    exact Finset.sum_nonneg (fun n _ => sq_nonneg _)
  have hpoint (i : ↥(exceptional z.val)) :
      (inverseWeightedRawN D r k upper negativeM j ell ⟨z,i⟩)^2 ≤
        ‖originalNFunctional D r k upper negativeM ell z.val.val z.val.property i.val‖^2 := by
    have ht : 0 ≤ tau z.val i.val := by unfold tau; positivity
    have hp : 1 ≤ W ^ tau z.val i.val := Real.one_le_rpow hw ht
    have hs : 1 ≤ Real.sqrt (W ^ tau z.val i.val) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
    have hdiv := div_le_self
      (norm_nonneg (originalNFunctional D r k upper negativeM ell z.val.val z.val.property i.val)) hs
    exact pow_le_pow_left₀ (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hdiv 2
  have hrow := raw_original_row_square D r k (originalRow D k upper z) upper negativeM ell ha
    (X := (1:ℝ)) (by norm_num)
  have hconst : sieveConstant*(1+max 1 (1:ℝ)) = 2*sieveConstant := by norm_num <;> ring
  simp only [one_rpow,one_mul,hconst] at hrow
  calc
    _ ≤ ∑ i : ↥(exceptional z.val),
        ‖originalNFunctional D r k upper negativeM ell z.val.val z.val.property i.val‖^2 :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ (2*sieveConstant*(1+G/(z.val.val:ℝ)))*rowMass D r k z.val := by
      simpa only [originalRow,G] using hrow
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hmass
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) sieveConstant_pos.le)
      exact add_le_add_left (div_le_div_of_nonneg_left hG hz zq) 1

/-- The actual positive exceptional chart, now with the fixed-level raw
n cost aggregated on the same occupied levels and one common phase. -/
theorem positive_chart_with_raw_sieve (D : OriginalData) (k : BlockKey)
    (upper : Bool) (J j : ℕ) (ell : D4 → ℤ) (ha : D.block.atom.residue ≠ 0) :
    let Z := fixedZ D upper
    let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
    let W := threshold V Z
    ∃ ω : ℝ, ∀ (r : ZMod (prefixPeriod D.key)) (negativeM : Bool) {Y : ℝ} (hY : 0 < Y),
      (∑ a : Slots D k upper, ‖rawSlot D r k upper negativeM J j ell Y a‖)^2 ≤
        (cosineCost*profileBudget ell hY)^2 *
          (((2+Real.log (4*V+1))^2 *
            ((pascadiJ (classicalLevels (Z/2)) W j ω +
              pascadiJ (classicalLevels Z) W j ω)/4)) *
            ((2*sieveConstant*(1+(((D.block.atom.residue.natAbs*k.1 : ℕ):ℝ)*rowLength k)/Z)) *
              ∑ z : ↥(levels D k upper), rowMass D r k z.val)) := by
  classical
  let Z := fixedZ D upper
  let V : ℝ := (((2:ℕ)^j : ℕ):ℝ)
  let W := threshold V Z
  have hw : 0 < W := threshold_pos (show 0 < V by dsimp [V]; positivity)
  obtain ⟨ω, hchart⟩ := raw_chart_profile_to_pascadi D k upper J j ell
  refine ⟨ω, ?_⟩
  intro r negativeM Y hY
  have hN := inverse_raw_energy_le D r k upper negativeM j ell ha
  have jnon (Q : ℝ) : 0 ≤ pascadiJ (classicalLevels Q) W j ω := by
    unfold pascadiJ
    apply Finset.sum_nonneg
    intro z _
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (Real.rpow_nonneg hw.le _) (sq_nonneg _)
  have hj : 0 ≤ (2+Real.log (4*V+1))^2 *
      ((pascadiJ (classicalLevels (Z/2)) W j ω +
        pascadiJ (classicalLevels Z) W j ω)/4) := by
    exact mul_nonneg (sq_nonneg _) (div_nonneg (add_nonneg (jnon _) (jnon _)) (by norm_num))
  have step := mul_le_mul_of_nonneg_left hN (mul_nonneg (sq_nonneg (cosineCost*profileBudget ell hY)) hj)
  exact (hchart r negativeM hY).trans (by simpa only [mul_assoc] using step)

end ImbalancedChen.Part3.OriginalRawChartSieve20261120
end
