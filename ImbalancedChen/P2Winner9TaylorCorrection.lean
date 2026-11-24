import ImbalancedChen.P2Winner9PowerMoment

namespace ImbalancedChen.P2Winner9TaylorCorrection

noncomputable section

open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor (gapTotal)
open ImbalancedChen.P2Winner9PowerMoment
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne (actualGapMass_pos)

private def spike (i r : Fin 9) : ℕ := if r = i then 1 else 0

/-- The weak compositions of one are the unit exponent vectors. -/
private theorem sum_compositions_one {M : Type*} [AddCommMonoid M] (f : (Fin 9 → ℕ) → M) :
    (∑ e ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 9)) 1, f e) =
      ∑ i : Fin 9, f (spike i) := by
  symm
  refine Finset.sum_nbij spike ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i _
    refine Finset.mem_piAntidiag.mpr ⟨?_, fun r _ => Finset.mem_univ r⟩
    change (∑ r : Fin 9, spike i r) = 1
    simp [spike, Finset.sum_ite_eq']
  · intro a _ b _ hab
    by_contra h
    have hh := congrFun hab a
    simp [spike, h] at hh
  · intro e he
    have hsum : (∑ r, e r) = 1 := (Finset.mem_piAntidiag.mp (Finset.mem_coe.mp he)).1
    have hex : ∃ i, e i ≠ 0 := by
      by_contra! h
      simp [h] at hsum
    obtain ⟨i, hi⟩ := hex
    have hi1 : e i = 1 := by
      have := Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hrest : ∑ r ∈ Finset.univ.erase i, e r = 0 := by
      have h := Finset.sum_erase_add Finset.univ e (Finset.mem_univ i)
      omega
    refine ⟨i, Finset.mem_coe.mpr (Finset.mem_univ _), funext (fun r => ?_)⟩
    by_cases hr : r = i
    · subst r
      simp [spike, hi1]
    · have hh := Finset.single_le_sum (f := e) (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ r⟩)
      simp [spike, hr, Nat.eq_zero_of_le_zero (hrest ▸ hh)]

private theorem weightedMoment_one (d : SimplexData) :
    weightedMoment d 1 = meanNumerator d := by
  rw [weightedMoment_eq_compositions]
  simp_rw [sum_compositions_one]
  have hprod (i : Fin 9) : (∏ r, d.y r ^ spike i r) = d.y i := by
    rw [Fintype.prod_eq_single i (fun r hr => by simp [spike, hr])]
    simp [spike]
  simp_rw [hprod, spike, add_mul, one_mul, ite_mul, zero_mul, Finset.sum_add_distrib]
  simp only [Finset.mem_univ, if_true, Finset.sum_ite_eq, one_mul, mul_add]
  rw [meanNumerator, gapTotal, Finset.sum_add_distrib, ← Finset.sum_mul]
  exact Nat.add_comm _ _

/-- The genuine first power moment equals the exact mean ratio. -/
theorem actualPowerExpectation_one (d : SimplexData) :
    actualPowerExpectation d 1 = (meanNumerator d : ℝ) / (D d : ℝ) := by
  rw [actualPowerExpectation_eq_weightedMoment, weightedMoment_one]
  norm_num [D, H, Nat.factorial_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem choose_mul_actualPowerExpectation (d : SimplexData) (k : ℕ) :
    ((9 + k).choose k : ℝ) * actualPowerExpectation d k =
      (weightedMoment d k : ℝ) / ((gapTotal d.gaps : ℝ) * (d.U : ℝ)^k) := by
  have hchoose : ((9 + k).choose k : ℝ) * ((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ) =
      ((k + 9).factorial : ℝ) := by
    rw [Nat.add_comm k 9]
    exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial 9 k)
  rw [actualPowerExpectation_eq_weightedMoment]
  calc
    _ = (((9 + k).choose k : ℝ) * ((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ) /
        ((k + 9).factorial : ℝ)) *
        ((weightedMoment d k : ℝ) / ((gapTotal d.gaps : ℝ) * (d.U : ℝ)^k)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hchoose, div_self (by positivity), one_mul]

/-- The exact integer source numerator represents the binomially weighted
Jensen gap for the genuine canonical power moment. -/
theorem actualPowerGap_eq_z (d : SimplexData) (k : ℕ) :
    ((9 + k).choose k : ℝ) *
        (actualPowerExpectation d k - (actualPowerExpectation d 1)^k) =
      (z d k : ℝ) / ((gapTotal d.gaps : ℝ) * (D d : ℝ)^k) := by
  have hH : (H d : ℝ) ≠ 0 := by
    have hg := d.gapsPos
    unfold H
    positivity
  rw [mul_sub, choose_mul_actualPowerExpectation, actualPowerExpectation_one]
  simp only [z, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, sub_div]
  congr 1
  · simp only [D, Nat.cast_mul, mul_pow]
    calc
      _ = ((weightedMoment d k : ℝ) / ((gapTotal d.gaps : ℝ) * (d.U : ℝ)^k)) *
          ((H d : ℝ)^k / (H d : ℝ)^k) := by rw [div_self (pow_ne_zero _ hH), mul_one]
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  · have hg : (gapTotal d.gaps : ℝ) ≠ 0 := by exact_mod_cast d.gapsPos.ne'
    calc
      _ = (((9 + k).choose k : ℝ) * ((meanNumerator d : ℝ) / (D d : ℝ))^k) *
          ((gapTotal d.gaps : ℝ) / (gapTotal d.gaps : ℝ)) := by rw [div_self hg, mul_one]
      _ = _ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

/-- The exact source correction is the canonical Jensen power correction
with the physical reciprocal tenth-power scale. -/
theorem actualTaylorCorrection_eq_t10 (d : SimplexData) :
    ((d.L : ℝ) / (d.U : ℝ))^10 *
      (∑ k ∈ Finset.Icc 2 10, ((9 + k).choose k : ℝ) *
        (actualPowerExpectation d k - (actualPowerExpectation d 1)^k)) =
      (value (t10 d) : ℝ) := by
  have hD : (D d : ℝ) ≠ 0 := by
    have hg := d.gapsPos
    have hu := d.UPos
    unfold D H
    positivity
  simp_rw [actualPowerGap_eq_z]
  unfold value t10 t10Numerator t10Denominator
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hle := (Finset.mem_Icc.mp hk).2
  have hpow : (D d : ℝ)^10 = (D d : ℝ)^k * (D d : ℝ)^(10 - k) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow, div_pow]
  symm
  calc
    _ = ((D d : ℝ)^(10 - k) * ((D d : ℝ)^(10 - k))⁻¹) *
        (((d.L : ℝ)^10 / (d.U : ℝ)^10) *
          ((z d k : ℝ) / ((gapTotal d.gaps : ℝ) * (D d : ℝ)^k))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hD), one_mul]

/-- The source Taylor identity with the original physical upper bound and
the symmetric binomial coefficient. -/
theorem actual_T10_identity (d : SimplexData) :
    (value (t10 d) : ℝ) =
      (1 / ((d.U : ℝ) / (d.L : ℝ))^10) *
        (∑ k ∈ Finset.Icc 2 10, ((9 + k).choose 9 : ℝ) *
          (actualPowerExpectation d k - (actualPowerExpectation d 1)^k)) := by
  simp_rw [Nat.choose_symm_add (a := 9)]
  rw [← actualTaylorCorrection_eq_t10]
  simp only [one_div, div_pow, inv_div]

/-- The canonical gap density has total probability one. -/
theorem actualPowerExpectation_zero (d : SimplexData) :
    actualPowerExpectation d 0 = 1 := by
  simp only [actualPowerExpectation, actualPowerNumerator, pow_zero, mul_one]
  exact div_self (ne_of_gt (actualGapMass_pos d))

/-- The form used by the probability Jensen theorem, including the two
identically zero terms for degrees zero and one. -/
theorem actual_T10_identity_range (d : SimplexData) :
    (value (t10 d) : ℝ) =
      (1 / ((d.U : ℝ) / (d.L : ℝ))^10) *
        (∑ k ∈ Finset.range 11, ((9 + k).choose k : ℝ) *
          (actualPowerExpectation d k - (actualPowerExpectation d 1)^k)) := by
  rw [actual_T10_identity]
  simp_rw [Nat.choose_symm_add (a := 9)]
  congr 1
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hk).2)
  · intro k hk hnot
    have hsmall : k = 0 ∨ k = 1 := by
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Icc] at hnot
      omega
    rcases hsmall with rfl | rfl
    · simp [actualPowerExpectation_zero]
    · simp

end

end ImbalancedChen.P2Winner9TaylorCorrection
