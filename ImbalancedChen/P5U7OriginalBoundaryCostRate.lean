import ImbalancedChen.P5U7OriginalGridBoundaryArea
import ImbalancedChen.P5U7OriginalUniformLogTail

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual generated rational-cover boundary cost has an explicit
vanishing rate. Proved uniform Taylor bounds give numeratorUpper<=1;
the original positive grid cutoff gives every actual cell upper<=125.
Thus the complete outer-minus-inner weighted boundary sum costs at most
125 times its proved O(1/m) geometric area. No coefficient cap is supplied.
-/

namespace ImbalancedChen.P5U7OriginalBoundaryCostRate

noncomputable section

open Filter Topology P2ContinuousSieveRational
open P5U7OriginalStraddlingCells P5U7OriginalStaircaseGeometry
open P5U7OriginalGridBoundaryArea P5U7OriginalUniformLogTail
open scoped BigOperators

theorem uniform_rate_le (n : ℕ) : rate n ≤ 4 * (7 / 66 : ℚ) := by
  have hp : (7 / 66 : ℚ) ^ (2 * n) ≤ 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  unfold rate
  rw [pow_succ]
  nlinarith only [hp]

theorem actual_logUpper_le_one (n : ℕ) (q : ℚ)
    (hq : 2 ≤ q) (hM : q ≤ 132 / 59) : logUpper n q ≤ 1 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hMR : (q : ℝ) ≤ 132 / 59 := by exact_mod_cast hM
  have hlog := Real.log_le_sub_one_of_pos (show 0 < (q : ℝ) - 1 by linarith)
  have hLo := (log_bounds n q hq).1
  have hGap : (logUpper n q : ℝ) - (logLower n q : ℝ) ≤ (rate n : ℝ) := by
    exact_mod_cast (rational_gap_le_rate n q hq hM).2
  have hRate : (rate n : ℝ) ≤ 4 * (7 / 66 : ℝ) := by
    exact_mod_cast uniform_rate_le n
  have hreal : (logUpper n q : ℝ) ≤ 1 := by
    linarith only [hMR, hlog, hLo, hGap, hRate]
  exact_mod_cast hreal

theorem numeratorUpper_le_one (B : Box) (n : ℕ) : B.numeratorUpper n ≤ 1 := by
  obtain ⟨hFL, _, _, _, hSL, _, hSH, hSM⟩ := Box.clamp_guards B
  have hf : 1 / B.firstLo ≤ 1 :=
    (div_le_iff₀ (by linarith : 0 < B.firstLo)).mpr (by linarith)
  have hs : (1 + logUpper n B.secondHi) / B.secondLo ≤ 1 := by
    apply (div_le_iff₀ (by linarith : 0 < B.secondLo)).mpr
    linarith only [actual_logUpper_le_one n B.secondHi hSH hSM, hSL]
  unfold Box.numeratorUpper
  split_ifs
  · exact hf
  · exact hs
  · exact max_le hf hs

/-- Actual generated-cell cap, using the literal original d cutoff. -/
theorem generated_cell_upper_le (n m : ℕ) (hm : 0 < m) (i : Index m) :
    (cell m i).upper n ≤ 125 := by
  have ha := (mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm i.1 i.1.isLt.le).1
  have hc := (mesh_bounds ulo uhi (by norm_num [ulo, uhi]) m hm i.2 i.2.isLt.le).1
  have ha5 : (1 / 5 : ℚ) ≤ (cell m i).a := by
    change 1 / 5 ≤ mesh tlo thi m i.1
    norm_num [tlo] at ha
    linarith only [ha]
  have hc5 : (1 / 5 : ℚ) ≤ (cell m i).c := by
    change 1 / 5 ≤ mesh ulo uhi m i.2
    norm_num [ulo] at hc
    linarith only [hc]
  have ha0 : 0 < (cell m i).a := lt_of_lt_of_le (by norm_num) ha5
  have hc0 : 0 < (cell m i).c := lt_of_lt_of_le (by norm_num) hc5
  have hden : (1 / 125 : ℚ) ≤ (cell m i).a * (cell m i).c ^ 2 := by
    calc
      _ = (1 / 5 : ℚ) * (1 / 5 : ℚ) ^ 2 := by norm_num
      _ ≤ _ := mul_le_mul ha5 (pow_le_pow_left₀ (by norm_num) hc5 2)
        (by positivity) ha0.le
  have hden0 : 0 < (cell m i).a * (cell m i).c ^ 2 := by positivity
  unfold Box.upper
  calc
    _ ≤ 1 / ((cell m i).a * (cell m i).c ^ 2) :=
      div_le_div_of_nonneg_right (numeratorUpper_le_one _ n) hden0.le
    _ ≤ 125 := (div_le_iff₀ hden0).mpr (by linarith only [hden])

def rationalBoundaryCost (n m : ℕ) : ℚ :=
  ∑ i ∈ boundaryIndices m, (cell m i).upper n * (cell m i).area

theorem rationalBoundaryCost_le (n m : ℕ) (hm : 0 < m) :
    rationalBoundaryCost n m ≤ 125 * areaRate m := by
  have hsum : rationalBoundaryCost n m ≤ 125 * rationalBoundaryArea m := by
    unfold rationalBoundaryCost rationalBoundaryArea
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hvalid := cell_valid m hm i
    have harea : 0 ≤ (cell m i).area := by
      unfold Box.area
      exact mul_nonneg (sub_nonneg.mpr hvalid.2.1) (sub_nonneg.mpr hvalid.2.2.2.2)
    exact mul_le_mul_of_nonneg_right (generated_cell_upper_le n m hm i) harea
  exact hsum.trans (mul_le_mul_of_nonneg_left (rationalBoundaryArea_le_rate m hm) (by norm_num))

theorem tendsto_areaRate : Tendsto (fun m : ℕ => (areaRate m : ℝ)) atTop (𝓝 0) := by
  have hi : Tendsto (fun m : ℕ => (m : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hi.const_mul
    (((thi - tlo) * (3 * (thi - tlo) + 4 * (uhi - ulo)) : ℚ) : ℝ)
  simpa only [areaRate_eq_constant_div, Rat.cast_div, Rat.cast_natCast,
    div_eq_mul_inv, mul_zero] using h

theorem tendsto_boundaryCost_fixed_precision (n : ℕ) :
    Tendsto (fun m : ℕ => (rationalBoundaryCost n m : ℝ)) atTop (𝓝 0) := by
  have hmajor := tendsto_areaRate.const_mul (125 : ℝ)
  apply squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using hmajor)
  · exact Filter.Eventually.of_forall (fun m => by
      unfold rationalBoundaryCost
      push_cast
      apply Finset.sum_nonneg
      intro i hi
      have hm : 0 < m := Nat.zero_lt_of_lt i.1.isLt
      have hvalid := cell_valid m hm i
      have harea : 0 ≤ (cell m i).area := by
        unfold Box.area
        exact mul_nonneg (sub_nonneg.mpr hvalid.2.1) (sub_nonneg.mpr hvalid.2.2.2.2)
      exact_mod_cast mul_nonneg (Box.upper_nonneg hvalid n) harea)
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    exact_mod_cast rationalBoundaryCost_le n m (by omega)

end

end ImbalancedChen.P5U7OriginalBoundaryCostRate
