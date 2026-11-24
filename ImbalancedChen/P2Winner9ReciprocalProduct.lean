import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Quadratic curvature bounds for the actual ten-factor reciprocal product. -/

namespace ImbalancedChen.P2Winner9ReciprocalProduct

noncomputable section

open Set
open scoped BigOperators

private def logRemainder (P V t : ℝ) : ℝ :=
  -Real.log t + Real.log P + (t - P) / P - (t - P)^2 / (2 * V^2)

private theorem logRemainder_derivative {P V t : ℝ} (hP : 0 < P) (hV : 0 < V)
    (ht : 0 < t) :
    HasDerivAt (logRemainder P V)
      ((t - P) * (V^2 - P * t) / (P * t * V^2)) t := by
  have hlin := ((hasDerivAt_id t).sub_const P).div_const P
  have hquad := (((hasDerivAt_id t).sub_const P).pow 2).div_const (2 * V^2)
  have hd := (((Real.hasDerivAt_log ht.ne').neg.add_const (Real.log P)).add hlin).sub hquad
  change HasDerivAt (logRemainder P V)
    (-t⁻¹ + 1 / P - (2 : ℕ) * (t - P)^(2 - 1) * 1 / (2 * V^2)) t at hd
  rw [show (t - P) * (V^2 - P * t) / (P * t * V^2) =
      -t⁻¹ + 1 / P - (2 : ℕ) * (t - P)^(2 - 1) * 1 / (2 * V^2) from by
    norm_num
    field_simp [hP.ne', hV.ne', ht.ne']
    ring]
  exact hd

/-- Original pointwise quadratic remainder, including either ordering of
its two positive endpoints. The lower curvature V^-2 is derived, not assumed. -/
theorem negLog_quadratic {a P V : ℝ} (ha : 0 < a) (hP : 0 < P)
    (haV : a ≤ V) (hPV : P ≤ V) :
    (a - P)^2 / (2 * V^2) ≤
      -Real.log a + Real.log P + (a - P) / P := by
  have hV : 0 < V := lt_of_lt_of_le ha haV
  have hD (t : ℝ) (ht : 0 < t) (htV : t ≤ V) :
      0 ≤ V^2 - P * t := by
    have hm := mul_le_mul hPV htV (by positivity : (0 : ℝ) ≤ t) hV.le
    nlinarith
  by_cases hPa : P ≤ a
  · have ht (t : ℝ) (hm : t ∈ Icc P a) : 0 < t ∧ t ≤ V :=
      ⟨lt_of_lt_of_le hP hm.1, le_trans hm.2 haV⟩
    have hc : ContinuousOn (logRemainder P V) (Icc P a) := by
      intro t hm
      exact (logRemainder_derivative hP hV (ht t hm).1).continuousAt.continuousWithinAt
    have hm : MonotoneOn (logRemainder P V) (Icc P a) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc P a) hc
      · intro t hm
        exact (logRemainder_derivative hP hV (ht t (interior_subset hm)).1).differentiableAt.differentiableWithinAt
      · intro t hm
        have hh := ht t (interior_subset hm)
        rw [(logRemainder_derivative hP hV hh.1).deriv]
        exact div_nonneg (mul_nonneg (sub_nonneg.mpr (interior_subset hm).1)
          (hD t hh.1 hh.2))
          (mul_nonneg (mul_nonneg hP.le hh.1.le) (sq_nonneg V))
    have hh := hm ⟨le_rfl, hPa⟩ ⟨hPa, le_rfl⟩ hPa
    have hz : logRemainder P V P = 0 := by simp [logRemainder]
    rw [hz] at hh
    dsimp [logRemainder] at hh
    linarith
  · have haP : a ≤ P := le_of_not_ge hPa
    have ht (t : ℝ) (hm : t ∈ Icc a P) : 0 < t ∧ t ≤ V :=
      ⟨lt_of_lt_of_le ha hm.1, le_trans hm.2 hPV⟩
    have hc : ContinuousOn (logRemainder P V) (Icc a P) := by
      intro t hm
      exact (logRemainder_derivative hP hV (ht t hm).1).continuousAt.continuousWithinAt
    have hm : AntitoneOn (logRemainder P V) (Icc a P) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc a P) hc
      · intro t hm
        exact (logRemainder_derivative hP hV (ht t (interior_subset hm)).1).differentiableAt.differentiableWithinAt
      · intro t hm
        have hh := ht t (interior_subset hm)
        rw [(logRemainder_derivative hP hV hh.1).deriv]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (interior_subset hm).2)
            (hD t hh.1 hh.2))
          (mul_nonneg (mul_nonneg hP.le hh.1.le) (sq_nonneg V))
    have hh := hm ⟨le_rfl, haP⟩ ⟨haP, le_rfl⟩ haP
    have hz : logRemainder P V P = 0 := by simp [logRemainder]
    rw [hz] at hh
    dsimp [logRemainder] at hh
    linarith

/-- Sum the actual quadratic remainders and exponentiate. The source's
linear cancellation is proved from sum(a_j)=10P; no reciprocal-product
bound is an assumption. -/
theorem reciprocal_product_quadratic (a V : Fin 10 → ℝ) (P : ℝ)
    (ha : ∀ j, 0 < a j) (hP : 0 < P) (haV : ∀ j, a j ≤ V j)
    (hPV : ∀ j, P ≤ V j) (hsum : ∑ j : Fin 10, a j = 10 * P) :
    (1 + ∑ j : Fin 10, (a j - P)^2 / (2 * (V j)^2)) / P^10 ≤
      1 / ∏ j : Fin 10, a j := by
  let Q : ℝ := ∑ j : Fin 10, (a j - P)^2 / (2 * (V j)^2)
  have hlin : (∑ j : Fin 10, (a j - P) / P) = 0 := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum]
    ring
  have hlog : Q ≤ -(∑ j : Fin 10, Real.log (a j)) + 10 * Real.log P := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 10))) =>
      negLog_quadratic (ha j) hP (haV j) (hPV j))
    simpa only [Q, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hlin, add_zero, Nat.cast_ofNat] using h
  have hprod : 0 < ∏ j : Fin 10, a j := Finset.prod_pos (fun j _ => ha j)
  have hprodLog : Real.log (∏ j : Fin 10, a j) = ∑ j : Fin 10, Real.log (a j) :=
    Real.log_prod (fun j _ => (ha j).ne')
  have he : Real.exp Q ≤ (1 / ∏ j : Fin 10, a j) * P^10 := by
    have h := Real.exp_le_exp.mpr hlog
    have hpow : Real.log (P^10) = 10 * Real.log P := by
      simp [Real.log_pow]
    rw [Real.exp_add, ← hprodLog, Real.exp_neg, Real.exp_log hprod,
      ← hpow, Real.exp_log (pow_pos hP 10)] at h
    simpa only [one_div] using h
  have hq : 1 + Q ≤ Real.exp Q := by nlinarith [Real.add_one_le_exp Q]
  apply (div_le_iff₀ (pow_pos hP 10)).2
  change 1 + Q ≤ _
  exact le_trans hq he

/-- Keeping the exact common term, the transverse correction admits the
constant denominator from any common upper bound `U` for `P`. -/
theorem reciprocal_product_constant_curvature (a V : Fin 10 → ℝ) (P U : ℝ)
    (ha : ∀ j, 0 < a j) (hP : 0 < P) (hPU : P ≤ U)
    (haV : ∀ j, a j ≤ V j) (hPV : ∀ j, P ≤ V j)
    (hsum : ∑ j : Fin 10, a j = 10 * P) :
    1 / P^10 + (∑ j : Fin 10, (a j - P)^2 / (2 * (V j)^2)) / U^10 ≤
      1 / ∏ j : Fin 10, a j := by
  let Q : ℝ := ∑ j : Fin 10, (a j - P)^2 / (2 * (V j)^2)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun j _ => div_nonneg (sq_nonneg _) (by positivity))
  have hmon : Q / U^10 ≤ Q / P^10 :=
    div_le_div_of_nonneg_left hQ (pow_pos hP _) (pow_le_pow_left₀ hP.le hPU _)
  change 1 / P^10 + Q / U^10 ≤ _
  calc
    1 / P^10 + Q / U^10 ≤ 1 / P^10 + Q / P^10 := add_le_add_right hmon _
    _ = (1 + Q) / P^10 := (add_div _ _ _).symm
    _ ≤ _ := reciprocal_product_quadratic a V P ha hP haV hPV hsum

end

end ImbalancedChen.P2Winner9ReciprocalProduct
