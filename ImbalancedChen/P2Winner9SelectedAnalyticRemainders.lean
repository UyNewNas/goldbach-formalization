import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The source's true quadratic -log remainder is proved from the sign of
its explicit derivative on the positive bounded segment. The finite
binomial lower polynomial also receives an explicit nonnegative remainder.
The T10 Jensen-GAP bound still needs the convex/expectation remainder step;
a mere nonnegative pointwise remainder is not silently substituted for it.
-/

namespace ImbalancedChen.P2Winner9SelectedAnalyticRemainders

noncomputable section

open Set
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9PhysicalAffineTransfer

def logRemainder (P V t : ℝ) : ℝ :=
  -Real.log t + Real.log P + (t - P) / P - (t - P)^2 / (2 * V^2)

theorem logRemainder_derivative {P V t : ℝ} (hP : 0 < P) (hV : 0 < V)
    (ht : 0 < t) :
    HasDerivAt (logRemainder P V)
      ((t - P) * (V^2 - P * t) / (P * t * V^2)) t := by
  have hlin := ((hasDerivAt_id t).sub_const P).div_const P
  have hquad := (((hasDerivAt_id t).sub_const P).pow 2).div_const (2 * V^2)
  have hd := (((Real.hasDerivAt_log ht.ne').neg.add_const (Real.log P)).add hlin).sub hquad
  convert hd using 1
  · ext x
    rfl
  · field_simp [hP.ne', hV.ne', ht.ne'] <;> ring

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
      apply monotoneOn_of_deriv_nonneg convex_Icc hc
      · intro t hm
        exact (logRemainder_derivative hP hV (ht t (interior_subset hm)).1).differentiableAt.differentiableWithinAt
      · intro t hm
        have hh := ht t (interior_subset hm)
        rw [(logRemainder_derivative hP hV hh.1).deriv]
        exact div_nonneg (mul_nonneg (sub_nonneg.mpr (interior_subset hm).1)
          (hD t hh.1 hh.2)) (by positivity)
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
      apply antitoneOn_of_deriv_nonpos convex_Icc hc
      · intro t hm
        exact (logRemainder_derivative hP hV (ht t (interior_subset hm)).1).differentiableAt.differentiableWithinAt
      · intro t hm
        have hh := ht t (interior_subset hm)
        rw [(logRemainder_derivative hP hV hh.1).deriv]
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (interior_subset hm).2)
            (hD t hh.1 hh.2)) (by positivity)
    have hh := hm ⟨le_rfl, haP⟩ ⟨haP, le_rfl⟩ haP
    have hz : logRemainder P V P = 0 := by simp [logRemainder]
    rw [hz] at hh
    dsimp [logRemainder] at hh
    linarith

/-- The actual rows supply all endpoint hypotheses of the original
quadratic inequality; there is no row-level curvature premise. -/
theorem actual_row_negLog_quadratic (r : Fin 2) {z : Ambient}
    (hz : z ∈ P2Winner9SelectedRowRealJacobian.sourceSupport (vertices r))
    (j : Fin 10) :
    ((normalizedFactor (fun k => (means r k : ℝ)) j z -
      physicalP (fun k => (means r k : ℝ)) z)^2 /
        (2 * (transverseUpper r j : ℝ)^2)) ≤
      -Real.log (normalizedFactor (fun k => (means r k : ℝ)) j z) +
        Real.log (physicalP (fun k => (means r k : ℝ)) z) +
        (normalizedFactor (fun k => (means r k : ℝ)) j z -
          physicalP (fun k => (means r k : ℝ)) z) /
            physicalP (fun k => (means r k : ℝ)) z := by
  have hc := actual_support_caps r hz
  have hj := hc.2.2.2.2 j
  have hp : 0 < physicalP (fun k => (means r k : ℝ)) z :=
    lt_of_lt_of_le (by exact_mod_cast (actual_vertex_guards r).2.1) hc.2.2.1
  exact negLog_quadratic hj.1 hp hj.2.1 hj.2.2

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
      hlin, add_zero] using h
  have hprod : 0 < ∏ j : Fin 10, a j := Finset.prod_pos (fun j _ => ha j)
  have hprodLog : Real.log (∏ j : Fin 10, a j) = ∑ j : Fin 10, Real.log (a j) :=
    Real.log_prod (fun j _ => (ha j).ne')
  have he : Real.exp Q ≤ (1 / ∏ j : Fin 10, a j) * P^10 := by
    have h := Real.exp_le_exp.mpr hlog
    rw [Real.exp_add, ← hprodLog, Real.exp_neg, Real.exp_log hprod,
      ← Real.log_pow, Real.exp_log (pow_pos hP 10)] at h
    simpa only [one_div] using h
  have hq : 1 + Q ≤ Real.exp Q := by nlinarith [Real.add_one_le_exp Q]
  apply (div_le_iff₀ (pow_pos hP 10)).2
  change 1 + Q ≤ _
  exact le_trans hq he

/-- Original pointwise common-affine plus transverse bound on the actual
row supports, preserving the ten original normalized factors. -/
theorem actual_row_product_quadratic (r : Fin 2) {z : Ambient}
    (hz : z ∈ P2Winner9SelectedRowRealJacobian.sourceSupport (vertices r)) :
    (1 + ∑ j : Fin 10,
      (normalizedFactor (fun k => (means r k : ℝ)) j z -
        physicalP (fun k => (means r k : ℝ)) z)^2 /
          (2 * (transverseUpper r j : ℝ)^2)) /
      (physicalP (fun k => (means r k : ℝ)) z)^10 ≤
        1 / ∏ j : Fin 10, normalizedFactor (fun k => (means r k : ℝ)) j z := by
  have hc := actual_support_caps r hz
  have hp : 0 < physicalP (fun k => (means r k : ℝ)) z :=
    lt_of_lt_of_le (by exact_mod_cast (actual_vertex_guards r).2.1) hc.2.2.1
  apply reciprocal_product_quadratic _ _ _
    (fun j => (hc.2.2.2.2 j).1) hp
    (fun j => (hc.2.2.2.2 j).2.1) (fun j => (hc.2.2.2.2 j).2.2)
  unfold physicalP
  ring

def binomial10 (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 11, ((9 + k).choose k : ℝ) * y^k

def binomial10RemainderNumerator (y : ℝ) : ℝ :=
  y^11 * ∑ j ∈ Finset.range 10, ((10 + j).choose j : ℝ) * (1 - y)^j

/-- Exact finite negative-binomial tail identity, proved algebraically. -/
theorem binomial10_remainder_identity (y : ℝ) :
    (1 - y)^10 * binomial10 y + binomial10RemainderNumerator y = 1 := by
  norm_num [binomial10, binomial10RemainderNumerator, Finset.sum_range_succ]
  ring

theorem binomial10_remainder_nonneg {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 ≤ binomial10RemainderNumerator y := by
  apply mul_nonneg (pow_nonneg hy _)
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (sub_nonneg.mpr hy1) _)

/-- A true finite pointwise binomial minorant with its positive remainder.
This alone is not the required T10 Jensen-gap expectation inequality. -/
theorem binomial10_pointwise {y : ℝ} (hy : 0 ≤ y) (hy1 : y < 1) :
    binomial10 y ≤ 1 / (1 - y)^10 := by
  have hd : 0 < (1 - y)^10 := by positivity
  apply (le_div_iff₀ hd).2
  have h := binomial10_remainder_identity y
  have hr := binomial10_remainder_nonneg hy hy1.le
  nlinarith

end

end ImbalancedChen.P2Winner9SelectedAnalyticRemainders
