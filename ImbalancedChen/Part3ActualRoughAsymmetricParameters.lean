import ImbalancedChen.Part3ActualRoughContourParameters

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual asymmetric Perron scalar geometry. The right displacement is
1/log X, so its X-power is exactly exp 1. The original left displacement
is half the actual rough width d*(loglog x)^3/log x. One threshold precedes
every X>=x^theta and pays every fixed logarithmic loss on the left.
Only real rpow/log/exp algebra and cubic dominance are used. No zero-free,
holomorphy, Perron, contour, SW, or final saving premise is supplied.
-/

namespace ImbalancedChen.Part3.ActualRoughAsymmetricParameters20261026b
noncomputable section
open Filter Topology
open ActualRoughContourParameters20261026b

def rightOffset (X : ℝ) : ℝ := 1 / Real.log X

def loglogThreshold (d theta A M : ℝ) : ℝ :=
  max 1 (max (1 / (d * theta)) ((A + 2 * M) / (d * theta / 2)))

private theorem cubic_dominates_linear {c K t : ℝ}
    (hc : 0 < c) (ht : 1 ≤ t) (hKt : K / c ≤ t) :
    K * t ≤ c * t ^ 3 := by
  have ht0 : 0 ≤ t := by linarith
  have hct : K ≤ c * t := by
    have h := (div_le_iff₀ hc).mp hKt
    nlinarith
  have htsq : t ≤ t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hctsq : K ≤ c * t ^ 2 :=
    hct.trans (mul_le_mul_of_nonneg_left htsq hc.le)
  have h := mul_le_mul_of_nonneg_right hctsq ht0
  nlinarith

/-- An explicit loglog threshold supplies all scalar gates at once,
before the arbitrary interval scale X. -/
theorem asymmetric_parameters_of_loglog_large
    {d theta A M x : ℝ} (hd : 0 < d) (htheta : 0 < theta)
    (_hA : 0 ≤ A) (hM : 0 ≤ M) (hx : 1 < x)
    (hL : 2 ≤ Real.log x)
    (hell : loglogThreshold d theta A M ≤ Real.log (Real.log x)) :
    ∀ X : ℝ, x ^ theta ≤ X →
      1 < X ∧ 0 < rightOffset X ∧ rightOffset X ≤ roughDelta d x ∧
      rightOffset X * Real.log X = 1 ∧
      X ^ (rightOffset X) = Real.exp 1 ∧
      X ^ (-(roughDelta d x) / 2) * (1 + Real.log x) ^ M ≤
        (Real.log x) ^ (-A) := by
  have hxpos : 0 < x := by linarith
  have hLp : 0 < Real.log x := by linarith
  have hell1 : 1 ≤ Real.log (Real.log x) :=
    (le_max_left _ _).trans hell
  have hellp : 0 < Real.log (Real.log x) := by linarith
  have hsmall : 1 / (d * theta) ≤ Real.log (Real.log x) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hell)
  have hlarge : (A + 2 * M) / (d * theta / 2) ≤ Real.log (Real.log x) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hell)
  have hdelta := roughDelta_eq d hx hellp
  have hdeltap : 0 < roughDelta d x := by rw [hdelta]; positivity
  have hc : 0 < d * theta := mul_pos hd htheta
  have hone : 1 ≤ d * theta * (Real.log (Real.log x)) ^ 3 := by
    have h := cubic_dominates_linear hc hell1 hsmall
    nlinarith
  have hpay := cubic_dominates_linear (div_pos hc (by norm_num : (0 : ℝ) < 2))
    hell1 hlarge
  intro X hX
  have hX1 : 1 < X := (Real.one_lt_rpow hx htheta).trans_le hX
  have hXp : 0 < X := by linarith
  have hlogXp : 0 < Real.log X := Real.log_pos hX1
  have hlogX : theta * Real.log x ≤ Real.log X := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hxpos theta) hX
    simpa only [Real.log_rpow hxpos] using h
  have hwidth : 1 ≤ roughDelta d x * Real.log X := by
    calc
      1 ≤ d * theta * (Real.log (Real.log x)) ^ 3 := hone
      _ = roughDelta d x * (theta * Real.log x) := by
        rw [hdelta]
        field_simp [hLp.ne']
        ring
      _ ≤ roughDelta d x * Real.log X :=
        mul_le_mul_of_nonneg_left hlogX hdeltap.le
  have hxi : rightOffset X ≤ roughDelta d x := by
    exact (div_le_iff₀ hlogXp).mpr hwidth
  have hproduct : rightOffset X * Real.log X = 1 := by
    exact div_mul_cancel₀ 1 hlogXp.ne'
  have hright : X ^ (rightOffset X) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hXp]
    congr 1
    simpa only [mul_comm] using hproduct
  have hcost : (A + 2 * M) * Real.log (Real.log x) ≤
      roughDelta d x / 2 * Real.log X := by
    calc
      _ ≤ (d * theta / 2) * (Real.log (Real.log x)) ^ 3 := hpay
      _ = roughDelta d x / 2 * (theta * Real.log x) := by
        rw [hdelta]
        field_simp [hLp.ne']
        ring
      _ ≤ roughDelta d x / 2 * Real.log X :=
        mul_le_mul_of_nonneg_left hlogX (div_nonneg hdeltap.le (by norm_num))
  have hsumSquare : 1 + Real.log x ≤ (Real.log x) ^ 2 := by
    calc
      _ ≤ 2 * Real.log x := by linarith
      _ ≤ Real.log x * Real.log x := mul_le_mul_of_nonneg_right hL hLp.le
      _ = _ := by ring
  have hlogSum : Real.log (1 + Real.log x) ≤ 2 * Real.log (Real.log x) := by
    have h := Real.log_le_log (by linarith : 0 < 1 + Real.log x) hsumSquare
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hleft : X ^ (-(roughDelta d x) / 2) * (1 + Real.log x) ^ M ≤
      (Real.log x) ^ (-A) := by
    rw [Real.rpow_def_of_pos hXp,
      Real.rpow_def_of_pos (by linarith : 0 < 1 + Real.log x),
      ← Real.exp_add, Real.rpow_def_of_pos hLp]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hlogSum hM
    nlinarith
  exact ⟨hX1, one_div_pos.mpr hlogXp, hxi, hproduct, hright, hleft⟩

/-- Eventual uniformity is before ALL interval scales X>=x^theta. -/
theorem eventually_actual_asymmetric_parameters
    (d theta A M : ℝ) (hd : 0 < d) (htheta : 0 < theta)
    (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∀ᶠ x : ℝ in atTop, ∀ X : ℝ, x ^ theta ≤ X →
      1 < X ∧ 0 < rightOffset X ∧ rightOffset X ≤ roughDelta d x ∧
      rightOffset X * Real.log X = 1 ∧
      X ^ (rightOffset X) = Real.exp 1 ∧
      X ^ (-(roughDelta d x) / 2) * (1 + Real.log x) ^ M ≤
        (Real.log x) ^ (-A) := by
  have hell := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop (loglogThreshold d theta A M))
  have hL := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hell, hL, eventually_gt_atTop (1 : ℝ)] with x hellx hLx hx
  exact asymmetric_parameters_of_loglog_large hd htheta hA hM hx hLx hellx

/-- One real threshold precedes every X and gives exactly exp(1),
rather than the incorrect growing right cost X^delta. -/
theorem exists_actual_asymmetric_threshold
    (d theta A M : ℝ) (hd : 0 < d) (htheta : 0 < theta)
    (hA : 0 ≤ A) (hM : 0 ≤ M) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ x : ℝ, x0 ≤ x → ∀ X : ℝ, x ^ theta ≤ X →
      1 < X ∧ 0 < rightOffset X ∧ rightOffset X ≤ roughDelta d x ∧
      rightOffset X * Real.log X = 1 ∧
      X ^ (rightOffset X) = Real.exp 1 ∧
      X ^ (-(roughDelta d x) / 2) * (1 + Real.log x) ^ M ≤
        (Real.log x) ^ (-A) := by
  obtain ⟨r, hr⟩ := eventually_atTop.mp
    (eventually_actual_asymmetric_parameters d theta A M hd htheta hA hM)
  refine ⟨max r 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x hx X hX
  exact hr x ((le_max_left _ _).trans hx) X hX

end
end ImbalancedChen.Part3.ActualRoughAsymmetricParameters20261026b
