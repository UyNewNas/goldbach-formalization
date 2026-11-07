import ImbalancedChen.Part3ActualKQMomentOrderHolomorphy
import ImbalancedChen.Part3ContinuedFourierMomentSeriesCalculus
import Mathlib.Analysis.Complex.Schwarz

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Every ACTUAL spatial Fourier q-jet is entire in the spectral parameter.
The proved spatial-majorant strip bound and a Cauchy/Schwarz estimate give
a summable uniform bound for its actual parameter derivative. This proves
honest differentiation under every actual spatial-moment series, at every
complex parameter and positive height. The argument retains all frequency
powers and the actual finite divisor coefficient. No normal convergence,
parameter-derivative domination or mixed-commutation supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualSpatialJetParameterSeries20261026b
noncomputable section
open Set Complex Filter Metric Topology
open scoped BigOperators
open ActualKQMomentOrderHolomorphy20261026b ComplexOrderKQCalculus
open Part3ActualRamanujanDirichletSeries Part3ActualRamanujanBesselNormalConvergence
open ContinuedFourierSpatialMoments ContinuedFourierMomentSeriesCalculus

theorem spectralCoefficient_parameter_differentiable (n : ℕ) :
    Differentiable ℂ (spectralCoefficient n) := by
  have hN : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp : Differentiable ℂ (fun s : ℂ => ((n + 1 : ℕ) : ℂ) ^ (s - 1 / 2)) :=
    (differentiable_id.sub_const _).const_cpow (Or.inl hN)
  have hd : Differentiable ℂ (fun s : ℂ => divisorFactor (n + 1) (2 * s)) := by
    unfold divisorFactor
    apply Differentiable.fun_sum
    intro d hd
    have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
    exact (differentiable_const.sub (differentiable_id.const_mul (2 : ℂ))).const_cpow (Or.inl hd0)
  exact hp.mul hd

/-- Entire parameter dependence of the literal j,k spatial-moment term. -/
theorem spatialMomentTerm_parameter_differentiable (j k n : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => spatialMomentTerm j k n s y x) := by
  have hw : 0 < frequency (n + 1) := by unfold frequency; positivity
  have hK : Differentiable ℂ (fun s : ℂ => qMoment k (s - 1 / 2) (frequency (n + 1) * y)) :=
    (qMoment_order_differentiable k (mul_pos hw hy)).comp (differentiable_id.sub_const _)
  exact ((((spectralCoefficient_parameter_differentiable n).mul_const _).mul_const _).mul hK).mul_const _

private theorem re_strip_of_ball {s w : ℂ} {M : ℕ}
    (hs : |s.re| ≤ (M : ℝ)) (hw : w ∈ ball s (1 : ℝ)) : |w.re| ≤ ((M + 1 : ℕ) : ℝ) := by
  have hn : ‖w - s‖ < (1 : ℝ) := by simpa only [mem_ball, dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w - s)).trans_lt hn
  simp only [Complex.sub_re] at hr
  have hsr := abs_le.mp hs
  have hwr := abs_lt.mp hr
  apply abs_le.mpr
  push_cast
  constructor <;> linarith

/-- An ACTUAL summable parameter-derivative majorant, uniform over the
whole closed spectral strip, all horizontal x, and all y>=a. -/
theorem spatialMomentTerm_parameter_derivative_bound (j k M n : ℕ) {a : ℝ} (ha : 0 < a)
    {s : ℂ} (hs : |s.re| ≤ (M : ℝ)) {y : ℝ} (hy : a ≤ y) (x : ℝ) :
    ‖deriv (fun w : ℂ => spatialMomentTerm j k n w y x) s‖ ≤
      2 * spatialMajorant j k (M + 1) a n := by
  have hy0 : 0 < y := ha.trans_le hy
  let U : ℝ := spatialMajorant j k (M + 1) a n
  have hvalue (w : ℂ) (hw : w ∈ ball s (1 : ℝ)) : ‖spatialMomentTerm j k n w y x‖ ≤ U :=
    spatialMomentTerm_norm_bound j k (M + 1) ha n (re_strip_of_ball hs hw) hy x
  have hsvalue : ‖spatialMomentTerm j k n s y x‖ ≤ U :=
    spatialMomentTerm_norm_bound j k (M + 1) ha n
      (hs.trans (by exact_mod_cast Nat.le_succ M)) hy x
  have hmaps : MapsTo (fun w : ℂ => spatialMomentTerm j k n w y x) (ball s (1 : ℝ))
      (closedBall (spatialMomentTerm j k n s y x) (2 * U)) := by
    intro w hw
    apply mem_closedBall.mpr
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hvalue w hw, hsvalue])
  have h := Complex.norm_deriv_le_div_of_mapsTo_ball
    (spatialMomentTerm_parameter_differentiable j k n hy0 x).differentiableOn hmaps (by norm_num : (0 : ℝ) < 1)
  simpa only [div_one] using h

def momentParameterSum (j k : ℕ) (s : ℂ) (y x : ℝ) : ℂ :=
  ∑' n : ℕ, deriv (fun w : ℂ => spatialMomentTerm j k n w y x) s

theorem spatialParameterDerivative_norm_summable (j k : ℕ) (s : ℂ)
    {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => ‖deriv (fun w : ℂ => spatialMomentTerm j k n w y x) s‖) := by
  let M : ℕ := Nat.ceil |s.re|
  exact ((spatialMajorant_summable j k (M + 1) hy).const_mul 2).of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun n => spatialMomentTerm_parameter_derivative_bound j k M n hy (Nat.le_ceil _) le_rfl x)

/-- Genuine parameter differentiation under the ACTUAL spatial q-jet
series, proved with a local summable derivative majorant. -/
theorem momentSum_hasDerivAt_parameter (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => momentSum j k w y x) (momentParameterSum j k s y x) s := by
  let M : ℕ := Nat.ceil |s.re| + 1
  have hs : |s.re| ≤ ((Nat.ceil |s.re| : ℕ) : ℝ) := Nat.le_ceil _
  have hstrip (w : ℂ) (hw : w ∈ ball s (1 : ℝ)) : |w.re| ≤ (M : ℝ) :=
    re_strip_of_ball hs hw
  refine hasDerivAt_tsum_of_isPreconnected
    ((spatialMajorant_summable j k (M + 1) hy).const_mul 2)
    isOpen_ball (convex_ball s (1 : ℝ)).isPreconnected
    (fun n w hw => (spatialMomentTerm_parameter_differentiable j k n hy x w).hasDerivAt)
    (fun n w hw => spatialMomentTerm_parameter_derivative_bound j k M n hy (hstrip w hw) le_rfl x)
    (mem_ball_self (by norm_num : (0 : ℝ) < 1))
    (spatialMoment_norm_summable j k s hy x).of_norm
    (mem_ball_self (by norm_num : (0 : ℝ) < 1))

theorem momentSum_parameter_differentiable (j k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Differentiable ℂ (fun s : ℂ => momentSum j k s y x) :=
  fun s => (momentSum_hasDerivAt_parameter j k s y x hy).differentiableAt

theorem momentSum_parameter_analyticAt (j k : ℕ) {y : ℝ} (hy : 0 < y) (x : ℝ) (s : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => momentSum j k w y x) s :=
  (momentSum_parameter_differentiable j k hy x).analyticAt s

theorem momentSum_parameter_deriv (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    deriv (fun w : ℂ => momentSum j k w y x) s = momentParameterSum j k s y x :=
  (momentSum_hasDerivAt_parameter j k s y x hy).deriv

/-- Both frequency signs retain their true complex parameter derivative. -/
theorem signedMomentSum_hasDerivAt_parameter (j k : ℕ) (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => signedMomentSum j k w y x)
      (momentParameterSum j k s y x + (-1 : ℂ) ^ j * momentParameterSum j k s y (-x)) s :=
  (momentSum_hasDerivAt_parameter j k s y x hy).add
    ((momentSum_hasDerivAt_parameter j k s y (-x) hy).const_mul ((-1 : ℂ) ^ j))

end
end ImbalancedChen.Part3.ActualSpatialJetParameterSeries20261026b
