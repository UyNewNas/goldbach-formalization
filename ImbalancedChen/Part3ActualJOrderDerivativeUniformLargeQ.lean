import ImbalancedChen.Part3ActualJHeightEnergyBound
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual order-derivative large-q bound uniform on each compact imaginary
order interval. Native order analyticity proves continuity of the actual
initial J and q-jets and their actual order derivatives. Hence the explicit
forced-energy amplitude is continuous and genuinely bounded on compact t.
This consumes no critical-kernel or held small-q Mellin supplier.
-/

namespace ImbalancedChen.Part3.ActualJOrderDerivativeUniformLargeQ20261026b

noncomputable section
open Complex Set Filter
open scoped Topology
open ActualGeneralJBesselSourceOnly ActualJLocalOrderHolomorphic20261026a
open ActualJFirstOrderJet20261026b ActualJFirstMixedDerivative20261026b
open ActualJImaginaryRadialJet20261026b ActualJRadialEnergyDerivative20261026b
open ActualJLargeQEnergyBound20261026b ActualJHeightRadialForcing20261026b
open ActualJHeightEnergyBound20261026b

private theorem orderHalfPlane_open : IsOpen orderHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem generalJFirst_order_analyticAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : AnalyticAt ℂ (fun z : ℂ => generalJFirst z q) nu := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => generalJFirst z q) orderHalfPlane :=
    fun z hz => (generalJFirst_order_hasDerivAt hz hq).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (orderHalfPlane_open.mem_nhds hnu)

theorem actualJOrderDerivative_order_continuousAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : ContinuousAt (fun z : ℂ => actualJOrderDerivative z q) nu := by
  have hc := (generalJ_order_analyticAt hnu hq).deriv.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [orderHalfPlane_open.mem_nhds hnu] with z hz
  exact (generalJ_order_hasDerivAt hz hq).deriv.symm

theorem actualJFirstOrderDerivative_order_continuousAt {nu : ℂ} (hnu : nu ∈ orderHalfPlane)
    {q : ℝ} (hq : 0 < q) : ContinuousAt (fun z : ℂ => actualJFirstOrderDerivative z q) nu := by
  have hc := (generalJFirst_order_analyticAt hnu hq).deriv.continuousAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [orderHalfPlane_open.mem_nhds hnu] with z hz
  exact (generalJFirst_order_hasDerivAt hz hq).deriv.symm

private theorem imaginary_order_mem (t : ℝ) : 2 * I * (t : ℂ) ∈ orderHalfPlane := by
  simp [orderHalfPlane]

private theorem generalJ_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => generalJ (2 * I * (t : ℂ)) q) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (generalJ_order_hasDerivAt (imaginary_order_mem t) hq).continuousAt.comp (by fun_prop)

private theorem generalJFirst_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => generalJFirst (2 * I * (t : ℂ)) q) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (generalJFirst_order_hasDerivAt (imaginary_order_mem t) hq).continuousAt.comp (by fun_prop)

theorem heightOrderJ_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => heightOrderJ t q) := by
  have hd : Continuous (fun t : ℝ => actualJOrderDerivative (2 * I * (t : ℂ)) q) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (actualJOrderDerivative_order_continuousAt (imaginary_order_mem t) hq).comp (by fun_prop)
  exact continuous_const.mul hd

theorem heightOrderJFirst_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => heightOrderJFirst t q) := by
  have hd : Continuous (fun t : ℝ => actualJFirstOrderDerivative (2 * I * (t : ℂ)) q) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (actualJFirstOrderDerivative_order_continuousAt (imaginary_order_mem t) hq).comp (by fun_prop)
  exact continuous_const.mul hd

private theorem radialJ_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => radialJ t q) :=
  continuous_const.mul (generalJ_height_continuous hq)

private theorem radialJFirst_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => radialJFirst t q) :=
  (continuous_const.mul (generalJFirst_height_continuous hq)).add
    (continuous_const.mul (generalJ_height_continuous hq))

private theorem radialW_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => radialW t q) :=
  continuous_const.mul (heightOrderJ_height_continuous hq)

private theorem radialWFirst_height_continuous {q : ℝ} (hq : 0 < q) :
    Continuous (fun t : ℝ => radialWFirst t q) :=
  (continuous_const.mul (heightOrderJFirst_height_continuous hq)).add
    (continuous_const.mul (heightOrderJ_height_continuous hq))

private theorem radialPotential_height_continuous (q : ℝ) :
    Continuous (fun t : ℝ => radialPotential t q) := by
  unfold radialPotential radialCoefficient
  fun_prop

theorem largeQAmplitude_continuous : Continuous largeQAmplitude := by
  have hE : Continuous (fun t : ℝ => radialEnergy t 1) := by
    have h := ((radialJFirst_height_continuous (by norm_num : (0 : ℝ) < 1)).norm.pow 2).add
      ((radialPotential_height_continuous 1).mul
        ((radialJ_height_continuous (by norm_num : (0 : ℝ) < 1)).norm.pow 2))
    simpa only [radialEnergy, Complex.normSq_eq_norm_sq] using h
  exact hE.sqrt

theorem forcedRadialEnergy_initial_continuous : Continuous (fun t : ℝ => forcedRadialEnergy t 1) :=
  ((radialWFirst_height_continuous (by norm_num : (0 : ℝ) < 1)).norm.pow 2).add
    ((radialPotential_height_continuous 1).mul
      ((radialW_height_continuous (by norm_num : (0 : ℝ) < 1)).norm.pow 2))

/-- Continuity is derived from actual initial jets and native order
derivatives. No continuous-amplitude supplier is assumed. -/
theorem heightLargeQAmplitude_continuous : Continuous heightLargeQAmplitude := by
  have hK : Continuous forcingMass := by
    exact (continuous_const.mul continuous_abs).mul largeQAmplitude_continuous
  exact ((forcedRadialEnergy_initial_continuous.add continuous_const).sqrt).add hK

theorem exists_heightOrderJ_uniform_large_q_bound (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| ≤ T → ∀ q : ℝ, 1 ≤ q →
      ‖heightOrderJ t q‖ ≤ C / Real.sqrt q := by
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (-T) T))
    .exists_bound_of_continuousOn heightLargeQAmplitude_continuous.continuousOn
  refine ⟨|A| + 1, by positivity, ?_⟩
  intro t ht q hq
  have hb : heightLargeQAmplitude t ≤ |A| + 1 := by
    have h := hA t (abs_le.mp ht)
    rw [Real.norm_eq_abs] at h
    have hB := le_abs_self (heightLargeQAmplitude t)
    have hAA := le_abs_self A
    linarith
  exact (heightOrderJ_large_q_bound t hq).trans (div_le_div_of_nonneg_right hb (Real.sqrt_nonneg q))

/-- The actual literal t derivative, uniformly on compact real heights. -/
theorem exists_native_height_derivative_uniform_large_q_bound (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| ≤ T → ∀ q : ℝ, 1 ≤ q →
      ‖deriv (fun x : ℝ => generalJ (2 * I * (x : ℂ)) q) t‖ ≤ C / Real.sqrt q := by
  obtain ⟨C, hC, hb⟩ := exists_heightOrderJ_uniform_large_q_bound T
  refine ⟨C, hC, ?_⟩
  intro t ht q hq
  rw [(generalJ_height_hasDerivAt t (by linarith : 0 < q)).deriv]
  exact hb t ht q hq

theorem exists_actual_order_derivative_uniform_large_q_bound (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| ≤ T → ∀ q : ℝ, 1 ≤ q →
      ‖actualJOrderDerivative (2 * I * (t : ℂ)) q‖ ≤ C / Real.sqrt q := by
  obtain ⟨C, hC, hb⟩ := exists_heightOrderJ_uniform_large_q_bound T
  refine ⟨C, hC, ?_⟩
  intro t ht q hq
  have h := hb t ht q hq
  rw [heightOrderJ, norm_mul, norm_mul, Complex.norm_I, norm_ofNat, mul_one] at h
  nlinarith [norm_nonneg (actualJOrderDerivative (2 * I * (t : ℂ)) q)]

end
end ImbalancedChen.Part3.ActualJOrderDerivativeUniformLargeQ20261026b
