import ImbalancedChen.P2OriginalChartDerivativeCore
import ImbalancedChen.P2SmoothLogFloorDerivativeCore
import ImbalancedChen.Part5OriginalH430ClassicalSmoothDyadicFamily
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Fixed real scalar factors used by the classical word. In an Euler chart
each logarithmic factor is affine. Each physical radial or floor factor
is a scalar smooth plateau of an affine logarithm. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds
noncomputable section
open Finset Set Filter Real Wu2008DoubleSieve
open P4B
open Part5OriginalH430ClassicalSmoothOuterWeight (floorGate thinGate radialGate)
open scoped Classical Topology BigOperators ContDiff


theorem step_bound {w : ℝ} (hw : 0<w) : ScalarBound (smoothGateUpperStep w) := by
  refine ⟨contDiff_smoothGateUpperStep _,?_⟩
  intro n
  obtain ⟨A,hA,H⟩ := exists_smoothGateUpperStep_derivative_budget n
  exact ⟨A/w^n,div_nonneg (zero_le_one.trans hA) (pow_nonneg hw.le n),H w hw⟩

private theorem log_upper_bound {w b : ℝ} (hw : 0<w) (hb : 0<b) :
    ScalarBound (fun u => smoothGateUpperStep w (b-exp u)) := by
  apply plateau_bound (l:=log b) (u:=log (b+w)) (v:=1) (w:=0)
  · exact (contDiff_smoothGateUpperStep _).comp (contDiff_const.sub contDiff_exp)
  · intro x
    rw [abs_of_nonneg (smoothGateUpperStep_nonneg _ _)]
    exact smoothGateUpperStep_le_one _ _
  · intro x hx
    apply smoothGateUpperStep_eq_one hw
    have h := exp_le_exp.mpr hx
    rw [exp_log hb] at h
    exact sub_nonneg.mpr h
  · intro x hx
    apply smoothGateUpperStep_eq_zero hw
    have h := exp_le_exp.mpr hx
    rw [exp_log (add_pos hb hw)] at h
    linarith only [h]

theorem log_thin_bound {c : ℝ} (hc : 0<c) : ScalarBound (fun u => thinGate c (exp u)) :=
  log_upper_bound (half_pos hc) (half_pos hc)

theorem log_radial_bound {h : ℝ} (hh : 0<h) : ScalarBound (fun u => radialGate h (exp u)) :=
  log_upper_bound hh zero_lt_one


end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds

