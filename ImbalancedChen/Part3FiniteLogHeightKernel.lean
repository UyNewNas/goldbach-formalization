import ImbalancedChen.Part3HeightScatteringWaveGram
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Finite log-height oscillatory boundary kernel, including its diagonal

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The kernel is the actual finite interval integral of exp(i*k*r).
Its divided-difference expression is only used for k != 0; its value at
k=0 is b-a, and continuity at zero is proved by parametric integration.
This is the local physical-wave boundary kernel, not an automorphic
Maass--Selberg theorem or an Eisenstein completeness assertion.
-/
namespace ImbalancedChen.Part3.FiniteLogHeightKernel20261026b
noncomputable section
open MeasureTheory Filter
open scoped Topology
open HeightScatteringWaveGram20261026b

def logBandKernel (a b k : ℝ) : ℂ :=
  ∫ r in a..b, planeWave k r

theorem planeWave_continuous (k : ℝ) : Continuous (planeWave k) := by
  unfold planeWave
  fun_prop

theorem planeWave_intervalIntegrable (a b k : ℝ) :
    IntervalIntegrable (planeWave k) volume a b :=
  (planeWave_continuous k).intervalIntegrable a b

@[simp] theorem logBandKernel_zero (a b : ℝ) :
    logBandKernel a b 0 = ((b - a : ℝ) : ℂ) := by
  simp [logBandKernel, planeWave]

@[simp] theorem logBandKernel_same_endpoints (a k : ℝ) :
    logBandKernel a a k = 0 := by simp [logBandKernel]

theorem logBandKernel_reverse_endpoints (a b k : ℝ) :
    logBandKernel b a k = -logBandKernel a b k := by
  exact intervalIntegral.integral_symm a b

/-- Exact boundary quotient away from the removable diagonal. -/
theorem logBandKernel_eq_boundary_quotient (a b : ℝ) {k : ℝ} (hk : k ≠ 0) :
    logBandKernel a b k =
      (planeWave k b - planeWave k a) / (Complex.I * (k : ℂ)) := by
  unfold logBandKernel planeWave
  exact intervalIntegral.integral_exp_mul_complex
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk))

/-- Continuity includes k=0, so the diagonal value is not a division by zero. -/
theorem logBandKernel_continuous (a b : ℝ) : Continuous (logBandKernel a b) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  change Continuous (fun p : ℝ × ℝ =>
    Complex.exp (Complex.I * (p.1 : ℂ) * (p.2 : ℂ)))
  fun_prop

theorem logBandKernel_tendsto_zero (a b : ℝ) :
    Tendsto (logBandKernel a b) (𝓝 0) (𝓝 ((b - a : ℝ) : ℂ)) := by
  simpa only [logBandKernel_zero] using
    ((logBandKernel_continuous a b).continuousAt :
      ContinuousAt (logBandKernel a b) 0)

/-- The two frequency combinations in the scattering Gram are both
continuous on the complete (t,u)-plane, including t=u and t=-u. -/
theorem logBandKernel_difference_continuous (a b : ℝ) :
    Continuous (fun p : ℝ × ℝ => logBandKernel a b (p.1 - p.2)) :=
  (logBandKernel_continuous a b).comp (continuous_fst.sub continuous_snd)

theorem logBandKernel_sum_continuous (a b : ℝ) :
    Continuous (fun p : ℝ × ℝ => logBandKernel a b (p.1 + p.2)) :=
  (logBandKernel_continuous a b).comp (continuous_fst.add continuous_snd)

end
end ImbalancedChen.Part3.FiniteLogHeightKernel20261026b


