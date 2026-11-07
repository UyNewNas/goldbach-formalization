import ImbalancedChen.Part3ActualCompletedConstantMixedDerivative

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The ACTUAL completed Fourier Eisenstein function has honest parameter/x
and parameter/y mixed derivatives at every positive height and s!=0,1,
including 1/2. The nonconstant part uses the proved derivative-series
exchange, both frequency signs, and the literal sqrt-height weight; the
constant uses its true central divided difference. All named spatial
jets below are identified with actual derivatives of the original field.
-/

namespace ImbalancedChen.Part3.ActualCompletedFourierParameterMixedJets20261026b
noncomputable section
open Set Complex Filter Topology
open CompletedEisensteinReflection20261025a CompletedEisensteinSpatialMaass
open CompletedEisensteinMeromorphic20261025a ContinuedFourierNonconstantMaass
open ContinuedFourierMomentSeriesCalculus ActualSpatialJetParameterSeries20261026b
open ActualFourierParameterSpatialCommutation20261026b
open ActualCompletedConstantParameterJets20261026b ActualCompletedConstantMixedDerivative20261026b

def completedParameter (s : ℂ) (y x : ℝ) : ℂ :=
  deriv (fun w : ℂ => completedEisensteinFourier w y x) s

def completedParameterX (s : ℂ) (y x : ℝ) : ℂ :=
  2 * root0 y * signedParameterSum 1 0 s y x

def completedParameterY (s : ℂ) (y x : ℝ) : ℂ :=
  deriv (fun w : ℂ => completedFirst w y) s +
    (2 * root1 y * signedParameterSum 0 0 s y x + 2 * root0 y * signedParameterSum 0 1 s y x)

theorem weightedKernel_parameter_hasDerivAt (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => weightedKernel w y x)
      (2 * root0 y * signedParameterSum 0 0 s y x) s := by
  have he : (fun w : ℂ => weightedKernel w y x) =
      (fun w : ℂ => 2 * root0 y * signedMomentSum 0 0 w y x) := by
    funext w
    rw [weightedKernel, root0_eq_sqrt, signedMomentSum_zero_zero_eq_actual w y x hy]
  rw [he]
  exact (signedMomentSum_hasDerivAt_parameter 0 0 s y x hy).const_mul (2 * root0 y)

theorem completedParameter_eq (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    completedParameter s y x = deriv (fun w : ℂ => completedConstant y w) s +
      2 * root0 y * signedParameterSum 0 0 s y x := by
  exact ((completedConstant_parameter_differentiableAt hs0 hs1 hy).hasDerivAt.add
    (weightedKernel_parameter_hasDerivAt s y x hy)).deriv

theorem completedFourier_hasDerivAt_x (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedEisensteinFourier s y t) (weightedKernelX s y x) x :=
  (weightedKernel_hasDerivAt_x s y x hy).const_add (completedConstant y s)

theorem completedFourierX_parameter_hasDerivAt (s : ℂ) (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => weightedKernelX w y x) (completedParameterX s y x) s := by
  simpa only [weightedKernelX, completedParameterX, root0_eq_sqrt] using
    (signedMomentSum_hasDerivAt_parameter 1 0 s y x hy).const_mul (2 * root0 y)

theorem completedFourierY_parameter_hasDerivAt (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun w : ℂ => completedFourierY w y x) (completedParameterY s y x) s := by
  exact (completedFirst_parameter_differentiableAt hs0 hs1 hy).hasDerivAt.add
    (((signedMomentSum_hasDerivAt_parameter 0 0 s y x hy).const_mul (2 * root1 y)).add
      ((signedMomentSum_hasDerivAt_parameter 0 1 s y x hy).const_mul (2 * root0 y)))

theorem completedParameter_hasDerivAt_x (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedParameter s y t) (completedParameterX s y x) x := by
  have he : (fun t : ℝ => completedParameter s y t) =
      (fun t : ℝ => deriv (fun w : ℂ => completedConstant y w) s +
        2 * root0 y * signedParameterSum 0 0 s y t) :=
    funext (fun t => completedParameter_eq s hs0 hs1 y t hy)
  rw [he]
  exact ((signedParameterSum_hasDerivAt_x 0 0 s y x hy).const_mul (2 * root0 y)).const_add _

theorem completedParameter_hasDerivAt_y (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => completedParameter s t x) (completedParameterY s y x) y := by
  have he : (fun t : ℝ => completedParameter s t x) =ᶠ[𝓝 y]
      (fun t : ℝ => deriv (fun w : ℂ => completedConstant t w) s +
        2 * root0 t * signedParameterSum 0 0 s t x) := by
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact completedParameter_eq s hs0 hs1 t x ht
  have h := (completedConstant_parameter_hasDerivAt_y s hs0 hs1 hy).add
    (((root0_hasDerivAt hy).const_mul (2 : ℂ)).mul
      (signedParameterSum_hasDerivAt_y 0 0 s y x hy))
  exact h.congr_of_eventuallyEq he

/-- The original horizontal derivative functional is used on the right. -/
theorem completedFourier_parameter_x_commute (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => completedEisensteinFourier w y t) s) x =
      deriv (fun w : ℂ => deriv (fun t : ℝ => completedEisensteinFourier w y t) x) s := by
  have he : (fun w : ℂ => deriv (fun t : ℝ => completedEisensteinFourier w y t) x) =
      (fun w : ℂ => weightedKernelX w y x) :=
    funext (fun w => (completedFourier_hasDerivAt_x w y x hy).deriv)
  rw [he, (completedFourierX_parameter_hasDerivAt s y x hy).deriv]
  exact (completedParameter_hasDerivAt_x s hs0 hs1 y x hy).deriv

/-- The original vertical derivative functional is used on the right. -/
theorem completedFourier_parameter_y_commute (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (y x : ℝ) (hy : 0 < y) :
    deriv (fun t : ℝ => deriv (fun w : ℂ => completedEisensteinFourier w t x) s) y =
      deriv (fun w : ℂ => deriv (fun t : ℝ => completedEisensteinFourier w t x) y) s := by
  have he : (fun w : ℂ => deriv (fun t : ℝ => completedEisensteinFourier w t x) y) =ᶠ[𝓝 s]
      (fun w : ℂ => completedFourierY w y x) := by
    filter_upwards [(isOpen_ne continuous_id continuous_const).mem_nhds hs0,
      (isOpen_ne continuous_id continuous_const).mem_nhds hs1] with w hw0 hw1
    exact (completedFourier_hasDerivAt_y w hw0 hw1 y x hy).deriv
  rw [he.deriv_eq, (completedFourierY_parameter_hasDerivAt s hs0 hs1 y x hy).deriv]
  exact (completedParameter_hasDerivAt_y s hs0 hs1 y x hy).deriv

end
end ImbalancedChen.Part3.ActualCompletedFourierParameterMixedJets20261026b
