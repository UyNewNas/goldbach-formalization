import ImbalancedChen.Part3ActualHalfOrderKWronskian
import ImbalancedChen.Part3ActualKRadialLogConjugation
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Actual half-order radial Green kernel: homogeneous sides and unit jump

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
This uses the actual series I_half and the actual integral K_half. It
constructs their min/max kernel on r=log(q), proves its continuity, the
homogeneous equation away from the source, and the derivative jump -1.
The operator is exactly -d^2/dr^2+exp(2r)+1/4. No weak Green identity,
self-adjoint realization, full Maass spectrum or Kuznetsov formula is claimed.
-/

namespace ImbalancedChen.Part3.ActualHalfOrderRadialGreenSourceOnly

noncomputable section
open Set Filter
open scoped Topology
open RealOrderKExceptionalSourceOnly ModifiedHalfOrderISourceOnly
open ActualHalfOrderKWronskianSourceOnly ActualKRadialLogConjugation20261025a

def actualHalfKSecond (q : ℝ) : ℝ :=
  halfKNormalization *
    ((3 / 4 : ℝ) * q ^ (-5 / 2 : ℝ) * Real.exp (-q) +
      q ^ (-3 / 2 : ℝ) * Real.exp (-q) + q ^ (-1 / 2 : ℝ) * Real.exp (-q))

theorem actualHalfKFirst_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt actualHalfKFirst (actualHalfKSecond q) q := by
  have hexp := (hasDerivAt_id q).neg.exp
  have hleft := ((hasDerivAt_rpow_minus_three_halves hq).const_mul (-1 / 2 : ℝ)).mul hexp
  have hright := (hasDerivAt_rpow_minus_half hq).mul hexp
  have h := (hleft.sub hright).const_mul halfKNormalization
  convert h using 1 <;> dsimp [actualHalfKFirst, actualHalfKSecond] <;> ring

theorem deriv_realOrderK_half_hasDerivAt {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv (realOrderK (1 / 2 : ℝ))) (actualHalfKSecond q) q := by
  apply (actualHalfKFirst_hasDerivAt hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  exact (realOrderK_half_hasDerivAt hx).deriv

/-- The actual integral K_half obeys its ODE as a consequence of its
proved integral evaluation and two genuine derivatives. -/
theorem actual_halfK_modifiedBessel_equation {q : ℝ} (hq : 0 < q) :
    q ^ 2 * deriv (deriv (realOrderK (1 / 2 : ℝ))) q +
      q * deriv (realOrderK (1 / 2 : ℝ)) q -
      (q ^ 2 + (1 / 4 : ℝ)) * realOrderK (1 / 2 : ℝ) q = 0 := by
  rw [(deriv_realOrderK_half_hasDerivAt hq).deriv, (realOrderK_half_hasDerivAt hq).deriv,
    realOrderK_half_eq_rpow hq]
  dsimp only [actualHalfKSecond, actualHalfKFirst]
  rw [rpow_minus_three_halves_eq hq, rpow_minus_five_halves_eq hq]
  field_simp [hq.ne']
  <;> ring

def radialHalfI : ℝ → ℝ := logPull modifiedHalfI
def radialHalfK : ℝ → ℝ := logPull (realOrderK (1 / 2 : ℝ))

def halfRadialOperator (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  -deriv (deriv F) r + (Real.exp (2 * r) + (1 / 4 : ℝ)) * F r

private theorem halfI_differentiableOn : DifferentiableOn ℝ modifiedHalfI (Ioi (0 : ℝ)) := by
  intro q hq
  exact (modifiedHalfI_hasDerivAt hq).differentiableAt.differentiableWithinAt

private theorem halfI_deriv_differentiableOn :
    DifferentiableOn ℝ (deriv modifiedHalfI) (Ioi (0 : ℝ)) := by
  intro q hq
  exact (deriv_modifiedHalfI_hasDerivAt hq).differentiableAt.differentiableWithinAt

private theorem halfK_differentiableOn :
    DifferentiableOn ℝ (realOrderK (1 / 2 : ℝ)) (Ioi (0 : ℝ)) := by
  intro q hq
  exact (realOrderK_half_hasDerivAt hq).differentiableAt.differentiableWithinAt

private theorem halfK_deriv_differentiableOn :
    DifferentiableOn ℝ (deriv (realOrderK (1 / 2 : ℝ))) (Ioi (0 : ℝ)) := by
  intro q hq
  exact (deriv_realOrderK_half_hasDerivAt hq).differentiableAt.differentiableWithinAt

theorem radialHalfI_hasDerivAt (r : ℝ) :
    HasDerivAt radialHalfI (Real.exp r * deriv modifiedHalfI (Real.exp r)) r := by
  simpa only [radialHalfI, smul_eq_mul] using
    logPull_hasDerivAt modifiedHalfI halfI_differentiableOn r

theorem radialHalfK_hasDerivAt (r : ℝ) :
    HasDerivAt radialHalfK
      (Real.exp r * deriv (realOrderK (1 / 2 : ℝ)) (Real.exp r)) r := by
  simpa only [radialHalfK, smul_eq_mul] using
    logPull_hasDerivAt (realOrderK (1 / 2 : ℝ)) halfK_differentiableOn r

private theorem exp_two_mul_eq_square (r : ℝ) : Real.exp (2 * r) = (Real.exp r) ^ 2 := by
  rw [show 2 * r = r + r by ring, Real.exp_add, pow_two]

theorem halfRadialOperator_radialHalfI (r : ℝ) : halfRadialOperator radialHalfI r = 0 := by
  unfold halfRadialOperator radialHalfI
  rw [logPull_second_deriv modifiedHalfI halfI_differentiableOn halfI_deriv_differentiableOn r,
    exp_two_mul_eq_square]
  simp only [smul_eq_mul, logPull]
  have h := modifiedHalfI_modifiedBessel_equation (Real.exp_pos r)
  linear_combination -h

theorem halfRadialOperator_radialHalfK (r : ℝ) : halfRadialOperator radialHalfK r = 0 := by
  unfold halfRadialOperator radialHalfK
  rw [logPull_second_deriv (realOrderK (1 / 2 : ℝ))
    halfK_differentiableOn halfK_deriv_differentiableOn r, exp_two_mul_eq_square]
  simp only [smul_eq_mul, logPull]
  have h := actual_halfK_modifiedBessel_equation (Real.exp_pos r)
  linear_combination -h

/-- The genuine min/max kernel in logarithmic radial coordinates. -/
def actualHalfRadialGreen (s r : ℝ) : ℝ := radialHalfI (min r s) * radialHalfK (max r s)

theorem actualHalfRadialGreen_eq_left {r s : ℝ} (h : r ≤ s) :
    actualHalfRadialGreen s r = radialHalfI r * radialHalfK s := by
  simp only [actualHalfRadialGreen, min_eq_left h, max_eq_right h]

theorem actualHalfRadialGreen_eq_right {r s : ℝ} (h : s ≤ r) :
    actualHalfRadialGreen s r = radialHalfI s * radialHalfK r := by
  simp only [actualHalfRadialGreen, min_eq_right h, max_eq_left h]

theorem actualHalfRadialGreen_continuous (s : ℝ) : Continuous (actualHalfRadialGreen s) := by
  have hI : Continuous radialHalfI :=
    (show Differentiable ℝ radialHalfI from fun r => (radialHalfI_hasDerivAt r).differentiableAt).continuous
  have hK : Continuous radialHalfK :=
    (show Differentiable ℝ radialHalfK from fun r => (radialHalfK_hasDerivAt r).differentiableAt).continuous
  exact (hI.comp (continuous_id.min continuous_const)).mul
    (hK.comp (continuous_id.max continuous_const))

private theorem halfRadialOperator_congr_of_eventuallyEq
    {F G : ℝ → ℝ} {r : ℝ} (h : F =ᶠ[𝓝 r] G) :
    halfRadialOperator F r = halfRadialOperator G r := by
  unfold halfRadialOperator
  rw [h.deriv.deriv_eq, h.eq_of_nhds]

private theorem halfRadialOperator_mul_const (F : ℝ → ℝ) (c r : ℝ) :
    halfRadialOperator (fun x => F x * c) r = halfRadialOperator F r * c := by
  simp only [halfRadialOperator, deriv_mul_const_field']
  ring

private theorem halfRadialOperator_const_mul (F : ℝ → ℝ) (c r : ℝ) :
    halfRadialOperator (fun x => c * F x) r = c * halfRadialOperator F r := by
  simp only [halfRadialOperator, deriv_const_mul_field']
  ring

/-- Genuine homogeneous equation on the left open side of the source. -/
theorem actualHalfRadialGreen_homogeneous_left {r s : ℝ} (hrs : r < s) :
    halfRadialOperator (actualHalfRadialGreen s) r = 0 := by
  have heq : actualHalfRadialGreen s =ᶠ[𝓝 r] fun x => radialHalfI x * radialHalfK s := by
    filter_upwards [Iio_mem_nhds hrs] with x hx
    exact actualHalfRadialGreen_eq_left hx.le
  rw [halfRadialOperator_congr_of_eventuallyEq heq, halfRadialOperator_mul_const,
    halfRadialOperator_radialHalfI, zero_mul]

/-- Genuine homogeneous equation on the right open side of the source. -/
theorem actualHalfRadialGreen_homogeneous_right {r s : ℝ} (hsr : s < r) :
    halfRadialOperator (actualHalfRadialGreen s) r = 0 := by
  have heq : actualHalfRadialGreen s =ᶠ[𝓝 r] fun x => radialHalfI s * radialHalfK x := by
    filter_upwards [Ioi_mem_nhds hsr] with x hx
    exact actualHalfRadialGreen_eq_right hx.le
  rw [halfRadialOperator_congr_of_eventuallyEq heq, halfRadialOperator_const_mul,
    halfRadialOperator_radialHalfK, mul_zero]

theorem actualHalfRadialGreen_hasDerivWithinAt_left (s : ℝ) :
    HasDerivWithinAt (actualHalfRadialGreen s)
      ((Real.exp s * deriv modifiedHalfI (Real.exp s)) * radialHalfK s) (Iic s) s := by
  apply ((radialHalfI_hasDerivAt s).mul_const (radialHalfK s)).hasDerivWithinAt.congr
  · intro r hr
    exact actualHalfRadialGreen_eq_left hr
  · exact actualHalfRadialGreen_eq_left le_rfl

theorem actualHalfRadialGreen_hasDerivWithinAt_right (s : ℝ) :
    HasDerivWithinAt (actualHalfRadialGreen s)
      (radialHalfI s * (Real.exp s * deriv (realOrderK (1 / 2 : ℝ)) (Real.exp s))) (Ici s) s := by
  apply ((radialHalfK_hasDerivAt s).const_mul (radialHalfI s)).hasDerivWithinAt.congr
  · intro r hr
    exact actualHalfRadialGreen_eq_right hr
  · exact actualHalfRadialGreen_eq_right le_rfl

/-- The actual one-sided derivative jump is exactly -1. Together with
the two homogeneous equations and continuity, this is the local Green
normalization for the literal operator -d²/dr²+exp(2r)+1/4. -/
theorem actualHalfRadialGreen_derivative_jump (s : ℝ) :
    derivWithin (actualHalfRadialGreen s) (Ici s) s -
      derivWithin (actualHalfRadialGreen s) (Iic s) s = -1 := by
  rw [(actualHalfRadialGreen_hasDerivWithinAt_right s).derivWithin (uniqueDiffWithinAt_Ici s),
    (actualHalfRadialGreen_hasDerivWithinAt_left s).derivWithin (uniqueDiffWithinAt_Iic s)]
  calc
    radialHalfI s * (Real.exp s * deriv (realOrderK (1 / 2 : ℝ)) (Real.exp s)) -
        (Real.exp s * deriv modifiedHalfI (Real.exp s)) * radialHalfK s =
        Real.exp s *
          (modifiedHalfI (Real.exp s) * deriv (realOrderK (1 / 2 : ℝ)) (Real.exp s) -
            deriv modifiedHalfI (Real.exp s) * realOrderK (1 / 2 : ℝ) (Real.exp s)) := by
      dsimp only [radialHalfI, radialHalfK, logPull]
      ring
    _ = Real.exp s * (-1 / Real.exp s) := by
      rw [actual_halfOrder_IK_wronskian (Real.exp_pos s)]
    _ = -1 := by field_simp [Real.exp_ne_zero s]

end

end ImbalancedChen.Part3.ActualHalfOrderRadialGreenSourceOnly
