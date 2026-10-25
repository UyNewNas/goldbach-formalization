import ImbalancedChen.Part3GeneralActualRadialGreen
import ImbalancedChen.Part3ActualImaginaryKIConnection

/-!
# The pointwise jump of the actual logarithmic Green kernel

The subtraction convention is G_(epsilon-i*tau) - G_(epsilon+i*tau).
Its boundary is +2*i*sinh(pi*tau)/pi times the product of the two actual
K_(i*tau) functions. The proof uses the literal integral's order symmetry,
the proved imaginary-order K/I connection, and actual order continuity.
No resolvent, spectral measure, Stone formula, or Plancherel identity is
assumed. This module proves pointwise boundary limits only.

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

noncomputable section
open scoped Topology
open Set Filter MeasureTheory

namespace ImbalancedChen.Part3.ActualGreenResolventJumpSourceOnly

open GeneralActualRadialGreenSourceOnly ComplexCompactGreenGluingSourceOnly
open ComplexOrderKRadialRegularitySourceOnly ComplexOrderKBridgeSourceOnly
open ComplexOrderKHolomorphicSourceOnly GeneralComplexISeriesSourceOnly
open GeneralIOrderHolomorphySourceOnly ActualImaginaryKIConnectionSourceOnly

/-- The literal cosh integral is even in its full complex order. -/
theorem complexOrderK_neg_order (nu : ℂ) (q : ℝ) :
    complexOrderK (-nu) q = complexOrderK nu q := by
  unfold complexOrderK
  apply integral_congr_ae
  exact Eventually.of_forall (fun u => by
    simp only [complexOrderIntegrand, neg_mul, Complex.cosh_neg])

theorem actualRadialGreen_continuousAt_order {nu : ℂ}
    (hre : nu.re = 0) (s r : ℝ) :
    ContinuousAt (fun z : ℂ => actualRadialGreen z s r) nu := by
  have hi := (analyticAt_generalI_order nu (by rw [hre]; norm_num)
    (Real.exp_pos (min r s))).continuousAt
  have hk := (complexOrderK_hasDerivAt nu (Real.exp (max r s))
    (Real.exp_pos _) (by rw [hre]; norm_num)).continuousAt
  exact hi.mul hk

/-- The actual outgoing boundary value along the positive-real order path. -/
theorem actualRadialGreen_tendsto_positive_translate {nu : ℂ}
    (hre : nu.re = 0) (s r : ℝ) :
    Tendsto (fun eps : ℝ => actualRadialGreen ((eps : ℂ) + nu) s r)
      (𝓝[>] 0) (𝓝 (actualRadialGreen nu s r)) :=
  (actualRadialGreen_continuousAt_order hre s r).tendsto.comp
    (tendsto_positive_real_translate nu)

private theorem generalI_order_difference {nu : ℂ}
    (hre : nu.re = 0) (him : nu.im ≠ 0) {q : ℝ} (hq : 0 < q) :
    generalI (-nu) q - generalI nu q =
      (2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ)) *
        complexOrderK nu q := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs := sin_pi_mul_ne_zero_of_im_ne_zero him
  rw [complexOrderK_eq_generalI_sub_of_re_zero hre him hq]
  field_simp [hp, hs]
  <;> ring

/-- The sign is fixed by the explicit order of subtraction: minus order
minus plus order. This statement uses actual Green and actual K definitions. -/
theorem actualRadialGreen_boundary_jump {nu : ℂ}
    (hre : nu.re = 0) (him : nu.im ≠ 0) (s r : ℝ) :
    actualRadialGreen (-nu) s r - actualRadialGreen nu s r =
      (2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ)) *
        complexOrderK nu (Real.exp r) * complexOrderK nu (Real.exp s) := by
  unfold actualRadialGreen kernel radialI radialK
  rw [complexOrderK_neg_order]
  calc
    _ = (generalI (-nu) (Real.exp (min r s)) - generalI nu (Real.exp (min r s))) *
        complexOrderK nu (Real.exp (max r s)) := by ring
    _ = ((2 * Complex.sin ((Real.pi : ℂ) * nu) / (Real.pi : ℂ)) *
        complexOrderK nu (Real.exp (min r s))) *
        complexOrderK nu (Real.exp (max r s)) := by
      rw [generalI_order_difference hre him (Real.exp_pos _)]
    _ = _ := by
      rcases le_total r s with hrs | hsr
      · rw [min_eq_left hrs, max_eq_right hrs]
      · rw [min_eq_right hsr, max_eq_left hsr]
        ring

/-- Hyperbolic normalization, including the zero-order value. -/
theorem actualRadialGreen_boundary_jump_sinh (tau s r : ℝ) :
    actualRadialGreen (-((tau : ℂ) * Complex.I)) s r -
        actualRadialGreen ((tau : ℂ) * Complex.I) s r =
      (2 * (Real.sinh (Real.pi * tau) : ℂ) * Complex.I / (Real.pi : ℂ)) *
        complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r) *
        complexOrderK ((tau : ℂ) * Complex.I) (Real.exp s) := by
  by_cases htau : tau = 0
  · subst tau
    simp
  rw [actualRadialGreen_boundary_jump (by simp) (by simpa using htau)]
  have hphase : (Real.pi : ℂ) * ((tau : ℂ) * Complex.I) =
      ((Real.pi * tau : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hphase, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  ring

/-- The genuine two-sided order boundary jump of the actual kernel,
obtained along epsilon +/- i*tau with epsilon tending to zero positively. -/
theorem actualRadialGreen_resolvent_jump_tendsto (tau s r : ℝ) :
    Tendsto (fun eps : ℝ =>
      actualRadialGreen ((eps : ℂ) - (tau : ℂ) * Complex.I) s r -
        actualRadialGreen ((eps : ℂ) + (tau : ℂ) * Complex.I) s r)
      (𝓝[>] 0)
      (𝓝 ((2 * (Real.sinh (Real.pi * tau) : ℂ) * Complex.I / (Real.pi : ℂ)) *
        complexOrderK ((tau : ℂ) * Complex.I) (Real.exp r) *
        complexOrderK ((tau : ℂ) * Complex.I) (Real.exp s))) := by
  have hm := actualRadialGreen_tendsto_positive_translate
    (nu := -((tau : ℂ) * Complex.I)) (by simp) s r
  have hp := actualRadialGreen_tendsto_positive_translate
    (nu := (tau : ℂ) * Complex.I) (by simp) s r
  have h := hm.sub hp
  rw [actualRadialGreen_boundary_jump_sinh] at h
  simpa only [sub_eq_add_neg] using h

end ImbalancedChen.Part3.ActualGreenResolventJumpSourceOnly
