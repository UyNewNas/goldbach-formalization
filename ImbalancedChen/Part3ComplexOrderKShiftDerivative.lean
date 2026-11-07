import ImbalancedChen.Part3ComplexOrderKQCalculus

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The actual complex-order K integral has an exact shifted-order derivative
recurrence. This is derived from the cosh addition identity and proved
moment integrability, with no connection formula or asymptotic premise.
-/
namespace ImbalancedChen.Part3.ComplexOrderKShiftDerivativeSourceOnly
noncomputable section
open Set MeasureTheory
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus

theorem actual_K_even_order (nu : ℂ) (q : ℝ) :
    complexOrderK (-nu) q = complexOrderK nu q := by
  unfold complexOrderK
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => by
    simp only [complexOrderIntegrand, neg_mul, Complex.cosh_neg])

/-- The derivative integrand is the negative mean of the adjacent orders. -/
theorem firstMomentIntegrand_eq_adjacent (nu : ℂ) (q u : ℝ) :
    qMomentIntegrand 1 nu q u = (-1 / 2 : ℂ) *
      (qMomentIntegrand 0 (nu - 1) q u + qMomentIntegrand 0 (nu + 1) q u) := by
  have hm : (nu - 1) * (u : ℂ) = nu * (u : ℂ) - (u : ℂ) := by ring
  have hp : (nu + 1) * (u : ℂ) = nu * (u : ℂ) + (u : ℂ) := by ring
  simp only [qMomentIntegrand, pow_one, pow_zero, one_mul, hm, hp,
    Complex.cosh_sub, Complex.cosh_add, ← Complex.ofReal_cosh]
  ring

/-- Every complex order is allowed; q>0 supplies the genuine absolute
integrability of both adjacent-order Laplace integrals. -/
theorem actual_K_derivative_eq_adjacent (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    deriv (complexOrderK nu) q = (-1 / 2 : ℂ) *
      (complexOrderK (nu - 1) q + complexOrderK (nu + 1) q) := by
  rw [(complexOrderK_hasDerivAt_q nu hq).deriv,
    ← qMoment_zero (nu - 1) q, ← qMoment_zero (nu + 1) q]
  unfold qMoment
  calc
    _ = ∫ u in Ioi (0 : ℝ), (-1 / 2 : ℂ) *
        (qMomentIntegrand 0 (nu - 1) q u + qMomentIntegrand 0 (nu + 1) q u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (firstMomentIntegrand_eq_adjacent nu q)
    _ = _ := by
      rw [integral_const_mul,
        integral_add (qMomentIntegrand_integrable 0 (nu - 1) hq)
          (qMomentIntegrand_integrable 0 (nu + 1) hq)]

/-- In the strip 0<Re nu<1 the lower shifted order is reflected into the
positive-real-part range of the actual small-argument supplier. -/
theorem actual_K_derivative_eq_positive_adjacent (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    deriv (complexOrderK nu) q = (-1 / 2 : ℂ) *
      (complexOrderK (1 - nu) q + complexOrderK (nu + 1) q) := by
  rw [actual_K_derivative_eq_adjacent nu hq]
  have he : complexOrderK (nu - 1) q = complexOrderK (1 - nu) q := by
    rw [show nu - 1 = -(1 - nu) by ring, actual_K_even_order]
  rw [he]

end
end ImbalancedChen.Part3.ComplexOrderKShiftDerivativeSourceOnly
