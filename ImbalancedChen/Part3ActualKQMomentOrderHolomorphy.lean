import ImbalancedChen.Part3ComplexOrderKShiftDerivative
import ImbalancedChen.Part3ComplexOrderKEntire

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

The literal q-moment integral at EVERY spatial derivative order is entire
in the complex K order. The adjacent-order identity is proved at the
actual integrand, integrated using the already proved absolute moment
integrability, then iterated from the actual entire K integral. Its
complex order derivative obeys the differentiated exact shift recurrence.
This supplies the missing parameter holomorphy of actual spatial q jets,
without assuming mixed derivative commutation or an evaluated coefficient.
-/

namespace ImbalancedChen.Part3.ActualKQMomentOrderHolomorphy20261026b
noncomputable section
open Set Complex MeasureTheory Filter
open ComplexOrderKQCalculus ComplexOrderKShiftDerivativeSourceOnly
open ComplexOrderKEntire20261025a

/-- Every q-jet has the same true adjacent-order recurrence at its
integrand; the power of -cosh is retained exactly. -/
theorem qMomentIntegrand_succ_adjacent (k : ℕ) (nu : ℂ) (q u : ℝ) :
    qMomentIntegrand (k + 1) nu q u = (-1 / 2 : ℂ) *
      (qMomentIntegrand k (nu - 1) q u + qMomentIntegrand k (nu + 1) q u) := by
  calc
    _ = (-(Real.cosh u : ℂ)) ^ k * qMomentIntegrand 1 nu q u := by
      simp only [qMomentIntegrand, pow_succ, pow_one]
      ring
    _ = _ := by
      rw [firstMomentIntegrand_eq_adjacent nu q u]
      simp only [qMomentIntegrand, pow_zero, one_mul]
      ring

/-- The recurrence is for the ACTUAL absolutely integrable q moments. -/
theorem qMoment_succ_adjacent (k : ℕ) (nu : ℂ) {q : ℝ} (hq : 0 < q) :
    qMoment (k + 1) nu q = (-1 / 2 : ℂ) *
      (qMoment k (nu - 1) q + qMoment k (nu + 1) q) := by
  unfold qMoment
  simp_rw [qMomentIntegrand_succ_adjacent]
  rw [integral_const_mul, integral_add
    (qMomentIntegrand_integrable k (nu - 1) hq) (qMomentIntegrand_integrable k (nu + 1) hq)]

/-- Entire order dependence of every actual spatial q jet. -/
theorem qMoment_order_differentiable (k : ℕ) {q : ℝ} (hq : 0 < q) :
    Differentiable ℂ (fun nu : ℂ => qMoment k nu q) := by
  induction k with
  | zero =>
      simpa only [qMoment_zero] using complexOrderK_differentiable_all hq
  | succ k ih =>
      have he : (fun nu : ℂ => qMoment (k + 1) nu q) =
          (fun nu : ℂ => (-1 / 2 : ℂ) * (qMoment k (nu - 1) q + qMoment k (nu + 1) q)) :=
        funext (fun nu => qMoment_succ_adjacent k nu hq)
      rw [he]
      exact ((ih.comp (differentiable_id.sub_const 1)).add
        (ih.comp (differentiable_id.add_const 1))).const_mul (-1 / 2 : ℂ)

theorem qMoment_order_analyticAt (k : ℕ) {q : ℝ} (hq : 0 < q) (nu : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => qMoment k w q) nu :=
  (qMoment_order_differentiable k hq).analyticAt nu

/-- The true parameter derivative of a spatial jet, with both shifted
orders retained. No q/order interchange is used to prove this identity. -/
theorem qMoment_order_deriv_succ_adjacent (k : ℕ) {q : ℝ} (hq : 0 < q) (nu : ℂ) :
    deriv (fun w : ℂ => qMoment (k + 1) w q) nu = (-1 / 2 : ℂ) *
      (deriv (fun w : ℂ => qMoment k w q) (nu - 1) +
        deriv (fun w : ℂ => qMoment k w q) (nu + 1)) := by
  have hm := ((qMoment_order_differentiable k hq) (nu - 1)).hasDerivAt.comp nu
    ((hasDerivAt_id nu).sub_const 1)
  have hp := ((qMoment_order_differentiable k hq) (nu + 1)).hasDerivAt.comp nu
    ((hasDerivAt_id nu).add_const 1)
  have h := (hm.add hp).const_mul (-1 / 2 : ℂ)
  have he : (fun w : ℂ => qMoment (k + 1) w q) =ᶠ[𝓝 nu]
      (fun w : ℂ => (-1 / 2 : ℂ) * (qMoment k (w - 1) q + qMoment k (w + 1) q)) :=
    Filter.Eventually.of_forall (fun w => qMoment_succ_adjacent k w hq)
  simpa only [mul_one] using (h.congr_of_eventuallyEq he).deriv

end
end ImbalancedChen.Part3.ActualKQMomentOrderHolomorphy20261026b
