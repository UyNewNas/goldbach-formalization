import ImbalancedChen.Part3Gamma0ActualHeatScalarCoefficient
import ImbalancedChen.Part3HeatFactorialScalarBound
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

All scalar heat moments of the ACTUAL Gamma0 unbounded scalar measure
are integrable at positive time, and M_m'(t)=-M_(m+1)(t). Genuine local
dominated differentiation uses the independently proved pure factorial
exponential bound and the finite actual measure, with no operator-domain
assumption on the physical vector and no moment/derivative supplier.

Native iteratedDeriv of the actual heat coefficient is (-1)^m M_m.
Consequently every alternating derivative is nonnegative: true complete
monotonicity on positive times. All moments and the actual coefficient
are also proved C-infinity there by finite-order derivative recursion.
No operator-power domain, heat-kernel, or spectral normalization claim
is substituted for these genuine scalar statements.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHeatCompleteMonotonicity20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0ActualUnboundedScalarMeasure20261025a
open Gamma0ActualHeatScalarCoefficient20261025a
open HeatFactorialScalarBound20261025a

def actualHeatMoment (N : ℕ) [NeZero N] (f : QuotientL2 N) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ lambda : ℝ, lambda^m*Real.exp (-t*lambda) ∂actualLaplaceMeasure N f

theorem actualHeatMoment_nonneg (N : ℕ) [NeZero N] (f : QuotientL2 N) (m : ℕ) (t : ℝ) :
    0≤actualHeatMoment N f m t := by
  apply integral_nonneg_of_ae
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  exact mul_nonneg (pow_nonneg hl m) (Real.exp_pos _).le

theorem actualHeatMoment_kernel_integrable (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) {t : ℝ} (ht : 0<t) :
    Integrable (fun lambda : ℝ => lambda^m*Real.exp (-t*lambda)) (actualLaplaceMeasure N f) := by
  apply (integrable_const ((m.factorial : ℝ)/t^m)).mono'
    (show AEStronglyMeasurable (fun lambda : ℝ => lambda^m*Real.exp (-t*lambda))
      (actualLaplaceMeasure N f) from
        (show Continuous (fun lambda : ℝ => lambda^m*Real.exp (-t*lambda)) by fun_prop).aestronglyMeasurable)
  filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hl m) (Real.exp_pos _).le)]
  exact pow_mul_exp_neg_mul_le_factorial_div_pow ht hl m

private theorem moment_local_derivative_bound (m : ℕ) {t s lambda : ℝ}
    (ht : 0<t) (hs : t/2<s) (hl : 0≤lambda) :
    ‖-(lambda^(m+1))*Real.exp (-s*lambda)‖ ≤
      ((m+1).factorial : ℝ)/(t/2)^(m+1) := by
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (pow_nonneg hl (m+1)),
    abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ lambda^(m+1)*Real.exp (-(t/2)*lambda) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl (m+1))
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hs.le hl]
    _ ≤ _ := pow_mul_exp_neg_mul_le_factorial_div_pow (half_pos ht) hl (m+1)

/-- The all-orders genuine moment recursion, with a derived local
integrable derivative bound and no actual unbounded-domain hypothesis. -/
theorem actualHeatMoment_hasDerivAt (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) {t : ℝ} (ht : 0<t) :
    HasDerivAt (actualHeatMoment N f m) (-actualHeatMoment N f (m+1) t) t := by
  have hs : Ioi (t/2) ∈ 𝓝 t := isOpen_Ioi.mem_nhds (by dsimp; linarith)
  have hmeas : ∀ᶠ s : ℝ in 𝓝 t, AEStronglyMeasurable
      (fun lambda : ℝ => lambda^m*Real.exp (-s*lambda)) (actualLaplaceMeasure N f) :=
    Eventually.of_forall fun s =>
      (show Continuous (fun lambda : ℝ => lambda^m*Real.exp (-s*lambda)) by fun_prop).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun lambda : ℝ => -(lambda^(m+1))*Real.exp (-t*lambda)) (actualLaplaceMeasure N f) :=
    (show Continuous (fun lambda : ℝ => -(lambda^(m+1))*Real.exp (-t*lambda)) by fun_prop)
      .aestronglyMeasurable
  have hbound : ∀ᵐ lambda ∂actualLaplaceMeasure N f, ∀ s ∈ Ioi (t/2),
      ‖-(lambda^(m+1))*Real.exp (-s*lambda)‖ ≤
        ((m+1).factorial : ℝ)/(t/2)^(m+1) := by
    filter_upwards [actualLaplaceMeasure_nonnegative_ae N f] with lambda hl
    intro s hs
    exact moment_local_derivative_bound m ht hs hl
  have hdiff : ∀ᵐ lambda ∂actualLaplaceMeasure N f, ∀ s ∈ Ioi (t/2),
      HasDerivAt (fun x : ℝ => lambda^m*Real.exp (-x*lambda))
        (-(lambda^(m+1))*Real.exp (-s*lambda)) s :=
    Eventually.of_forall fun lambda s _ => by
      convert ((((hasDerivAt_id s).neg).mul_const lambda).exp).const_mul (lambda^m)
        using 1 <;> simp only [pow_succ] <;> ring
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s lambda : ℝ => lambda^m*Real.exp (-s*lambda))
    (F' := fun s lambda : ℝ => -(lambda^(m+1))*Real.exp (-s*lambda))
    (bound := fun _lambda : ℝ => ((m+1).factorial : ℝ)/(t/2)^(m+1))
    hs hmeas (actualHeatMoment_kernel_integrable N f m ht) hdmeas hbound
    (integrable_const _) hdiff).2
  simpa only [actualHeatMoment, neg_mul, integral_neg] using hd

theorem actualHeatMoment_deriv (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) {t : ℝ} (ht : 0<t) :
    deriv (actualHeatMoment N f m) t = -actualHeatMoment N f (m+1) t :=
  (actualHeatMoment_hasDerivAt N f m ht).deriv

theorem actualHeatMoment_differentiableOn (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) :
    DifferentiableOn ℝ (actualHeatMoment N f m) (Ioi (0 : ℝ)) :=
  fun _ ht => (actualHeatMoment_hasDerivAt N f m ht).differentiableAt.differentiableWithinAt

theorem actualHeatMoment_zero_eq_coefficient (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {t : ℝ} (ht : 0≤t) :
    actualHeatMoment N f 0 t = actualHeatCoefficient N f t := by
  simpa only [actualHeatMoment, pow_zero, one_mul] using actualHeat_scalar_integral N ht f

/-- Native iteratedDeriv, not a recursively renamed abstract derivative. -/
theorem actualHeatCoefficient_iteratedDeriv (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) {t : ℝ} (ht : 0<t) :
    iteratedDeriv m (actualHeatCoefficient N f) t = (-1 : ℝ)^m*actualHeatMoment N f m t := by
  induction m generalizing t with
  | zero =>
      rw [iteratedDeriv_zero, pow_zero, one_mul]
      exact (actualHeatMoment_zero_eq_coefficient N f ht.le).symm
  | succ m ih =>
      have heq : iteratedDeriv m (actualHeatCoefficient N f) =ᶠ[𝓝 t]
          (fun s : ℝ => (-1 : ℝ)^m*actualHeatMoment N f m s) := by
        apply Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht)
        intro s hs
        exact ih hs
      have hd := ((actualHeatMoment_hasDerivAt N f m ht).const_mul ((-1 : ℝ)^m))
        .congr_of_eventuallyEq heq
      rw [iteratedDeriv_succ, hd.deriv, pow_succ]
      ring

/-- Complete monotonicity at every order and every strictly positive
time for every actual physical quotient vector. -/
theorem actualHeatCoefficient_completeMonotone (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) {t : ℝ} (ht : 0<t) :
    0≤(-1 : ℝ)^m*iteratedDeriv m (actualHeatCoefficient N f) t := by
  have hsign : (-1 : ℝ)^m*(-1 : ℝ)^m = 1 := by rw [← mul_pow]; norm_num
  rw [actualHeatCoefficient_iteratedDeriv N f m ht, ← mul_assoc, hsign, one_mul]
  exact actualHeatMoment_nonneg N f m t

/-- Finite-order smoothness for all moments is derived simultaneously
from the proved successor recursion, then upgraded to C-infinity. -/
theorem actualHeatMoment_contDiffOn_nat (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (n m : ℕ) :
    ContDiffOn ℝ n (actualHeatMoment N f m) (Ioi (0 : ℝ)) := by
  induction n generalizing m with
  | zero =>
      exact contDiffOn_zero.mpr (actualHeatMoment_differentiableOn N f m).continuousOn
  | succ n ih =>
      have hsmooth : ContDiffOn ℝ ((n : ℕ∞ω)+1) (actualHeatMoment N f m) (Ioi (0 : ℝ)) := by
        apply (contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi).mpr
        refine ⟨actualHeatMoment_differentiableOn N f m, ?_, ?_⟩
        · simp
        · exact (ih (m+1)).neg.congr fun t ht => actualHeatMoment_deriv N f m ht
      simpa using hsmooth

theorem actualHeatMoment_contDiffOn_infty (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (m : ℕ) :
    ContDiffOn ℝ ∞ (actualHeatMoment N f m) (Ioi (0 : ℝ)) :=
  contDiffOn_infty.mpr (fun n => actualHeatMoment_contDiffOn_nat N f n m)

theorem actualHeatCoefficient_contDiffOn_infty (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    ContDiffOn ℝ ∞ (actualHeatCoefficient N f) (Ioi (0 : ℝ)) :=
  (actualHeatMoment_contDiffOn_infty N f 0).congr
    (fun _ ht => (actualHeatMoment_zero_eq_coefficient N f ht.le).symm)

end
end ImbalancedChen.Part3.Gamma0ActualHeatCompleteMonotonicity20261025a
