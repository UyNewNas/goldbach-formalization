import ImbalancedChen.Part3ComplexOrderKBridge
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
Complex differentiability in the order parameter only, on the open
real-part strip |Re nu|<7/32. The derivative is the literal positive-u
integral of exp(-q cosh u) u sinh(nu u). No q differentiation, Bessel
ODE, Kuznetsov identity, or spectral estimate is asserted.
-/

namespace ImbalancedChen.Part3.ComplexOrderKHolomorphicSourceOnly
noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology
open ComplexOrderKBridgeSourceOnly
open RealOrderKExceptionalSourceOnly (realOrderIntegrand realOrderIntegrand_norm_le realOrderEnvelope_integrable)

def complexOrderDerivIntegrand (ν : ℂ) (q u : ℝ) : ℂ :=
  (Real.exp (-q * Real.cosh u) : ℂ) * (u : ℂ) *
    Complex.sinh (ν * (u : ℂ))

theorem norm_complex_sinh_le_real_cosh (z : ℂ) :
    ‖Complex.sinh z‖ ≤ Real.cosh z.re := by
  have ht : 2 * ‖Complex.sinh z‖ ≤
      Real.exp z.re + Real.exp (-z.re) := by
    calc
      2 * ‖Complex.sinh z‖ = ‖(2 : ℂ) * Complex.sinh z‖ := by simp
      _ = ‖Complex.exp z - Complex.exp (-z)‖ := by rw [Complex.two_sinh]
      _ ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_sub_le _ _
      _ = Real.exp z.re + Real.exp (-z.re) := by
        simp only [Complex.norm_exp, Complex.neg_re]
  rw [Real.cosh_eq]
  linarith

private lemma u_exp_neg_le {u : ℝ} (hu : 0 ≤ u) :
    u * Real.exp (-u) ≤ 2 * Real.exp (-(u/2)) := by
  have he := Real.add_one_le_exp (u/2)
  have hle : u ≤ 2 * Real.exp (u/2) := by linarith
  calc
    u * Real.exp (-u) ≤ (2 * Real.exp (u/2)) * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    _ = 2 * Real.exp (-(u/2)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1 <;> ring

/-- The derivative has an integrable uniform bound throughout every
positive q half-line and closed 7/32 strip. -/
theorem complexOrderDerivIntegrand_norm_le {a q u : ℝ} {ν : ℂ}
    (ha : 0 < a) (hq : a ≤ q)
    (hν : |ν.re| ≤ (7/32 : ℝ)) (hu : 0 ≤ u) :
    ‖complexOrderDerivIntegrand ν q u‖ ≤
      2 * Real.exp (8/a) * Real.exp (-(u/2)) := by
  have hs : ‖Complex.sinh (ν * (u : ℂ))‖ ≤
      Real.cosh (ν.re * u) := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using
      norm_complex_sinh_le_real_cosh (ν * (u : ℂ))
  have hbase : Real.exp (-q * Real.cosh u) *
      Real.cosh (ν.re * u) ≤ Real.exp (8/a) * Real.exp (-u) := by
    have hp : 0 ≤ realOrderIntegrand ν.re q u :=
      mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
    simpa only [realOrderIntegrand, Real.norm_eq_abs, abs_of_nonneg hp] using
      realOrderIntegrand_norm_le ha hq hν hu
  have h0 : 0 ≤ Real.exp (-q * Real.cosh u) := (Real.exp_pos _).le
  have hmid : ‖complexOrderDerivIntegrand ν q u‖ ≤
      u * (Real.exp (-q * Real.cosh u) * Real.cosh (ν.re * u)) := by
    calc
      ‖complexOrderDerivIntegrand ν q u‖ =
          u * (Real.exp (-q * Real.cosh u) *
            ‖Complex.sinh (ν * (u : ℂ))‖) := by
        simp only [complexOrderDerivIntegrand, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_nonneg hu]
        ring
      _ ≤ u * (Real.exp (-q * Real.cosh u) * Real.cosh (ν.re * u)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs h0) hu
  calc
    ‖complexOrderDerivIntegrand ν q u‖ ≤
        u * (Real.exp (-q * Real.cosh u) * Real.cosh (ν.re * u)) := hmid
    _ ≤ u * (Real.exp (8/a) * Real.exp (-u)) :=
      mul_le_mul_of_nonneg_left hbase hu
    _ ≤ 2 * Real.exp (8/a) * Real.exp (-(u/2)) := by
      have hh := mul_le_mul_of_nonneg_left (u_exp_neg_le hu)
        (Real.exp_pos (8/a)).le
      nlinarith [hh]

theorem complexOrderDerivEnvelope_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ =>
      2 * Real.exp (8/a) * Real.exp (-(u/2))) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => Real.exp ((-(1/2) : ℝ)*u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num : (-(1/2) : ℝ) < 0) 0
  have he : (fun u : ℝ => Real.exp ((-(1/2) : ℝ)*u)) =
      (fun u : ℝ => Real.exp (-(u/2))) := by
    funext u
    congr 1
    ring
  rw [he] at h
  exact h.const_mul (2 * Real.exp (8/a))

theorem complexOrderDerivIntegrand_integrable (ν : ℂ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q)
    (hν : |ν.re| ≤ (7/32 : ℝ)) :
    IntegrableOn (complexOrderDerivIntegrand ν q) (Ioi 0) := by
  have hc : Continuous (complexOrderDerivIntegrand ν q) := by
    unfold complexOrderDerivIntegrand
    fun_prop
  apply (complexOrderDerivEnvelope_integrable ha).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact complexOrderDerivIntegrand_norm_le ha hq hν hu.le

private lemma complexOrderIntegrand_hasDerivAt (q u : ℝ) (ν : ℂ) :
    HasDerivAt (fun z : ℂ => complexOrderIntegrand z q u)
      (complexOrderDerivIntegrand ν q u) ν := by
  have hm : HasDerivAt (fun z : ℂ => z * (u : ℂ)) (u : ℂ) ν := by
    simpa using (hasDerivAt_id ν).mul_const (u : ℂ)
  have hc := hm.ccosh
  have he := hc.const_mul (Real.exp (-q * Real.cosh u) : ℂ)
  simpa only [complexOrderIntegrand, complexOrderDerivIntegrand,
    mul_assoc, mul_comm, mul_left_comm] using he

private lemma open_order_strip :
    IsOpen {ν : ℂ | |ν.re| < (7/32 : ℝ)} := by
  have hr : Continuous (fun ν : ℂ => |ν.re|) :=
    continuous_abs.comp Complex.continuous_re
  exact isOpen_lt hr continuous_const

/-- The integral derivative is valid at every order strictly inside the
exceptional real-part strip. -/
theorem complexOrderK_hasDerivAt (ν : ℂ) (q : ℝ) (hq : 0 < q)
    (hν : |ν.re| < (7/32 : ℝ)) :
    HasDerivAt (fun z : ℂ => complexOrderK z q)
      (∫ u in Ioi (0 : ℝ), complexOrderDerivIntegrand ν q u) ν := by
  let s : Set ℂ := {z | |z.re| < (7/32 : ℝ)}
  have hs : s ∈ 𝓝 ν := open_order_strip.mem_nhds hν
  have hFmeas : ∀ᶠ z in 𝓝 ν,
      AEStronglyMeasurable (complexOrderIntegrand z q)
        (volume.restrict (Ioi (0 : ℝ))) := by
    apply Filter.Eventually.of_forall
    intro z
    have hc : Continuous (complexOrderIntegrand z q) := by
      unfold complexOrderIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hFint : IntegrableOn (complexOrderIntegrand ν q) (Ioi 0) :=
    complexOrderIntegrand_integrable ν hq le_rfl (le_of_lt hν)
  have hF'meas : AEStronglyMeasurable (complexOrderDerivIntegrand ν q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : Continuous (complexOrderDerivIntegrand ν q) := by
      unfold complexOrderDerivIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ z ∈ s, ‖complexOrderDerivIntegrand z q u‖ ≤
        2 * Real.exp (8/q) * Real.exp (-(u/2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro z hz
    exact complexOrderDerivIntegrand_norm_le hq le_rfl (le_of_lt hz) hu.le
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ z ∈ s,
        HasDerivAt (fun w : ℂ => complexOrderIntegrand w q u)
          (complexOrderDerivIntegrand z q u) z := by
    exact Filter.Eventually.of_forall
      (fun u z _ => complexOrderIntegrand_hasDerivAt q u z)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z u => complexOrderIntegrand z q u)
    (F' := fun z u => complexOrderDerivIntegrand z q u)
    (bound := fun u => 2 * Real.exp (8/q) * Real.exp (-(u/2)))
    hs hFmeas hFint hF'meas hbound
    (complexOrderDerivEnvelope_integrable hq) hdiff
  exact hd.2

theorem complexOrderK_differentiableOn (q : ℝ) (hq : 0 < q) :
    DifferentiableOn ℂ (fun z : ℂ => complexOrderK z q)
      {z : ℂ | |z.re| < (7/32 : ℝ)} := by
  intro ν hν
  exact (complexOrderK_hasDerivAt ν q hq hν).differentiableAt.differentiableWithinAt

end
end ImbalancedChen.Part3.ComplexOrderKHolomorphicSourceOnly
