import ImbalancedChen.Part3RealOrderKExceptional
import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
One complex-order positive-axis K integral unifies the two actual integral
realizations used by the real exceptional and imaginary principal branches.
The identities are proved at the integrand level. This gives no equality
to a separate special-function implementation or full Kuznetsov kernel.
-/

namespace ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
noncomputable section

open Set MeasureTheory Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open RealOrderKExceptionalSourceOnly

def complexOrderIntegrand (ν : ℂ) (q u : ℝ) : ℂ :=
  (Real.exp (-q * Real.cosh u) : ℂ) * Complex.cosh (ν * (u : ℂ))

def complexOrderK (ν : ℂ) (q : ℝ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), complexOrderIntegrand ν q u

/-- A direct consequence of the exponential definition of complex cosh. -/
theorem norm_complex_cosh_le_real_cosh (z : ℂ) :
    ‖Complex.cosh z‖ ≤ Real.cosh z.re := by
  have ht : 2 * ‖Complex.cosh z‖ ≤
      Real.exp z.re + Real.exp (-z.re) := by
    calc
      2 * ‖Complex.cosh z‖ = ‖(2 : ℂ) * Complex.cosh z‖ := by simp
      _ = ‖Complex.exp z + Complex.exp (-z)‖ := by rw [Complex.two_cosh]
      _ ≤ ‖Complex.exp z‖ + ‖Complex.exp (-z)‖ := norm_add_le _ _
      _ = Real.exp z.re + Real.exp (-z.re) := by
        simp only [Complex.norm_exp, Complex.neg_re]
  rw [Real.cosh_eq]
  linarith

theorem complexOrderIntegrand_norm_le_real (ν : ℂ) (q u : ℝ) :
    ‖complexOrderIntegrand ν q u‖ ≤
      realOrderIntegrand ν.re q u := by
  have hcosh : ‖Complex.cosh (ν * (u : ℂ))‖ ≤
      Real.cosh (ν.re * u) := by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero] using
      norm_complex_cosh_le_real_cosh (ν * (u : ℂ))
  calc
    ‖complexOrderIntegrand ν q u‖ =
        Real.exp (-q * Real.cosh u) * ‖Complex.cosh (ν * (u : ℂ))‖ := by
      simp only [complexOrderIntegrand, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-q * Real.cosh u) * Real.cosh (ν.re * u) :=
      mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le
    _ = realOrderIntegrand ν.re q u := rfl

/-- The real-part strip has the same positive-u envelope as the
real-order exceptional integral. -/
theorem complexOrderIntegrand_norm_le {a q u : ℝ} {ν : ℂ}
    (ha : 0 < a) (hq : a ≤ q)
    (hν : |ν.re| ≤ (7/32 : ℝ)) (hu : 0 ≤ u) :
    ‖complexOrderIntegrand ν q u‖ ≤
      Real.exp (8/a) * Real.exp (-u) := by
  have hp : 0 ≤ realOrderIntegrand ν.re q u :=
    mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
  calc
    ‖complexOrderIntegrand ν q u‖ ≤ realOrderIntegrand ν.re q u :=
      complexOrderIntegrand_norm_le_real ν q u
    _ = ‖realOrderIntegrand ν.re q u‖ :=
      (by rw [Real.norm_eq_abs, abs_of_nonneg hp])
    _ ≤ Real.exp (8/a) * Real.exp (-u) :=
      realOrderIntegrand_norm_le ha hq hν hu

theorem complexOrderIntegrand_integrable (ν : ℂ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q)
    (hν : |ν.re| ≤ (7/32 : ℝ)) :
    IntegrableOn (complexOrderIntegrand ν q) (Ioi 0) := by
  have hc : Continuous (complexOrderIntegrand ν q) := by
    unfold complexOrderIntegrand
    fun_prop
  apply (realOrderEnvelope_integrable ha).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact complexOrderIntegrand_norm_le ha hq hν hu.le

/-- Imaginary order `ν=2it` gives exactly the previously defined
`K_{2it}` cosine-Laplace integral. -/
theorem complexOrderK_imaginary (t q : ℝ) :
    complexOrderK (((2*t : ℝ) : ℂ) * Complex.I) q =
      (imaginaryOrderK t q : ℂ) := by
  have hpoint (u : ℝ) :
      complexOrderIntegrand (((2*t : ℝ) : ℂ) * Complex.I) q u =
        (kIntegrand t q u : ℂ) := by
    have hm : ((((2*t : ℝ) : ℂ) * Complex.I) * (u : ℂ)) =
        (((2*t*u : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    unfold complexOrderIntegrand kIntegrand
    rw [hm, Complex.cosh_mul_I, ← Complex.ofReal_cos]
    push_cast
    ring
  calc
    complexOrderK (((2*t : ℝ) : ℂ) * Complex.I) q =
        ∫ u in Ioi (0 : ℝ), (kIntegrand t q u : ℂ) := by
      unfold complexOrderK
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (imaginaryOrderK t q : ℂ) := by
      rw [integral_complex_ofReal]
      rfl

/-- Real order `ν=α` gives exactly the previously defined exceptional
cosh-Laplace integral. -/
theorem complexOrderK_real (α q : ℝ) :
    complexOrderK (α : ℂ) q = (realOrderK α q : ℂ) := by
  have hpoint (u : ℝ) :
      complexOrderIntegrand (α : ℂ) q u =
        (realOrderIntegrand α q u : ℂ) := by
    have hm : (α : ℂ) * (u : ℂ) = ((α*u : ℝ) : ℂ) := by push_cast; rfl
    unfold complexOrderIntegrand realOrderIntegrand
    rw [hm, ← Complex.ofReal_cosh]
    push_cast
    ring
  calc
    complexOrderK (α : ℂ) q =
        ∫ u in Ioi (0 : ℝ), (realOrderIntegrand α q u : ℂ) := by
      unfold complexOrderK
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (realOrderK α q : ℂ) := by
      rw [integral_complex_ofReal]
      rfl

/-- Joint continuity on each closed positive-q half-line and the closed
real-part strip. It follows from the established common L1 envelope. -/
theorem complexOrderK_joint_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun p : {ν : ℂ | |ν.re| ≤ (7/32 : ℝ)} × Ici a =>
      complexOrderK (p.1 : ℂ) (p.2 : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto
    (fun r : {ν : ℂ | |ν.re| ≤ (7/32 : ℝ)} × Ici a =>
      ∫ u in Ioi (0 : ℝ), complexOrderIntegrand (r.1 : ℂ) (r.2 : ℝ) u)
    (𝓝 p)
    (𝓝 (∫ u in Ioi (0 : ℝ), complexOrderIntegrand (p.1 : ℂ) (p.2 : ℝ) u))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (8/a) * Real.exp (-u))
  · apply Filter.Eventually.of_forall
    intro r
    have hc : Continuous (fun u : ℝ =>
        complexOrderIntegrand (r.1 : ℂ) (r.2 : ℝ) u) := by
      unfold complexOrderIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro r
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact complexOrderIntegrand_norm_le ha r.2.property r.1.property hu.le
  · exact realOrderEnvelope_integrable ha
  · apply Filter.Eventually.of_forall
    intro u
    have hc : Continuous
        (fun r : {ν : ℂ | |ν.re| ≤ (7/32 : ℝ)} × Ici a =>
          complexOrderIntegrand (r.1 : ℂ) (r.2 : ℝ) u) := by
      unfold complexOrderIntegrand
      fun_prop
    exact hc.continuousAt

end
end ImbalancedChen.Part3.ComplexOrderKBridgeSourceOnly
