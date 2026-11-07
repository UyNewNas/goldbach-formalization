import ImbalancedChen.Part3ImaginaryOrderKPositiveAxis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
The real-order K integral for the complementary/exceptional branch.
`alpha` is the actual real Bessel order, not the imaginary-order parameter
`2*t`.  The analytic definition and continuity do not assert a Kuznetsov
identity, a spectral bound, or the 7/32 estimate itself.
-/

namespace ImbalancedChen.Part3.RealOrderKExceptionalSourceOnly
noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology

/-- The real-order cosine-hyperbolic Laplace kernel. -/
def realOrderIntegrand (α q u : ℝ) : ℝ :=
  Real.exp (-q * Real.cosh u) * Real.cosh (α * u)

/-- The integral realization of `K_α(q)` on the positive axis. -/
def realOrderK (α q : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), realOrderIntegrand α q u

/-- Elementary quadratic growth is enough to dominate every order in the
fixed exceptional interval, even when the positive q cutoff is small. -/
private lemma cosh_quadratic_lower {u : ℝ} (hu : 0 ≤ u) :
    u^2 / 8 ≤ Real.cosh u := by
  have he : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp _
  have hb : 0 ≤ u / 2 + 1 := by linarith
  have hs : (u / 2 + 1)^2 ≤ (Real.exp (u / 2))^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he)
      (add_nonneg (Real.exp_nonneg _) hb)]
  have hexp : Real.exp u = (Real.exp (u / 2))^2 := by
    calc
      Real.exp u = Real.exp (u / 2 + u / 2) := by congr 1 <;> ring
      _ = Real.exp (u / 2) * Real.exp (u / 2) := Real.exp_add _ _
      _ = (Real.exp (u / 2))^2 := by ring
  rw [Real.cosh_eq, hexp]
  nlinarith [Real.exp_pos (-u)]

private lemma cosh_order_le_exp {α u : ℝ}
    (hα : |α| ≤ (7 / 32 : ℝ)) (hu : 0 ≤ u) :
    Real.cosh (α * u) ≤ Real.exp u := by
  have hαp : α ≤ 1 := by linarith [le_abs_self α]
  have hαn : -α ≤ 1 := by linarith [neg_le_abs α]
  have hp : Real.exp (α * u) ≤ Real.exp u :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hn : Real.exp (-(α * u)) ≤ Real.exp u :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.cosh_eq]
  linarith

/-- A pointwise L1 envelope shared by every `|α|≤7/32` and every `q≥a`.
The constant `8/a` comes from `(a*u-8)^2≥0`. -/
theorem realOrderIntegrand_norm_le {a q α u : ℝ}
    (ha : 0 < a) (hq : a ≤ q) (hα : |α| ≤ (7 / 32 : ℝ))
    (hu : 0 ≤ u) :
    ‖realOrderIntegrand α q u‖ ≤
      Real.exp (8 / a) * Real.exp (-u) := by
  have hc := cosh_quadratic_lower hu
  have hcpos := Real.cosh_pos u
  have hprod : a * Real.cosh u ≤ q * Real.cosh u :=
    mul_le_mul_of_nonneg_right hq hcpos.le
  have hdiv : a * (8 / a) = 8 := by field_simp [ne_of_gt ha]
  have hsq := sq_nonneg (a * u - 8)
  have hlinear : 2 * u - 8 / a ≤ a * Real.cosh u := by
    have hcs : 0 ≤ a^2 * (Real.cosh u - u^2/8) :=
      mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hc)
    have hmul : 0 ≤ a * (a * Real.cosh u - 2*u + 8/a) := by
      nlinarith [hcs, hsq, hdiv]
    nlinarith
  have horder := cosh_order_le_exp hα hu
  calc
    ‖realOrderIntegrand α q u‖ =
        Real.exp (-q * Real.cosh u) * Real.cosh (α*u) := by
      simp only [realOrderIntegrand, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _), abs_of_pos (Real.cosh_pos _)]
    _ ≤ Real.exp (-q * Real.cosh u) * Real.exp u :=
      mul_le_mul_of_nonneg_left horder (Real.exp_pos _).le
    _ = Real.exp (-q * Real.cosh u + u) := by rw [← Real.exp_add]
    _ ≤ Real.exp (8/a-u) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = Real.exp (8/a) * Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1 <;> ring

theorem realOrderEnvelope_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (8/a) * Real.exp (-u)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => Real.exp ((-1 : ℝ)*u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
  simpa only [neg_one_mul] using h.const_mul (Real.exp (8/a))

/-- Absolute integrability of the real-order integral on the entire
exceptional order interval.  No prior K-integrability premise is used. -/
theorem realOrderIntegrand_integrable (α : ℝ) {q : ℝ} (hq : 0 < q)
    (hα : |α| ≤ (7 / 32 : ℝ)) :
    IntegrableOn (realOrderIntegrand α q) (Ioi 0) := by
  have hc : Continuous (realOrderIntegrand α q) := by
    unfold realOrderIntegrand
    fun_prop
  apply (realOrderEnvelope_integrable hq).mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact realOrderIntegrand_norm_le hq le_rfl hα hu.le

theorem realOrderK_even (α q : ℝ) : realOrderK (-α) q = realOrderK α q := by
  unfold realOrderK
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  simp only [realOrderIntegrand, neg_mul, Real.cosh_neg]

theorem realOrderK_pos (α : ℝ) {q : ℝ} (hq : 0 < q)
    (hα : |α| ≤ (7 / 32 : ℝ)) : 0 < realOrderK α q := by
  have hint := realOrderIntegrand_integrable α hq hα
  have hc : Continuous (realOrderIntegrand α q) := by
    unfold realOrderIntegrand
    fun_prop
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] realOrderIntegrand α q :=
    Filter.Eventually.of_forall (fun u =>
      mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
  apply (setIntegral_pos_iff_support_of_nonneg_ae hn hint).2
  have hopen : IsOpen (support (realOrderIntegrand α q) ∩ Ioi (0 : ℝ)) :=
    hc.isOpen_support.inter isOpen_Ioi
  have hmem : (1 : ℝ) ∈ support (realOrderIntegrand α q) ∩ Ioi (0 : ℝ) := by
    constructor
    · change realOrderIntegrand α q 1 ≠ 0
      unfold realOrderIntegrand
      exact ne_of_gt (mul_pos (Real.exp_pos _) (Real.cosh_pos _))
    · norm_num
  exact IsOpen.measure_pos volume hopen ⟨1, hmem⟩

/-- Joint continuity on every positive q half-line and the closed
exceptional order interval, including both order endpoints. -/
theorem realOrderK_joint_continuous (a : ℝ) (ha : 0 < a) :
    Continuous (fun p : Icc (-(7/32 : ℝ)) (7/32 : ℝ) × Ici a =>
      realOrderK (p.1 : ℝ) (p.2 : ℝ)) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto
    (fun r : Icc (-(7/32 : ℝ)) (7/32 : ℝ) × Ici a =>
      ∫ u in Ioi (0 : ℝ), realOrderIntegrand (r.1 : ℝ) (r.2 : ℝ) u)
    (𝓝 p)
    (𝓝 (∫ u in Ioi (0 : ℝ), realOrderIntegrand (p.1 : ℝ) (p.2 : ℝ) u))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (8/a) * Real.exp (-u))
  · apply Filter.Eventually.of_forall
    intro r
    have hc : Continuous (fun u : ℝ =>
        realOrderIntegrand (r.1 : ℝ) (r.2 : ℝ) u) := by
      unfold realOrderIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro r
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hα : |(r.1 : ℝ)| ≤ (7/32 : ℝ) := by
      rcases r.1.property with ⟨hlo, hhi⟩
      exact abs_le.mpr ⟨by linarith, hhi⟩
    exact realOrderIntegrand_norm_le ha r.2.property hα hu.le
  · exact realOrderEnvelope_integrable ha
  · apply Filter.Eventually.of_forall
    intro u
    have hc : Continuous (fun r : Icc (-(7/32 : ℝ)) (7/32 : ℝ) × Ici a =>
        realOrderIntegrand (r.1 : ℝ) (r.2 : ℝ) u) := by
      unfold realOrderIntegrand
      fun_prop
    exact hc.continuousAt

end
end ImbalancedChen.Part3.RealOrderKExceptionalSourceOnly
