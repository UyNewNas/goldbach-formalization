import ImbalancedChen.Part3ImaginaryOrderKExplicitMajorant
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
ROOT reports that compilation is disabled until the user explicitly resumes
it. No compiler, checker, numerical helper or actual source edit is used.

The actual q derivative of the already defined exp-cosh cosine integral is
constructed below. All differentiability, integrability and uniform bounds
required by dominated differentiation are proved from the actual integrand.
The derivative in q is -cosh(u), with NO factor 2. The factor 2 belongs only
to cos(2*t*u), whose q derivative is zero.

The q-positive derivative is continuous, so this candidate also establishes
the real C1 property on Ioi 0. This is solely q parameter calculus for raw K.
It supplies no spectral measure, Kuznetsov identity or weighted return.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKQDerivativeSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKExplicitMajorantSourceOnly

def qDerivativeIntegrand (t q u : ℝ) : ℝ :=
  -Real.cosh u * Real.exp (-q*Real.cosh u) * Real.cos (2*t*u)

def qDerivative (t q : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), qDerivativeIntegrand t q u

/-- Uniform for every q>=a>0; no upper endpoint is needed. -/
def qDerivativeMajorant (a u : ℝ) : ℝ :=
  (2/a) * Real.exp (-(a/4)*u)

lemma kIntegrand_hasDerivAt_q (t q u : ℝ) :
    HasDerivAt (fun r => kIntegrand t r u) (qDerivativeIntegrand t q u) q := by
  convert (((hasDerivAt_id q).neg.mul_const (Real.cosh u)).exp.mul_const
    (Real.cos (2*t*u))) using 1 <;>
    dsimp [kIntegrand, qDerivativeIntegrand] <;> ring

/-- The first-degree exponential estimate used in the height-decay draft,
repeated here to keep this source independent of an uncompiled draft import. -/
lemma linear_exp_bound (a u : ℝ) :
    a * Real.cosh u * Real.exp (-a*Real.cosh u) ≤
      2 * Real.exp (-(a/2)*Real.cosh u) := by
  have hp : a*Real.cosh u ≤ 2*Real.exp (a*Real.cosh u/2) := by
    have h := Real.add_one_le_exp (a*Real.cosh u/2)
    linarith
  calc
    a * Real.cosh u * Real.exp (-a*Real.cosh u) ≤
        (2*Real.exp (a*Real.cosh u/2))*Real.exp (-a*Real.cosh u) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 2*Real.exp (-(a/2)*Real.cosh u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring

lemma cosh_exp_bound {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.cosh u * Real.exp (-a*Real.cosh u) ≤
      (2/a)*Real.exp (-(a/2)*Real.cosh u) := by
  apply (mul_le_mul_left ha).mp
  calc
    a*(Real.cosh u*Real.exp (-a*Real.cosh u)) =
        a*Real.cosh u*Real.exp (-a*Real.cosh u) := by ring
    _ ≤ 2*Real.exp (-(a/2)*Real.cosh u) := linear_exp_bound a u
    _ = a*((2/a)*Real.exp (-(a/2)*Real.cosh u)) := by
      field_simp [ha.ne'] <;> ring

lemma half_exp_le_linear {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.exp (-(a/2)*Real.cosh u) ≤ Real.exp (-(a/4)*u) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (half_le_cosh u)
    (by positivity : 0 ≤ a/2)
  nlinarith

lemma qDerivativeIntegrand_norm_le {a q : ℝ} (ha : 0 < a) (hq : a ≤ q)
    (t u : ℝ) :
    ‖qDerivativeIntegrand t q u‖ ≤ qDerivativeMajorant a u := by
  have h_exp : Real.exp (-q*Real.cosh u) ≤ Real.exp (-a*Real.cosh u) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le
    linarith
  calc
    ‖qDerivativeIntegrand t q u‖ =
        Real.cosh u * Real.exp (-q*Real.cosh u) * |Real.cos (2*t*u)| := by
      simp only [qDerivativeIntegrand, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_pos (Real.cosh_pos u), abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.cosh u * Real.exp (-q*Real.cosh u) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (mul_nonneg (Real.cosh_pos u).le (Real.exp_pos _).le)
    _ ≤ Real.cosh u * Real.exp (-a*Real.cosh u) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left h_exp (Real.cosh_pos u).le
    _ ≤ (2/a)*Real.exp (-(a/2)*Real.cosh u) := cosh_exp_bound ha u
    _ ≤ qDerivativeMajorant a u :=
      mul_le_mul_of_nonneg_left (half_exp_le_linear ha u) (by positivity)

lemma qDerivativeMajorant_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (qDerivativeMajorant a) (Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (by linarith : -(a/4) < 0) 0).const_mul (2/a)

lemma qDerivativeIntegrand_integrable (t : ℝ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qDerivativeIntegrand t q) (Ioi 0) := by
  have hc : Continuous (qDerivativeIntegrand t q) := by
    unfold qDerivativeIntegrand
    fun_prop
  exact (qDerivativeMajorant_integrable hq).mono' hc.aestronglyMeasurable
    (Eventually.of_forall (qDerivativeIntegrand_norm_le hq le_rfl t))

lemma qDerivativeIntegrand_integrable_Ici (t : ℝ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qDerivativeIntegrand t q) (Ici 0) := by
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2
    (qDerivativeIntegrand_integrable t hq)

lemma qDerivativeKernel_integrable_Ici (t : ℝ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun u => Real.cosh u * Real.exp (-q*Real.cosh u) *
      Real.cos (2*t*u)) (Ici 0) := by
  apply (qDerivativeIntegrand_integrable_Ici t hq).neg.congr
  exact Eventually.of_forall (fun u => by unfold qDerivativeIntegrand; ring)

/-- Genuine uniform domination on every compact positive q interval. -/
theorem qDerivative_uniform_domination (t a b : ℝ) (ha : 0 < a) :
    IntegrableOn (qDerivativeMajorant a) (Ioi 0) ∧
      ∀ q ∈ Icc a b, ∀ u : ℝ,
        ‖qDerivativeIntegrand t q u‖ ≤ qDerivativeMajorant a u := by
  refine ⟨qDerivativeMajorant_integrable ha, ?_⟩
  intro q hq u
  exact qDerivativeIntegrand_norm_le ha hq.1 t u

/-- The main dominated-differentiation endpoint. Its only analytic domain
premise is q>0; every hypothesis of the mathlib theorem is supplied above. -/
theorem imaginaryOrderK_hasDerivAt_q_integral (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (imaginaryOrderK t) (qDerivative t q) q := by
  have ha : 0 < q/2 := by linarith
  have hs : Ioi (q/2) ∈ 𝓝 q := Ioi_mem_nhds (by linarith)
  have hF : ∀ᶠ r in 𝓝 q,
      AEStronglyMeasurable (kIntegrand t r) (volume.restrict (Ioi (0 : ℝ))) := by
    apply Eventually.of_forall
    intro r
    have hc : Continuous (kIntegrand t r) := by unfold kIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  have hF' : AEStronglyMeasurable (qDerivativeIntegrand t q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : Continuous (qDerivativeIntegrand t q) := by
      unfold qDerivativeIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ r ∈ Ioi (q/2),
        ‖qDerivativeIntegrand t r u‖ ≤ qDerivativeMajorant (q/2) u := by
    exact Eventually.of_forall (fun u r hr => qDerivativeIntegrand_norm_le ha hr.le t u)
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ r ∈ Ioi (q/2),
        HasDerivAt (fun x => kIntegrand t x u) (qDerivativeIntegrand t r u) r := by
    exact Eventually.of_forall (fun u r _ => kIntegrand_hasDerivAt_q t r u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r u => kIntegrand t r u)
    (F' := fun r u => qDerivativeIntegrand t r u)
    (bound := qDerivativeMajorant (q/2)) hs hF (kIntegrand_integrable t hq)
    hF' hbound (qDerivativeMajorant_integrable ha) hdiff).2

/-- Lebesgue's singleton {0} has measure zero, so the displayed derivative
may be written with the requested closed endpoint Ici 0. -/
lemma qDerivative_eq_neg_Ici (t q : ℝ) :
    qDerivative t q =
      -(∫ u in Ici (0 : ℝ), Real.cosh u * Real.exp (-q*Real.cosh u) *
        Real.cos (2*t*u)) := by
  rw [integral_Ici_eq_integral_Ioi]
  unfold qDerivative
  calc
    (∫ u in Ioi (0 : ℝ), qDerivativeIntegrand t q u) =
        ∫ u in Ioi (0 : ℝ),
          -(Real.cosh u * Real.exp (-q*Real.cosh u) * Real.cos (2*t*u)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by unfold qDerivativeIntegrand; ring)
    _ = _ := integral_neg _

theorem imaginaryOrderK_hasDerivAt_q (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (imaginaryOrderK t)
      (-(∫ u in Ici (0 : ℝ), Real.cosh u * Real.exp (-q*Real.cosh u) *
        Real.cos (2*t*u))) q := by
  rw [← qDerivative_eq_neg_Ici]
  exact imaginaryOrderK_hasDerivAt_q_integral t hq

theorem deriv_imaginaryOrderK_q (t : ℝ) {q : ℝ} (hq : 0 < q) :
    deriv (imaginaryOrderK t) q =
      -(∫ u in Ici (0 : ℝ), Real.cosh u * Real.exp (-q*Real.cosh u) *
        Real.cos (2*t*u)) := by
  exact (imaginaryOrderK_hasDerivAt_q t hq).deriv

theorem imaginaryOrderK_differentiableOn_q (t : ℝ) :
    DifferentiableOn ℝ (imaginaryOrderK t) (Ioi 0) := by
  intro q hq
  exact (imaginaryOrderK_hasDerivAt_q_integral t hq).differentiableAt.differentiableWithinAt

/-- Continuity of the actual derivative follows from the same explicit
local majorant; this is not assumed as a C1/spectral-family premise. -/
theorem qDerivative_continuousAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ContinuousAt (qDerivative t) q := by
  have ha : 0 < q/2 := by linarith
  change Tendsto
    (fun r : ℝ => ∫ u in Ioi (0 : ℝ), qDerivativeIntegrand t r u)
    (𝓝 q) (𝓝 (∫ u in Ioi (0 : ℝ), qDerivativeIntegrand t q u))
  apply tendsto_integral_filter_of_dominated_convergence (qDerivativeMajorant (q/2))
  · apply Eventually.of_forall
    intro r
    have hc : Continuous (qDerivativeIntegrand t r) := by
      unfold qDerivativeIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (by linarith : q/2 < q)] with r hr
    exact Eventually.of_forall (qDerivativeIntegrand_norm_le ha hr.le t)
  · exact qDerivativeMajorant_integrable ha
  · apply Eventually.of_forall
    intro u
    have hc : Continuous (fun r : ℝ => qDerivativeIntegrand t r u) := by
      unfold qDerivativeIntegrand
      fun_prop
    exact hc.continuousAt

theorem qDerivative_continuousOn (t : ℝ) :
    ContinuousOn (qDerivative t) (Ioi 0) := by
  intro q hq
  exact (qDerivative_continuousAt t hq).continuousWithinAt

theorem deriv_imaginaryOrderK_continuousOn_q (t : ℝ) :
    ContinuousOn (deriv (imaginaryOrderK t)) (Ioi 0) := by
  exact (qDerivative_continuousOn t).congr
    (fun q hq => (imaginaryOrderK_hasDerivAt_q_integral t hq).deriv)

/-- The actual integral is C1 in q throughout the positive axis. -/
theorem imaginaryOrderK_contDiffOn_one_q (t : ℝ) :
    ContDiffOn ℝ 1 (imaginaryOrderK t) (Ioi 0) := by
  have hchar : ContDiffOn ℝ 1 (imaginaryOrderK t) (Ioi (0 : ℝ)) ↔
      DifferentiableOn ℝ (imaginaryOrderK t) (Ioi (0 : ℝ)) ∧
        ContinuousOn (deriv (imaginaryOrderK t)) (Ioi (0 : ℝ)) := by
    rw [show (1 : ℕ∞ω) = 0+1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    simp
  exact hchar.mpr ⟨imaginaryOrderK_differentiableOn_q t,
    deriv_imaginaryOrderK_continuousOn_q t⟩

theorem imaginaryOrderK_contDiffOn_one_Icc (t : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ 1 (imaginaryOrderK t) (Icc a b) := by
  exact (imaginaryOrderK_contDiffOn_one_q t).mono
    (fun q hq => lt_of_lt_of_le ha hq.1)

lemma qDerivativeMajorant_integral {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), qDerivativeMajorant a u) = 8/a^2 := by
  have hexp : (∫ u in Ioi (0 : ℝ), Real.exp (-(a/4)*u)) = 4/a := by
    rw [integral_exp_mul_Ioi (by linarith : -(a/4) < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ha.ne']
  change (∫ u in Ioi (0 : ℝ), (2/a)*Real.exp (-(a/4)*u)) = 8/a^2
  rw [integral_const_mul, hexp]
  field_simp [ha.ne'] <;> ring

theorem qDerivative_abs_le_on_halfLine (t : ℝ) {a q : ℝ}
    (ha : 0 < a) (hq : a ≤ q) :
    |qDerivative t q| ≤ 8/a^2 := by
  calc
    |qDerivative t q| ≤ ∫ u in Ioi (0 : ℝ), qDerivativeMajorant a u := by
      simpa only [qDerivative, Real.norm_eq_abs] using
        norm_integral_le_of_norm_le (qDerivativeMajorant_integrable ha)
          (Eventually.of_forall (qDerivativeIntegrand_norm_le ha hq t))
    _ = 8/a^2 := qDerivativeMajorant_integral ha

theorem qDerivative_abs_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |qDerivative t q| ≤ 8/q^2 := by
  exact qDerivative_abs_le_on_halfLine t hq le_rfl

theorem deriv_imaginaryOrderK_abs_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |deriv (imaginaryOrderK t) q| ≤ 8/q^2 := by
  rw [(imaginaryOrderK_hasDerivAt_q_integral t hq).deriv]
  exact qDerivative_abs_le t hq

/-- An actual compact-q consequence of the proved derivative bound, using
the mean value theorem with no Lipschitz hypothesis on K. -/
theorem imaginaryOrderK_lipschitz_on_Icc (t : ℝ) {a b r s : ℝ} (ha : 0 < a)
    (hr : r ∈ Icc a b) (hs : s ∈ Icc a b) :
    |imaginaryOrderK t r - imaginaryOrderK t s| ≤ (8/a^2)*|r-s| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := imaginaryOrderK t) (f' := qDerivative t) (s := Icc a b)
    (fun q hq => (imaginaryOrderK_hasDerivAt_q_integral t
      (lt_of_lt_of_le ha hq.1)).hasDerivWithinAt)
    (fun q hq => by
      simpa only [Real.norm_eq_abs] using qDerivative_abs_le_on_halfLine t ha hq.1)
    (convex_Icc a b) hs hr
  simpa only [Real.norm_eq_abs] using h

/-- The actual dq/q normalizer differentiated as a q function. -/
theorem imaginaryOrderK_div_hasDerivAt_q (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r => imaginaryOrderK t r / r)
      ((qDerivative t q * q - imaginaryOrderK t q)/q^2) q := by
  simpa only [mul_one, id_eq] using
    (imaginaryOrderK_hasDerivAt_q_integral t hq).div (hasDerivAt_id q) hq.ne'

theorem imaginaryOrderK_div_deriv_abs_le (t : ℝ) {q : ℝ} (hq : 0 < q) :
    |deriv (fun r => imaginaryOrderK t r / r) q| ≤ 10/q^3 := by
  rw [(imaginaryOrderK_div_hasDerivAt_q t hq).deriv, abs_div,
    abs_of_pos (pow_pos hq 2)]
  have hdiff : |qDerivative t q * q - imaginaryOrderK t q| ≤
      |qDerivative t q| * q + |imaginaryOrderK t q| := by
    calc
      |qDerivative t q * q - imaginaryOrderK t q| ≤
          |qDerivative t q * q| + |imaginaryOrderK t q| := abs_sub _ _
      _ = _ := by rw [abs_mul, abs_of_pos hq]
  calc
    |qDerivative t q * q - imaginaryOrderK t q| / q^2 ≤
        (|qDerivative t q|*q+|imaginaryOrderK t q|)/q^2 :=
      div_le_div_of_nonneg_right hdiff (sq_nonneg q)
    _ ≤ ((8/q^2)*q+2/q)/q^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg q)
      exact add_le_add (mul_le_mul_of_nonneg_right (qDerivative_abs_le t hq) hq.le)
        (imaginaryOrderK_abs_le t hq)
    _ = 10/q^3 := by field_simp [hq.ne'] <;> ring

end
end ImbalancedChen.Part3.ImaginaryOrderKQDerivativeSourceOnly
