import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED, 2026-10-24.

The real-line Dirichlet form for a complex-valued C² compactly
supported function, followed by the full positive quadratic form for
one tensor on the upper-half-plane coordinate chart. The weighted
coordinate measure and all integrability claims are defined and proved
here. Identification with the canonical `UpperHalfPlane.volume` remains
a separate change-of-coordinates lemma.
-/

namespace ImbalancedChen.Part3.CompactComplexLaplacianForm20261024z

noncomputable section

open MeasureTheory

/-- Complex integration by parts with no boundary term.  The support of
`deriv f` and `deriv (deriv f)` is compact because the support of `f` is
compact; the three integrands are consequently integrable. -/
theorem integral_star_mul_secondDeriv (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, star (f x) * deriv (deriv f) x) =
      -(∫ x : ℝ, star (deriv f x) * deriv f x) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by
    simpa using hf
  have hfst : Differentiable ℝ f := (contDiff_succ_iff_deriv.mp hs).1
  have hdf : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hs).2.2
  have hdst : Differentiable ℝ (deriv f) := hdf.differentiable_one
  have hc₀ : Continuous f := hf.continuous
  have hc₁ : Continuous (deriv f) := hdf.continuous
  have hc₂ : Continuous (deriv (deriv f)) := hdf.continuous_deriv_one
  have hi₁ : Integrable (fun x : ℝ => star (f x) * deriv (deriv f) x) :=
    (hc₀.star.mul hc₂).integrable_of_hasCompactSupport
      (hfc.deriv.deriv.mul_left)
  have hi₂ : Integrable (fun x : ℝ => star (deriv f x) * deriv f x) :=
    (hc₁.star.mul hc₁).integrable_of_hasCompactSupport
      (hfc.deriv.mul_left)
  have hi₀ : Integrable (fun x : ℝ => star (f x) * deriv f x) :=
    (hc₀.star.mul hc₁).integrable_of_hasCompactSupport
      (hfc.deriv.mul_left)
  exact MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => star (f x))
    (v := deriv f)
    (u' := fun x : ℝ => star (deriv f x))
    (v' := deriv (deriv f))
    (fun x _ => (hfst x).hasDerivAt.star)
    (fun x _ => (hdst x).hasDerivAt)
    hi₁ hi₂ hi₀

/-- The compact-support energy identity, with the actual real-line second
derivative and the complex conjugate represented by `star`. -/
theorem integral_negative_secondDeriv_eq_deriv_norm_sq (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, -(star (f x) * deriv (deriv f) x)) =
      ((∫ x : ℝ, ‖deriv f x‖ ^ 2) : ℂ) := by
  rw [integral_neg, integral_star_mul_secondDeriv f hf hfc, neg_neg]
  have hpoint (x : ℝ) :
      star (deriv f x) * deriv f x = ((‖deriv f x‖ ^ 2 : ℝ) : ℂ) := by
    calc
      star (deriv f x) * deriv f x =
          (Complex.normSq (deriv f x) : ℂ) := by
        simpa only [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := deriv f x)).symm
      _ = ((‖deriv f x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
  simp_rw [hpoint]
  exact MeasureTheory.integral_complex_ofReal

/-- Real-part identity needed for positivity of the Laplacian form. -/
theorem re_integral_negative_secondDeriv_eq_deriv_norm_sq (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x : ℝ, -(star (f x) * deriv (deriv f) x)).re =
      ∫ x : ℝ, ‖deriv f x‖ ^ 2 := by
  simpa using congrArg Complex.re
    (integral_negative_secondDeriv_eq_deriv_norm_sq f hf hfc)

/-- Nonnegativity of the one-dimensional component of the form. -/
theorem re_integral_negative_secondDeriv_nonneg (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (∫ x : ℝ, -(star (f x) * deriv (deriv f) x)).re := by
  rw [re_integral_negative_secondDeriv_eq_deriv_norm_sq f hf hfc]
  exact integral_nonneg (fun x : ℝ => sq_nonneg (‖deriv f x‖))

/-!
## A single tensor in the upper-half-plane coordinate chart

The following measure is exactly `y⁻² dx dy` on the positive chart. It
first restricts planar Lebesgue measure to `y > 0` and then multiplies by
the nonnegative density `(y⁻¹)^2`. The value of the density outside that
open chart is irrelevant. Its relation to the canonical complex-coordinate
`UpperHalfPlane.volume` can be proved by the real/imaginary chart map.
-/

def upperChart : Set (ℝ × ℝ) := {p | 0 < p.2}

theorem upperChart_measurable : MeasurableSet upperChart := by
  exact measurableSet_Ioi.preimage measurable_snd

def chartWeight (p : ℝ × ℝ) : ℝ≥0 :=
  ⟨(p.2⁻¹) ^ 2, sq_nonneg _⟩

theorem chartWeight_measurable : Measurable chartWeight := by
  unfold chartWeight
  exact Measurable.subtype_mk (measurable_snd.inv.pow_const 2)

def chartMeasure : Measure (ℝ × ℝ) :=
  ((volume : Measure (ℝ × ℝ)).restrict upperChart).withDensity
    (fun p => (chartWeight p : ℝ≥0∞))

/-- The tensor and its actual negative hyperbolic Laplacian in the
`(x,y)` chart. -/
def tensorFunction (g h : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  g p.1 * h p.2

def tensorHyperbolicLaplacian (g h : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((p.2 : ℂ) ^ 2 *
    (deriv (deriv g) p.1 * h p.2 + g p.1 * deriv (deriv h) p.2))

def unweightedTensorForm (g h : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((star (g p.1) * deriv (deriv g) p.1) *
        (star (h p.2) * h p.2) +
      (star (g p.1) * g p.1) *
        (star (h p.2) * deriv (deriv h) p.2))

def tensorEnergy (g h : ℝ → ℂ) : ℝ :=
  (∫ x : ℝ, ‖deriv g x‖ ^ 2) * (∫ y : ℝ, ‖h y‖ ^ 2) +
    (∫ x : ℝ, ‖g x‖ ^ 2) * (∫ y : ℝ, ‖deriv h y‖ ^ 2)

/-- The hyperbolic density cancels the `y²` in the Laplacian at every
point of the open chart. -/
theorem chartWeight_mul_tensor_form (g h : ℝ → ℂ) {p : ℝ × ℝ}
    (hp : p ∈ upperChart) :
    chartWeight p •
        (star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p) =
      unweightedTensorForm g h p := by
  have hy : 0 < p.2 := hp
  have hqReal : (p.2⁻¹) ^ 2 * p.2 ^ 2 = (1 : ℝ) := by
    rw [← mul_pow, inv_mul_cancel₀ (ne_of_gt hy), one_pow]
  have hq : ((chartWeight p : ℝ) : ℂ) * (p.2 : ℂ) ^ 2 = 1 := by
    change (((p.2⁻¹) ^ 2 : ℝ) : ℂ) * (p.2 : ℂ) ^ 2 = 1
    exact_mod_cast hqReal
  calc
    chartWeight p •
        (star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p) =
        (((chartWeight p : ℝ) : ℂ) * (p.2 : ℂ) ^ 2) *
          unweightedTensorForm g h p := by
      simp only [tensorFunction, tensorHyperbolicLaplacian,
        unweightedTensorForm, NNReal.smul_def, Complex.real_smul, star_mul]
      ring
    _ = unweightedTensorForm g h p := by rw [hq, one_mul]

/-- The compact one-dimensional mass term is integrable. -/
theorem integrable_star_mul_self (f : ℝ → ℂ)
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x : ℝ => star (f x) * f x) :=
  (hf.star.mul hf).integrable_of_hasCompactSupport (hfc.mul_left)

/-- The compact second-derivative term is integrable. -/
theorem integrable_star_mul_secondDeriv (f : ℝ → ℂ)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun x : ℝ => star (f x) * deriv (deriv f) x) := by
  have hs : ContDiff ℝ ((1 : ℕ∞ω) + 1) f := by
    simpa using hf
  have hdf : ContDiff ℝ 1 (deriv f) := (contDiff_succ_iff_deriv.mp hs).2.2
  exact (hf.continuous.star.mul hdf.continuous_deriv_one).integrable_of_hasCompactSupport
    (hfc.deriv.deriv.mul_left)

theorem unweightedTensorForm_integrable (g h : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    Integrable (unweightedTensorForm g h)
      (volume : Measure (ℝ × ℝ)) := by
  change Integrable (fun p : ℝ × ℝ =>
      -((star (g p.1) * deriv (deriv g) p.1) *
            (star (h p.2) * h p.2) +
          (star (g p.1) * g p.1) *
            (star (h p.2) * deriv (deriv h) p.2)))
    ((volume : Measure ℝ).prod (volume : Measure ℝ))
  exact (((integrable_star_mul_secondDeriv g hg hgc).mul_prod
      (integrable_star_mul_self h hh.continuous hhc)).add
    ((integrable_star_mul_self g hg.continuous hgc).mul_prod
      (integrable_star_mul_secondDeriv h hh hhc))).neg

/-- The weighted tensor integrand is integrable under the actual
hyperbolic chart measure; no integrability premise is supplied. -/
theorem tensorForm_integrable (g h : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    Integrable (fun p : ℝ × ℝ =>
      star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p)
      chartMeasure := by
  unfold chartMeasure
  apply (integrable_withDensity_iff_integrable_smul chartWeight_measurable).2
  have hbase : Integrable (unweightedTensorForm g h)
      ((volume : Measure (ℝ × ℝ)).restrict upperChart) :=
    (unweightedTensorForm_integrable g h hg hh hgc hhc).integrableOn upperChart
  apply hbase.congr
  apply (ae_restrict_iff' upperChart_measurable).2
  exact Filter.Eventually.of_forall fun p hp =>
    (chartWeight_mul_tensor_form g h hp).symm

theorem chartTensorForm_integral_eq_unweighted (g h : ℝ → ℂ)
    (hhpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    (∫ p : ℝ × ℝ,
      star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p
      ∂chartMeasure) =
      ∫ p : ℝ × ℝ, unweightedTensorForm g h p := by
  unfold chartMeasure
  rw [integral_withDensity_eq_integral_smul chartWeight_measurable]
  change (∫ p in upperChart,
      chartWeight p •
        (star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p)
      ∂(volume : Measure (ℝ × ℝ))) = _
  calc
    (∫ p in upperChart,
      chartWeight p •
        (star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p)
      ∂(volume : Measure (ℝ × ℝ))) =
        ∫ p in upperChart, unweightedTensorForm g h p
          ∂(volume : Measure (ℝ × ℝ)) := by
      apply setIntegral_congr_fun upperChart_measurable
      intro p hp
      exact chartWeight_mul_tensor_form g h hp
    _ = ∫ p : ℝ × ℝ, unweightedTensorForm g h p := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hyNot : p.2 ∉ tsupport h := by
        intro hy
        exact hp (hhpos hy)
      have hz : h p.2 = 0 := image_eq_zero_of_notMem_tsupport hyNot
      simp [unweightedTensorForm, hz]

theorem integral_star_mul_self_eq_norm_sq (f : ℝ → ℂ) :
    (∫ x : ℝ, star (f x) * f x) =
      ((∫ x : ℝ, ‖f x‖ ^ 2) : ℂ) := by
  have hpoint (x : ℝ) :
      star (f x) * f x = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    calc
      star (f x) * f x = (Complex.normSq (f x) : ℂ) := by
        simpa only [Complex.star_def] using
          (Complex.normSq_eq_conj_mul_self (z := f x)).symm
      _ = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq]
  simp_rw [hpoint]
  exact integral_complex_ofReal

theorem unweightedTensorForm_integral_eq_energy (g h : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h) :
    (∫ p : ℝ × ℝ, unweightedTensorForm g h p) =
      (tensorEnergy g h : ℂ) := by
  have hA := integrable_star_mul_secondDeriv g hg hgc
  have hB := integrable_star_mul_self h hh.continuous hhc
  have hC := integrable_star_mul_self g hg.continuous hgc
  have hD := integrable_star_mul_secondDeriv h hh hhc
  have hAB : Integrable (fun p : ℝ × ℝ =>
      (star (g p.1) * deriv (deriv g) p.1) *
        (star (h p.2) * h p.2)) := hA.mul_prod hB
  have hCD : Integrable (fun p : ℝ × ℝ =>
      (star (g p.1) * g p.1) *
        (star (h p.2) * deriv (deriv h) p.2)) := hC.mul_prod hD
  calc
    (∫ p : ℝ × ℝ, unweightedTensorForm g h p) =
        -((∫ p : ℝ × ℝ,
          (star (g p.1) * deriv (deriv g) p.1) *
            (star (h p.2) * h p.2)) +
          (∫ p : ℝ × ℝ,
          (star (g p.1) * g p.1) *
            (star (h p.2) * deriv (deriv h) p.2))) := by
      simp only [unweightedTensorForm]
      rw [integral_neg, integral_add hAB hCD]
    _ = -((∫ x : ℝ, star (g x) * deriv (deriv g) x) *
          (∫ y : ℝ, star (h y) * h y) +
        (∫ x : ℝ, star (g x) * g x) *
          (∫ y : ℝ, star (h y) * deriv (deriv h) y)) := by
      rw [integral_prod_mul, integral_prod_mul]
    _ = (tensorEnergy g h : ℂ) := by
      rw [integral_star_mul_secondDeriv g hg hgc,
        integral_star_mul_secondDeriv h hh hhc,
        integral_star_mul_self_eq_norm_sq (deriv g),
        integral_star_mul_self_eq_norm_sq h,
        integral_star_mul_self_eq_norm_sq g,
        integral_star_mul_self_eq_norm_sq (deriv h)]
      simp only [tensorEnergy]
      push_cast
      ring

/-- The full positive quadratic form for one compactly supported tensor
on the upper-half-plane chart. -/
theorem tensorHyperbolicLaplacian_energy_identity (g h : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hhpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    (∫ p : ℝ × ℝ,
      star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p
      ∂chartMeasure).re = tensorEnergy g h := by
  rw [chartTensorForm_integral_eq_unweighted g h hhpos,
    unweightedTensorForm_integral_eq_energy g h hg hh hgc hhc]
  simp

theorem tensorHyperbolicLaplacian_form_nonneg (g h : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hhpos : tsupport h ⊆ Set.Ioi (0 : ℝ)) :
    0 ≤ (∫ p : ℝ × ℝ,
      star (tensorFunction g h p) * tensorHyperbolicLaplacian g h p
      ∂chartMeasure).re := by
  rw [tensorHyperbolicLaplacian_energy_identity g h hg hh hgc hhc hhpos]
  unfold tensorEnergy
  apply add_nonneg
  · exact mul_nonneg (integral_nonneg fun x : ℝ => sq_nonneg (‖deriv g x‖))
      (integral_nonneg fun y : ℝ => sq_nonneg (‖h y‖))
  · exact mul_nonneg (integral_nonneg fun x : ℝ => sq_nonneg (‖g x‖))
      (integral_nonneg fun y : ℝ => sq_nonneg (‖deriv h y‖))

end

end ImbalancedChen.Part3.CompactComplexLaplacianForm20261024z
