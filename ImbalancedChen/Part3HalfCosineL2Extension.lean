import ImbalancedChen.Part3EvenL1L2Density
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The actual raw half-cosine transform extends to all even L2 classes. Its
squared norm is pi/4 times the full-line input squared norm. The factor
2/sqrt(pi) normalizes it to a linear isometry. No Plancherel premise is used.
-/

noncomputable section

namespace ImbalancedChen.Part3.HalfCosineL2ExtensionSourceOnly

open MeasureTheory SchwartzMap FourierTransform
open scoped SchwartzMap FourierTransform
open EvenFourierHilbertSourceOnly EvenL1L2DensitySourceOnly
open FourierL1L2PlancherelSourceOnly HalfCosinePlancherelSourceOnly

private theorem divPi_quasiMeasurePreserving :
    QuasiMeasurePreserving (fun t : ℝ => t / Real.pi) volume volume := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
      (inv_ne_zero Real.pi_ne_zero))

private theorem dilation_memLp (f : ComplexL2) :
    MemLp (fun t : ℝ => f (t / Real.pi)) 2 := by
  have hm := (Lp.memLp f).aestronglyMeasurable.comp_quasiMeasurePreserving
    divPi_quasiMeasurePreserving
  apply (memLp_two_iff_integrable_sq_norm hm).2
  exact ((memLp_two_iff_integrable_sq_norm
    (Lp.memLp f).aestronglyMeasurable).1 (Lp.memLp f)).comp_div Real.pi_ne_zero

/-- Genuine raw-frequency dilation on the quotient L2 space. -/
def dilation (f : ComplexL2) : ComplexL2 :=
  (dilation_memLp f).toLp (fun t : ℝ => f (t / Real.pi))

theorem dilation_coe (f : ComplexL2) :
    (dilation f : ℝ → ℂ) =ᵐ[volume] fun t : ℝ => f (t / Real.pi) :=
  (dilation_memLp f).coeFn_toLp

private theorem dilation_add (f g : ComplexL2) :
    dilation (f + g) = dilation f + dilation g := by
  apply Lp.ext
  filter_upwards [dilation_coe (f + g), dilation_coe f, dilation_coe g,
    divPi_quasiMeasurePreserving.ae_eq (Lp.coeFn_add f g),
    Lp.coeFn_add (dilation f) (dilation g)] with t ht hf hg hfg hsum
  change (f + g) (t / Real.pi) = f (t / Real.pi) + g (t / Real.pi) at hfg
  change (dilation f + dilation g) t = dilation f t + dilation g t at hsum
  rw [ht, hfg, hsum, hf, hg]

private theorem dilation_smul (c : ℂ) (f : ComplexL2) :
    dilation (c • f) = c • dilation f := by
  apply Lp.ext
  filter_upwards [dilation_coe (c • f), dilation_coe f,
    divPi_quasiMeasurePreserving.ae_eq (Lp.coeFn_smul c f),
    Lp.coeFn_smul c (dilation f)] with t ht hf hcf hsmul
  change (c • f) (t / Real.pi) = c • f (t / Real.pi) at hcf
  change (c • dilation f) t = c • dilation f t at hsmul
  rw [ht, hcf, hsmul, hf]

/-- The Jacobian is pi for the substitution t = pi*xi. -/
theorem dilation_norm_sq (f : ComplexL2) :
    ‖dilation f‖ ^ 2 = Real.pi * ‖f‖ ^ 2 := by
  calc
    _ = ∫ t : ℝ, ‖dilation f t‖ ^ 2 := (integral_norm_sq_lp _).symm
    _ = ∫ t : ℝ, ‖f (t / Real.pi)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [dilation_coe f] with t ht
      rw [ht]
    _ = Real.pi * ∫ t : ℝ, ‖f t‖ ^ 2 := by
      rw [Measure.integral_comp_div]
      simp [abs_of_pos Real.pi_pos]
    _ = _ := by rw [integral_norm_sq_lp]

theorem dilation_norm (f : ComplexL2) :
    ‖dilation f‖ = Real.sqrt Real.pi * ‖f‖ := by
  have hs : (Real.sqrt Real.pi * ‖f‖) ^ 2 = Real.pi * ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt Real.pi_pos.le]
  have hnonneg : 0 ≤ Real.sqrt Real.pi * ‖f‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [dilation_norm_sq f, norm_nonneg (dilation f)]

private def dilationLinear : ComplexL2 →ₗ[ℂ] ComplexL2 where
  toFun := dilation
  map_add' := dilation_add
  map_smul' := dilation_smul

/-- Bounded linear dilation, constructed from the preceding exact norm. -/
def dilationCLM : ComplexL2 →L[ℂ] ComplexL2 :=
  dilationLinear.mkContinuous (Real.sqrt Real.pi) (fun f => (dilation_norm f).le)

/-- The half-cosine extension, with raw order t and phase cos(2*t*u). -/
def rawHalfCosine : evenL2 →L[ℂ] ComplexL2 :=
  (1 / 2 : ℂ) • dilationCLM.comp
    (evenL2.subtypeL.comp evenFourier.toLinearIsometry.toContinuousLinearMap)

theorem rawHalfCosine_apply (f : evenL2) :
    rawHalfCosine f = (1 / 2 : ℂ) • dilation (evenFourier f : ComplexL2) := by
  rfl

/-- Exact raw dt normalization for every even L2 class, not only packets. -/
theorem rawHalfCosine_norm_sq (f : evenL2) :
    ‖rawHalfCosine f‖ ^ 2 = (Real.pi / 4) * ‖f‖ ^ 2 := by
  rw [rawHalfCosine_apply, norm_smul, mul_pow, dilation_norm_sq]
  have hnorm : ‖(evenFourier f : ComplexL2)‖ = ‖f‖ := evenFourier.norm_map f
  rw [hnorm]
  norm_num [norm_div] <;> ring

/-- Compatibility with the actual integral on the dense L1-intersect-L2
pointwise-even domain. The equality is one of actual representatives a.e. -/
theorem rawHalfCosine_toLp_ae {f : ℝ → ℂ} (h₁ : Integrable f)
    (h₂ : MemLp f 2) (heven : ∀ x : ℝ, f (-x) = f x) :
    (rawHalfCosine ⟨h₂.toLp f, toLp_mem_evenL2 h₂ heven⟩ : ℝ → ℂ)
      =ᵐ[volume] halfCosineTransform f := by
  let v : evenL2 := ⟨h₂.toLp f, toLp_mem_evenL2 h₂ heven⟩
  have hF : ((evenFourier v : ComplexL2) : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
    fourier_toLp_ae_eq h₁ h₂
  have hscaled := divPi_quasiMeasurePreserving.ae_eq hF
  change (rawHalfCosine v : ℝ → ℂ) =ᵐ[volume] halfCosineTransform f
  rw [rawHalfCosine_apply]
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ)
    (dilation (evenFourier v : ComplexL2)),
    dilation_coe (evenFourier v : ComplexL2), hscaled] with t ht hd hft
  change (evenFourier v : ComplexL2) (t / Real.pi) = 𝓕 f (t / Real.pi) at hft
  change ((1 / 2 : ℂ) • dilation (evenFourier v : ComplexL2)) t =
    (1 / 2 : ℂ) • dilation (evenFourier v : ComplexL2) t at ht
  rw [ht, hd, hft, smul_eq_mul,
    halfCosineTransform_eq_half_fourier h₁ heven]

/-- Normalization by 2/sqrt(pi), against the full-line input L2 norm. -/
def normalizedHalfCosineCLM : evenL2 →L[ℂ] ComplexL2 :=
  ((2 / Real.sqrt Real.pi : ℝ) : ℂ) • rawHalfCosine

theorem normalizedHalfCosine_norm_sq (f : evenL2) :
    ‖normalizedHalfCosineCLM f‖ ^ 2 = ‖f‖ ^ 2 := by
  change ‖((2 / Real.sqrt Real.pi : ℝ) : ℂ) • rawHalfCosine f‖ ^ 2 = _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    sq_abs, div_pow, rawHalfCosine_norm_sq,
    Real.sq_sqrt Real.pi_pos.le]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- A bounded linear isometric extension of the normalized actual integral. -/
def normalizedHalfCosine : evenL2 →ₗᵢ[ℂ] ComplexL2 where
  toLinearMap := normalizedHalfCosineCLM.toLinearMap
  norm_map' f := by
    have hs := normalizedHalfCosine_norm_sq f
    nlinarith [norm_nonneg (normalizedHalfCosineCLM f), norm_nonneg f]

/-- Density makes the bounded extension unique. It suffices to fix its
values on the explicit symmetrized Schwartz family. -/
theorem rawHalfCosine_unique (T : evenL2 →L[ℂ] ComplexL2)
    (hT : ∀ g : 𝓢(ℝ, ℂ),
      T (evenSchwartzEmbedding g) = rawHalfCosine (evenSchwartzEmbedding g)) :
    T = rawHalfCosine := by
  ext f
  apply DenseRange.induction_on (p := fun v : evenL2 => T v = rawHalfCosine v)
    denseRange_evenSchwartzEmbedding f
  · exact isClosed_eq T.continuous rawHalfCosine.continuous
  · exact hT

end ImbalancedChen.Part3.HalfCosineL2ExtensionSourceOnly
