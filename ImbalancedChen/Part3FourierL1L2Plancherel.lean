import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
SOURCEONLY / UNCOMPILED, 2026-10-24.
The integral Fourier transform of an L1 ∩ L2 function is identified almost
everywhere with Mathlib's L2 Fourier isometry. No Plancherel identity or
compatibility identity is assumed. The identification uses distributional
uniqueness and the genuine Mathlib Fourier pairing theorem.
-/

noncomputable section

namespace ImbalancedChen.Part3.FourierL1L2PlancherelSourceOnly

open MeasureTheory SchwartzMap FourierTransform
open scoped FourierTransform SchwartzMap RealInnerProductSpace ComplexInnerProductSpace

/-- The Fubini identity with only one Schwartz factor. -/
theorem integral_schwartz_fourier_mul (g : 𝓢(ℝ, ℂ))
    {f : ℝ → ℂ} (hf : Integrable f) :
    (∫ x : ℝ, 𝓕 g x * f x) = ∫ x : ℝ, g x * 𝓕 f x := by
  simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
    g.integrable hf

/-- Distributional uniqueness supplies the missing compatibility between
the Bochner-integral Fourier transform and Mathlib's L2 Fourier transform. -/
theorem fourier_toLp_ae_eq {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    ((𝓕 (h₂.toLp f) : Lp ℂ 2) : ℝ → ℂ) =ᵐ[volume] 𝓕 f := by
  let F : Lp ℂ 2 := 𝓕 (h₂.toLp f)
  have hcont : Continuous (𝓕 f) := by
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ h₁
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp F).locallyIntegrable (by norm_num)) hcont.locallyIntegrable
  intro g hg hc
  have hc' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hc.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let G : 𝓢(ℝ, ℂ) := hc'.toSchwartzMap hg'
  have hdist := congrArg (fun T : 𝓢'(ℝ, ℂ) => T G)
    (Lp.fourier_toTemperedDistribution_eq (h₂.toLp f))
  have hpair : (∫ x : ℝ, G x * F x) = ∫ x : ℝ, 𝓕 G x * f x := by
    calc
      _ = ∫ x : ℝ, 𝓕 G x * h₂.toLp f x := by
        simpa only [TemperedDistribution.fourier_apply,
          Lp.toTemperedDistribution_apply, smul_eq_mul, F] using hdist.symm
      _ = _ := integral_congr_ae (by
        filter_upwards [h₂.coeFn_toLp] with x hx
        rw [hx])
  have hpair' := hpair.trans (integral_schwartz_fourier_mul G h₁)
  simpa [G, Complex.real_smul] using hpair'

/-- In particular the integral Fourier transform is square integrable. -/
theorem memLp_fourier {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) : MemLp (𝓕 f) 2 := by
  exact (memLp_congr_ae (fourier_toLp_ae_eq h₁ h₂)).1
    (Lp.memLp (𝓕 (h₂.toLp f)))

/-- Conversion from the Hilbert-space norm to the integral square norm. -/
theorem integral_norm_sq_lp (f : Lp (α := ℝ) ℂ 2) :
    (∫ x : ℝ, ‖f x‖ ^ 2) = ‖f‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    (L2.inner_def (𝕜 := ℂ) f f).symm

/-- Plancherel for the actual Bochner-integral Fourier transform, proved
from Mathlib's Fourier isometry rather than assumed as a premise. -/
theorem integral_norm_sq_fourier {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) = ∫ u : ℝ, ‖f u‖ ^ 2 := by
  calc
    _ = ∫ ξ : ℝ, ‖(𝓕 (h₂.toLp f) : Lp ℂ 2) ξ‖ ^ 2 :=
      integral_congr_ae (by
        filter_upwards [fourier_toLp_ae_eq h₁ h₂] with ξ hξ
        rw [hξ])
    _ = ‖𝓕 (h₂.toLp f)‖ ^ 2 := integral_norm_sq_lp _
    _ = ‖h₂.toLp f‖ ^ 2 := by rw [Lp.norm_fourier_eq]
    _ = ∫ u : ℝ, ‖h₂.toLp f u‖ ^ 2 := (integral_norm_sq_lp _).symm
    _ = _ := integral_congr_ae (by
      filter_upwards [h₂.coeFn_toLp] with u hu
      rw [hu])

/-- Exact rescaling for the frequency convention cos(2tu): the associated
half-transform is one half of the ordinary Fourier transform at t/π. -/
theorem integral_norm_sq_half_rescaled_fourier {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    (∫ t : ℝ, ‖(1 / 2 : ℂ) * 𝓕 f (t / Real.pi)‖ ^ 2) =
      (Real.pi / 4) * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  calc
    _ = (1 / 4 : ℝ) * ∫ t : ℝ, ‖𝓕 f (t / Real.pi)‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, mul_pow]
      ring
    _ = (1 / 4 : ℝ) * (Real.pi * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) := by
      rw [Measure.integral_comp_div]
      simp [abs_of_pos Real.pi_pos]
    _ = _ := by rw [integral_norm_sq_fourier h₁ h₂]; ring

theorem integrable_norm_sq_half_rescaled_fourier {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    Integrable (fun t : ℝ => ‖(1 / 2 : ℂ) * 𝓕 f (t / Real.pi)‖ ^ 2) := by
  have hF := memLp_fourier h₁ h₂
  have hs : Integrable (fun ξ : ℝ => ‖𝓕 f ξ‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).1 hF
  have hscaled := (hs.comp_div Real.pi_ne_zero).const_mul (1 / 4 : ℝ)
  refine hscaled.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat, mul_pow]
  ring

/-- A stable Schwartz specialization, independent of any profile supplier. -/
theorem schwartz_integral_norm_sq_half_rescaled_fourier (f : 𝓢(ℝ, ℂ)) :
    (∫ t : ℝ, ‖(1 / 2 : ℂ) * 𝓕 (f : ℝ → ℂ) (t / Real.pi)‖ ^ 2) =
      (Real.pi / 4) * ∫ u : ℝ, ‖f u‖ ^ 2 := by
  calc
    _ = (1 / 4 : ℝ) * ∫ t : ℝ, ‖𝓕 f (t / Real.pi)‖ ^ 2 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp only [SchwartzMap.fourier_coe, norm_mul, norm_div, norm_one,
        Complex.norm_ofNat, mul_pow]
      ring
    _ = (1 / 4 : ℝ) * (Real.pi * ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2) := by
      rw [Measure.integral_comp_div]
      simp [abs_of_pos Real.pi_pos]
    _ = _ := by rw [SchwartzMap.integral_norm_sq_fourier]; ring

end ImbalancedChen.Part3.FourierL1L2PlancherelSourceOnly
