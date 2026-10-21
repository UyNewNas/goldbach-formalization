import Mathlib.Analysis.Distribution.FourierMultiplier
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A quantitative fourth-order Schwartz Fourier L1 estimate

The Fourier convention is the native kernel `exp (-2 * pi * I * inner x xi)`.
Accordingly, the normalized second-order operator is
`D = Id - ((2 * pi)^2)⁻¹ * Delta`, and the fourth-order operator is `D ∘ D`.
Its actual Fourier symbol is `(1 + norm xi^2)^2`.

In real dimension strictly less than eight, the reciprocal symbol is in L2.
Quantitative Holder and the native Schwartz Plancherel theorem therefore give
a constant chosen before every Schwartz function. No Sobolev norm estimate,
Fourier-symbol identity or quantitative target bound is supplied as a premise.
-/

namespace ImbalancedChen.Part3.SchwartzFourierL1Sobolev

noncomputable section

open MeasureTheory FourierTransform Laplacian
open scoped SchwartzMap FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual normalized second-order differential operator. The coefficient
matches the native Fourier convention, including its full `2 * pi` factor. -/
def normalizedStep (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  f - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • Δ f

/-- The actual fourth-order differential operator `(Id - (2*pi)^(-2) Delta)^2`. -/
def normalizedFourth (f : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  normalizedStep (normalizedStep f)

private theorem fourier_laplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (Δ f) ξ = (-(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) • 𝓕 f ξ := by
  rw [SchwartzMap.laplacian_eq_fourierMultiplierCLM,
    FourierTransform.fourier_smul, SchwartzMap.fourierMultiplierCLM_apply,
    FourierTransform.fourier_fourierInv_eq]
  change (-(2 * Real.pi) ^ 2) •
      (SchwartzMap.smulLeftCLM ℂ (fun x : E ↦ ‖x‖ ^ 2) (𝓕 f) ξ) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (Function.hasTemperateGrowth_norm_sq E), smul_smul]

private theorem fourier_normalizedStep_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (normalizedStep f) ξ = (1 + ‖ξ‖ ^ 2) • 𝓕 f ξ := by
  have hlin : 𝓕 (normalizedStep f) =
      𝓕 f - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • 𝓕 (Δ f) := by
    simp only [normalizedStep, sub_eq_add_neg, FourierTransform.fourier_add,
      FourierTransform.fourier_neg, FourierTransform.fourier_smul]
  rw [hlin]
  change 𝓕 f ξ - (((2 * Real.pi) ^ 2)⁻¹ : ℝ) • 𝓕 (Δ f) ξ = _
  rw [fourier_laplacian_apply, smul_smul]
  have hpi : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  have hcoef : ((2 * Real.pi) ^ 2)⁻¹ *
      (-(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) = -(‖ξ‖ ^ 2) := by
    calc
      ((2 * Real.pi) ^ 2)⁻¹ * (-(2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) =
          -((((2 * Real.pi) ^ 2)⁻¹ * (2 * Real.pi) ^ 2) * ‖ξ‖ ^ 2) := by ring
      _ = -(‖ξ‖ ^ 2) := by rw [inv_mul_cancel₀ hpi, one_mul]
  rw [hcoef, neg_smul, sub_neg_eq_add, add_smul, one_smul]

private theorem fourier_normalizedFourth_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (normalizedFourth f) ξ = (1 + ‖ξ‖ ^ 2) ^ 2 • 𝓕 f ξ := by
  rw [normalizedFourth, fourier_normalizedStep_apply,
    fourier_normalizedStep_apply, smul_smul, ← pow_two]

private def inverseSymbol (ξ : E) : ℝ := ((1 + ‖ξ‖ ^ 2) ^ 2)⁻¹

private theorem inverseSymbol_nonneg (ξ : E) : 0 ≤ inverseSymbol ξ := by
  unfold inverseSymbol
  positivity

private theorem inverseSymbol_continuous : Continuous (inverseSymbol : E → ℝ) := by
  unfold inverseSymbol
  exact ((continuous_const.add (continuous_norm.pow 2)).pow 2).inv₀
    (fun ξ ↦ by positivity)

private theorem inverseSymbol_sq_eq (ξ : E) :
    inverseSymbol ξ ^ 2 = (1 + ‖ξ‖ ^ 2) ^ (-(8 : ℝ) / 2) := by
  have he : -(8 : ℝ) / 2 = -(4 : ℝ) := by norm_num
  rw [he]
  norm_num only [inverseSymbol, Real.rpow_neg_ofNat, zpow_neg, zpow_natCast,
    ← inv_pow, ← pow_mul]

private theorem inverseSymbol_sq_integrable
    (hd : Module.finrank ℝ E < 8) :
    Integrable (fun ξ : E ↦ inverseSymbol ξ ^ 2) := by
  have hdim : (Module.finrank ℝ E : ℝ) < 8 := by exact_mod_cast hd
  have h := integrable_rpow_neg_one_add_norm_sq (μ := (volume : Measure E)) hdim
  simpa only [← inverseSymbol_sq_eq] using h

private theorem inverseSymbol_memLp (hd : Module.finrank ℝ E < 8) :
    MemLp (inverseSymbol : E → ℝ) 2 :=
  (memLp_two_iff_integrable_sq inverseSymbol_continuous.aestronglyMeasurable).2
    (inverseSymbol_sq_integrable hd)

private theorem inverseSymbol_mul_fourier_norm (f : 𝓢(E, ℂ)) (ξ : E) :
    inverseSymbol ξ * ‖𝓕 (normalizedFourth f) ξ‖ = ‖𝓕 f ξ‖ := by
  rw [fourier_normalizedFourth_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (1 + ‖ξ‖ ^ 2))]
  unfold inverseSymbol
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

private theorem fourier_integral_norm_le_explicit
    (hd : Module.finrank ℝ E < 8) (f : 𝓢(E, ℂ)) :
    (∫ ξ : E, ‖𝓕 f ξ‖) ≤
      Real.sqrt (∫ ξ : E, inverseSymbol ξ ^ 2) *
        Real.sqrt (∫ x : E, ‖normalizedFourth f x‖ ^ 2) := by
  have hk : MemLp (inverseSymbol : E → ℝ) (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using inverseSymbol_memLp hd
  have hF : MemLp (fun ξ : E ↦ ‖𝓕 (normalizedFourth f) ξ‖)
      (ENNReal.ofReal (2 : ℝ)) := by
    simpa only [ENNReal.ofReal_ofNat] using ((𝓕 (normalizedFourth f)).memLp 2).norm
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (inverseSymbol_nonneg (E := E)))
    (Filter.Eventually.of_forall (fun ξ : E ↦ norm_nonneg (𝓕 (normalizedFourth f) ξ)))
    hk hF
  have hHolder_sqrt :
      (∫ ξ : E, inverseSymbol ξ * ‖𝓕 (normalizedFourth f) ξ‖) ≤
        Real.sqrt (∫ ξ : E, inverseSymbol ξ ^ 2) *
          Real.sqrt (∫ ξ : E, ‖𝓕 (normalizedFourth f) ξ‖ ^ 2) := by
    simpa only [Real.rpow_ofNat, ← Real.sqrt_eq_rpow] using hHolder
  calc
    (∫ ξ : E, ‖𝓕 f ξ‖) =
        ∫ ξ : E, inverseSymbol ξ * ‖𝓕 (normalizedFourth f) ξ‖ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ξ ↦ (inverseSymbol_mul_fourier_norm f ξ).symm)
    _ ≤ Real.sqrt (∫ ξ : E, inverseSymbol ξ ^ 2) *
        Real.sqrt (∫ ξ : E, ‖𝓕 (normalizedFourth f) ξ‖ ^ 2) := hHolder_sqrt
    _ = Real.sqrt (∫ ξ : E, inverseSymbol ξ ^ 2) *
        Real.sqrt (∫ x : E, ‖normalizedFourth f x‖ ^ 2) := by
      rw [SchwartzMap.integral_norm_sq_fourier]

/-- A quantitative fourth-order Fourier L1 estimate in every real dimension
strictly below eight. The constant depends only on the fixed domain and is
chosen before all Schwartz functions. Both integrals use native volume. -/
theorem fourier_integral_norm_le_normalizedFourth
    (hd : Module.finrank ℝ E < 8) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : 𝓢(E, ℂ),
      (∫ ξ : E, ‖𝓕 f ξ‖) ≤
        C * Real.sqrt (∫ x : E, ‖normalizedFourth f x‖ ^ 2) := by
  refine ⟨1 + Real.sqrt (∫ ξ : E, inverseSymbol ξ ^ 2), by positivity, ?_⟩
  intro f
  exact (fourier_integral_norm_le_explicit hd f).trans
    (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))

end

end ImbalancedChen.Part3.SchwartzFourierL1Sobolev
