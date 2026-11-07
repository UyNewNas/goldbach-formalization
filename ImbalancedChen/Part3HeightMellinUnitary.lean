import ImbalancedChen.Part3AngularFourierUnitary
import ImbalancedChen.Part3WeightedHeightNativeUnitary
import ImbalancedChen.Part3FourierL1L2Plancherel
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-!
# Literal height Mellin waves and forward/inverse angular Fourier formulas

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
The native height L2(dy/y^2) is mapped to the angular Fourier line by
f(y) -> Fourier[r -> exp(-r/2) f(exp r)](t/(2*pi)).
The physical generalized waves are sqrt(y)*exp(i*t*log y).
Only the full real t-line measure dt/(2*pi) occurs in the unitary here.
-/
namespace ImbalancedChen.Part3.HeightMellinUnitary20261026b
noncomputable section
open MeasureTheory FourierTransform
open scoped FourierTransform RealInnerProductSpace
open AngularFourierUnitary20261026b
open WeightedHeightNativeUnitary20261026a
open CuspCylinderMeasure20261024z
open FourierL1L2PlancherelSourceOnly

/-- The literal angular Fourier integral; no 2*pi is hidden in t. -/
def angularTransform (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ r : ℝ, Complex.exp (-Complex.I * (t : ℂ) * (r : ℂ)) * f r

/-- The inverse uses the literal positive wave and dt/(2*pi). -/
def angularInverse (g : ℝ → ℂ) (r : ℝ) : ℂ :=
  ∫ t, Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)) * g t ∂angularMeasure

theorem angularTransform_eq_fourier (f : ℝ → ℂ) (t : ℝ) :
    angularTransform f t = 𝓕 f (t / (2 * Real.pi)) := by
  rw [angularTransform, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with r
  have harg : ((↑(-2 * Real.pi * ⟪r, t / (2 * Real.pi)⟫_ℝ) : ℂ) * Complex.I) =
      -Complex.I * (t : ℂ) * (r : ℂ) := by
    rw [Real.inner_apply]
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  simp only [harg, smul_eq_mul]

theorem angularInverse_angularTransform_eq_fourierInv (f : ℝ → ℂ) (r : ℝ) :
    angularInverse (angularTransform f) r = 𝓕⁻ (𝓕 f) r := by
  unfold angularInverse
  rw [← angularCoordinate_integral]
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [angularTransform_eq_fourier]
  have hc : (2 * Real.pi * x) / (2 * Real.pi) = x := by
    field_simp [Real.pi_ne_zero]
  rw [hc]
  have harg : Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) * (r : ℂ) =
      ((↑(2 * Real.pi * ⟪x, r⟫_ℝ) : ℂ) * Complex.I) := by
    rw [Real.inner_apply]
    push_cast
    ring
  simp only [harg, smul_eq_mul]

/-- Genuine pointwise forward/inverse identity on Schwartz functions. -/
theorem angularInverse_angularTransform_schwartz (f : 𝓢(ℝ, ℂ)) (r : ℝ) :
    angularInverse (angularTransform f) r = f r := by
  rw [angularInverse_angularTransform_eq_fourierInv]
  change 𝓕⁻ (𝓕 (f : ℝ → ℂ)) r = f r
  rw [← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe,
    fourierInv_fourier_eq]

/-- L1∩L2 representatives of the genuine angular unitary are the literal
integrals, almost everywhere for the normalized angular measure. -/
theorem angularFourierUnitary_toLp_ae {f : ℝ → ℂ}
    (h₁ : Integrable f) (h₂ : MemLp f 2) :
    angularFourierUnitary (h₂.toLp f) =ᵐ[angularMeasure] angularTransform f := by
  have hF := angularCoordinate_symm_measurePreserving.quasiMeasurePreserving.ae
    (fourier_toLp_ae_eq h₁ h₂)
  filter_upwards [angularFourierUnitary_forward_ae (h₂.toLp f), hF] with t ht hFt
  rw [ht, angularTransform_eq_fourier]
  simpa only [angularCoordinate_symm_apply] using hFt

/-- Actual height Mellin unitary, including surjectivity for all L2 vectors. -/
def heightMellinUnitary : HeightL2 ≃ₗᵢ[ℂ] AngularL2 :=
  (weightedHeightUnitary 1 (by norm_num)).trans angularFourierUnitary

theorem heightMellinUnitary_inverse_forward (f : HeightL2) :
    heightMellinUnitary.symm (heightMellinUnitary f) = f :=
  heightMellinUnitary.symm_apply_apply f

theorem heightMellinUnitary_forward_inverse (g : AngularL2) :
    heightMellinUnitary (heightMellinUnitary.symm g) = g :=
  heightMellinUnitary.apply_symm_apply g

theorem heightMellinUnitary_inner (f g : HeightL2) :
    inner ℂ (heightMellinUnitary f) (heightMellinUnitary g) = inner ℂ f g :=
  heightMellinUnitary.inner_map_map f g

/-- The forward Mellin integral on the actual height logarithmic profile.
Only the genuine L1 domain condition is needed to identify the integral
representative; the unitary itself is defined on every height L2 vector. -/
theorem heightMellinUnitary_forward_ae (f : HeightL2)
    (h₁ : Integrable (heightToRadialFunction 1 (by norm_num) f)) :
    heightMellinUnitary f =ᵐ[angularMeasure]
      angularTransform (heightToRadialFunction 1 (by norm_num) f) := by
  exact angularFourierUnitary_toLp_ae h₁
    (heightToRadialFunction_memLp 1 (by norm_num) f)

/-- The inverse on all quotient vectors has the literal physical sqrt(y)
multiplier and log(y), with no additive phase from a scaled coordinate. -/
theorem heightMellinUnitary_inverse_ae (g : AngularL2) :
    heightMellinUnitary.symm g =ᵐ[heightMeasure]
      fun y : PositiveHeight => (Real.sqrt (y : ℝ) : ℂ) *
        (angularFourierUnitary.symm g) (Real.log (y : ℝ)) := by
  simpa only [one_mul] using weightedHeightUnitary_inverse_ae
    1 (by norm_num) (angularFourierUnitary.symm g)
/-- The physical zero-mode wave at the literal spectral parameter t. -/
def heightWave (t : ℝ) (y : PositiveHeight) : ℂ :=
  (Real.sqrt (y : ℝ) : ℂ) *
    Complex.exp (Complex.I * (t : ℂ) * (Real.log (y : ℝ) : ℂ))

/-- The height inverse multiplier is exactly sqrt(y) times the inverse
Fourier kernel. This is a generalized wave, not an L2 eigenvector. -/
theorem heightWave_eq_inverse_profile (t : ℝ) (y : PositiveHeight) :
    heightWave t y = radialToHeightFunction 1 (by norm_num)
      (fun r => Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))) y := by
  simp only [heightWave, radialToHeightFunction,
    WeightedHeightLogMeasure20261026a.scaledHeightEquiv_symm, one_mul]

end
end ImbalancedChen.Part3.HeightMellinUnitary20261026b

