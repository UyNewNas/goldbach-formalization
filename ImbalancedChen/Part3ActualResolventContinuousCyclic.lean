import ImbalancedChen.Part3ActualResolventScalarMeasure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Genuine complex continuous cyclic calculus on the actual real resolvent
spectrum, with its exact scalar-measure inner-product and squared-norm
identities. Complex CFC is transported along the actual real/complex
spectrum homeomorphism and is proved to restrict to the previous real CFC.
No norm, measure or density supplier is assumed.
-/

namespace ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a

def complexOfReal (φ : C(ResolventSpectrum, ℝ)) : C(ResolventSpectrum, ℂ) :=
  ⟨fun t => (φ t : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩

def realPart (φ : C(ResolventSpectrum, ℂ)) : C(ResolventSpectrum, ℝ) :=
  ⟨fun t => (φ t).re, Complex.continuous_re.comp φ.continuous⟩

def imagPart (φ : C(ResolventSpectrum, ℂ)) : C(ResolventSpectrum, ℝ) :=
  ⟨fun t => (φ t).im, Complex.continuous_im.comp φ.continuous⟩

/-- Actual complex CFC, transported from the complex spectrum to the
actual real spectrum of the actual self-adjoint energy resolvent. -/
def complexResolventCFC : C(ResolventSpectrum, ℂ) →⋆ₐ[ℂ] ResolventAlgebra :=
  (cfcHom (R := ℂ) actualWeakResolvent_selfAdjoint.isStarNormal).comp
    (Homeomorph.compStarAlgEquiv' ℂ ℂ
      actualWeakResolvent_selfAdjoint.spectrumRestricts.homeomorph).toStarAlgHom

theorem complexResolventCFC_ofReal (φ : C(ResolventSpectrum, ℝ)) :
    complexResolventCFC (complexOfReal φ) = resolventCFC φ := by
  unfold complexResolventCFC resolventCFC
  rw [cfcHom_real_eq_restrict]
  simp only [StarAlgHom.comp_apply, SpectrumRestricts.starAlgHom_apply]
  congr 1
  ext t
  rfl

theorem complex_decomposition (φ : C(ResolventSpectrum, ℂ)) :
    φ = complexOfReal (realPart φ) + Complex.I • complexOfReal (imagPart φ) := by
  ext t
  apply Complex.ext <;> simp [complexOfReal, realPart, imagPart, Complex.mul_re, Complex.mul_im]

theorem complexResolventCFC_decomposition (φ : C(ResolventSpectrum, ℂ)) :
    complexResolventCFC φ = resolventCFC (realPart φ) + Complex.I • resolventCFC (imagPart φ) := by
  rw [complex_decomposition φ, map_add, map_smul,
    complexResolventCFC_ofReal, complexResolventCFC_ofReal]

/-- Genuine complex scalar integral representation, derived from the
constructed real RMK measure and the actual complex CFC. -/
theorem scalarMeasure_complexCFC_integral (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℂ)) :
    (∫ t : ResolventSpectrum, φ t ∂scalarMeasure f) =
      inner ℂ f ((complexResolventCFC φ) f) := by
  have hφ : Integrable φ (scalarMeasure f) :=
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
  have hpair : inner ℂ f ((complexResolventCFC φ) f) =
      inner ℂ f ((resolventCFC (realPart φ)) f) +
        Complex.I * inner ℂ f ((resolventCFC (imagPart φ)) f) := by
    rw [complexResolventCFC_decomposition, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right]
  apply Complex.ext
  · rw [← integral_re hφ, hpair]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      scalarCoefficient_im_zero, zero_mul, one_mul, sub_zero, add_zero]
    exact scalarMeasure_integral f (realPart φ)
  · rw [← integral_im hφ, hpair]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      scalarCoefficient_im_zero, zero_mul, one_mul, zero_add, add_zero]
    exact scalarMeasure_integral f (imagPart φ)

def continuousCyclicMap (f : HyperbolicL2) : C(ResolventSpectrum, ℂ) →ₗ[ℂ] HyperbolicL2 :=
  (ContinuousLinearMap.apply ℂ HyperbolicL2 f).toLinearMap.comp complexResolventCFC.toLinearMap

theorem continuousCyclicMap_apply (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℂ)) :
    continuousCyclicMap f φ = (complexResolventCFC φ) f := rfl

def coordinateComplex : C(ResolventSpectrum, ℂ) := complexOfReal spectrumCoordinate

theorem complexResolventCFC_coordinate : complexResolventCFC coordinateComplex = actualWeakResolvent := by
  rw [coordinateComplex, complexResolventCFC_ofReal, resolventCFC_coordinate]

theorem continuousCyclicMap_coordinate (f : HyperbolicL2) (φ : C(ResolventSpectrum, ℂ)) :
    continuousCyclicMap f (coordinateComplex * φ) =
      actualWeakResolvent (continuousCyclicMap f φ) := by
  change (complexResolventCFC (coordinateComplex * φ)) f =
    actualWeakResolvent ((complexResolventCFC φ) f)
  rw [map_mul, complexResolventCFC_coordinate]

/-- Exact mixed cyclic inner product, not merely a diagonal norm identity. -/
theorem continuousCyclicMap_inner_integral (f : HyperbolicL2)
    (φ ψ : C(ResolventSpectrum, ℂ)) :
    inner ℂ (continuousCyclicMap f φ) (continuousCyclicMap f ψ) =
      ∫ t : ResolventSpectrum, star (φ t) * ψ t ∂scalarMeasure f := by
  change inner ℂ ((complexResolventCFC φ) f) ((complexResolventCFC ψ) f) = _
  calc
    _ = inner ℂ f ((complexResolventCFC φ).adjoint ((complexResolventCFC ψ) f)) :=
      ((complexResolventCFC φ).adjoint_inner_right f ((complexResolventCFC ψ) f)).symm
    _ = inner ℂ f ((complexResolventCFC (star φ * ψ)) f) := by
      rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
    _ = _ := by simpa using (scalarMeasure_complexCFC_integral f (star φ * ψ)).symm

private theorem complex_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  calc
    star z * z = (Complex.normSq z : ℂ) := by
      simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := z)).symm
    _ = _ := by rw [Complex.normSq_eq_norm_sq]

theorem continuousCyclicMap_norm_sq_integral (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℂ)) :
    ‖continuousCyclicMap f φ‖ ^ 2 =
      ∫ t : ResolventSpectrum, ‖φ t‖ ^ 2 ∂scalarMeasure f := by
  have hi := continuousCyclicMap_inner_integral f φ φ
  simp_rw [complex_star_mul_self] at hi
  rw [integral_complex_ofReal] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re] using
    congrArg Complex.re hi

abbrev ScalarL2 (f : HyperbolicL2) := Lp ℂ 2 (scalarMeasure f)

def spectralToLp (f : HyperbolicL2) : C(ResolventSpectrum, ℂ) →L[ℂ] ScalarL2 f :=
  ContinuousMap.toLp 2 (scalarMeasure f) ℂ

theorem spectralToLp_denseRange (f : HyperbolicL2) : DenseRange (spectralToLp f) :=
  ContinuousMap.toLp_denseRange ℂ (scalarMeasure f) ℂ ENNReal.ofNat_ne_top

theorem continuousCyclicMap_inner_eq_L2 (f : HyperbolicL2)
    (φ ψ : C(ResolventSpectrum, ℂ)) :
    inner ℂ (continuousCyclicMap f φ) (continuousCyclicMap f ψ) =
      inner ℂ (spectralToLp f φ) (spectralToLp f ψ) := by
  rw [continuousCyclicMap_inner_integral, L2.inner_def]
  apply integral_congr_ae
  have hφ := φ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure f) (𝕜 := ℂ)
  have hψ := ψ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure f) (𝕜 := ℂ)
  filter_upwards [hφ, hψ] with t htφ htψ
  rw [htφ, htψ]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem continuousCyclicMap_norm_eq_L2 (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℂ)) :
    ‖continuousCyclicMap f φ‖ = ‖spectralToLp f φ‖ := by
  have hinner := continuousCyclicMap_inner_eq_L2 f φ φ
  have hsq : ‖continuousCyclicMap f φ‖ ^ 2 = ‖spectralToLp f φ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  nlinarith [norm_nonneg (continuousCyclicMap f φ), norm_nonneg (spectralToLp f φ)]

end

end ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a
