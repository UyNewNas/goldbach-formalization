import ImbalancedChen.Part3GenericResolventScalarMeasure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Normed.Operator.Extend

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Genuine cyclic scalar-measure L² representation on every complex Hilbert
space for every bounded self-adjoint R. Complex CFC, mixed integral and norm
identities, quotient descent, dense isometric extension and surjectivity
onto the actual closed cyclic orbit are proved for the variable H,R,f.
No concrete realization, fixed-space alias or density/onto premise occurs.
-/

namespace ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

def complexOfReal (φ : C(ResolventSpectrum R, ℝ)) : C(ResolventSpectrum R, ℂ) :=
  ⟨fun t => (φ t : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩

def realPart (φ : C(ResolventSpectrum R, ℂ)) : C(ResolventSpectrum R, ℝ) :=
  ⟨fun t => (φ t).re, Complex.continuous_re.comp φ.continuous⟩

def imagPart (φ : C(ResolventSpectrum R, ℂ)) : C(ResolventSpectrum R, ℝ) :=
  ⟨fun t => (φ t).im, Complex.continuous_im.comp φ.continuous⟩

def complexResolventCFC : C(ResolventSpectrum R, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  (cfcHom (R := ℂ) hSA.isStarNormal).comp
    (Homeomorph.compStarAlgEquiv' ℂ ℂ hSA.spectrumRestricts.homeomorph).toStarAlgHom

theorem complexResolventCFC_ofReal (φ : C(ResolventSpectrum R, ℝ)) :
    complexResolventCFC R hSA (complexOfReal R φ) = resolventCFC R hSA φ := by
  unfold complexResolventCFC resolventCFC
  rw [cfcHom_real_eq_restrict]
  simp only [StarAlgHom.comp_apply, SpectrumRestricts.starAlgHom_apply]
  congr 1
  ext t
  rfl

theorem complex_decomposition (φ : C(ResolventSpectrum R, ℂ)) :
    φ = complexOfReal R (realPart R φ) + Complex.I • complexOfReal R (imagPart R φ) := by
  ext t
  apply Complex.ext <;> simp [complexOfReal, realPart, imagPart, Complex.mul_re, Complex.mul_im]

theorem complexResolventCFC_decomposition (φ : C(ResolventSpectrum R, ℂ)) :
    complexResolventCFC R hSA φ =
      resolventCFC R hSA (realPart R φ) + Complex.I • resolventCFC R hSA (imagPart R φ) := by
  rw [complex_decomposition R φ, map_add, map_smul,
    complexResolventCFC_ofReal, complexResolventCFC_ofReal]

theorem scalarMeasure_complexCFC_integral (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    (∫ t : ResolventSpectrum R, φ t ∂scalarMeasure R hSA f) =
      inner ℂ f ((complexResolventCFC R hSA φ) f) := by
  have hφ : Integrable φ (scalarMeasure R hSA f) :=
    φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace φ)
  have hpair : inner ℂ f ((complexResolventCFC R hSA φ) f) =
      inner ℂ f ((resolventCFC R hSA (realPart R φ)) f) +
        Complex.I * inner ℂ f ((resolventCFC R hSA (imagPart R φ)) f) := by
    rw [complexResolventCFC_decomposition, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right]
  apply Complex.ext
  · rw [← integral_re hφ, hpair]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      scalarCoefficient_im_zero, zero_mul, one_mul, sub_zero, add_zero]
    exact scalarMeasure_integral R hSA f (realPart R φ)
  · rw [← integral_im hφ, hpair]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      scalarCoefficient_im_zero, zero_mul, one_mul, zero_add, add_zero]
    exact scalarMeasure_integral R hSA f (imagPart R φ)

def continuousCyclicMap (f : H) : C(ResolventSpectrum R, ℂ) →ₗ[ℂ] H :=
  (ContinuousLinearMap.apply ℂ H f).toLinearMap.comp (complexResolventCFC R hSA).toLinearMap

theorem continuousCyclicMap_apply (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    continuousCyclicMap R hSA f φ = (complexResolventCFC R hSA φ) f := rfl

def coordinateComplex : C(ResolventSpectrum R, ℂ) := complexOfReal R (spectrumCoordinate R)

theorem complexResolventCFC_coordinate : complexResolventCFC R hSA (coordinateComplex R) = R := by
  rw [coordinateComplex, complexResolventCFC_ofReal, resolventCFC_coordinate]

theorem continuousCyclicMap_coordinate (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    continuousCyclicMap R hSA f (coordinateComplex R * φ) =
      R (continuousCyclicMap R hSA f φ) := by
  change (complexResolventCFC R hSA (coordinateComplex R * φ)) f =
    R ((complexResolventCFC R hSA φ) f)
  rw [map_mul, complexResolventCFC_coordinate]

theorem continuousCyclicMap_inner_integral (f : H) (φ ψ : C(ResolventSpectrum R, ℂ)) :
    inner ℂ (continuousCyclicMap R hSA f φ) (continuousCyclicMap R hSA f ψ) =
      ∫ t : ResolventSpectrum R, star (φ t) * ψ t ∂scalarMeasure R hSA f := by
  change inner ℂ ((complexResolventCFC R hSA φ) f) ((complexResolventCFC R hSA ψ) f) = _
  calc
    _ = inner ℂ f ((complexResolventCFC R hSA φ).adjoint
        ((complexResolventCFC R hSA ψ) f)) :=
      ((complexResolventCFC R hSA φ).adjoint_inner_right f
        ((complexResolventCFC R hSA ψ) f)).symm
    _ = inner ℂ f ((complexResolventCFC R hSA (star φ * ψ)) f) := by
      rw [map_mul, map_star, ContinuousLinearMap.star_eq_adjoint]
    _ = _ := by simpa using (scalarMeasure_complexCFC_integral R hSA f (star φ * ψ)).symm

private theorem complex_star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  calc
    star z * z = (Complex.normSq z : ℂ) := by
      simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := z)).symm
    _ = _ := by rw [Complex.normSq_eq_norm_sq]

theorem continuousCyclicMap_norm_sq_integral (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    ‖continuousCyclicMap R hSA f φ‖ ^ 2 =
      ∫ t : ResolventSpectrum R, ‖φ t‖ ^ 2 ∂scalarMeasure R hSA f := by
  have hi := continuousCyclicMap_inner_integral R hSA f φ φ
  simp_rw [complex_star_mul_self] at hi
  rw [integral_complex_ofReal] at hi
  simpa only [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re] using
    congrArg Complex.re hi

abbrev ScalarL2 (f : H) := Lp ℂ 2 (scalarMeasure R hSA f)

def spectralToLp (f : H) : C(ResolventSpectrum R, ℂ) →L[ℂ] ScalarL2 R hSA f :=
  ContinuousMap.toLp 2 (scalarMeasure R hSA f) ℂ

theorem spectralToLp_denseRange (f : H) : DenseRange (spectralToLp R hSA f) :=
  ContinuousMap.toLp_denseRange ℂ (scalarMeasure R hSA f) ℂ ENNReal.ofNat_ne_top

theorem continuousCyclicMap_inner_eq_L2 (f : H) (φ ψ : C(ResolventSpectrum R, ℂ)) :
    inner ℂ (continuousCyclicMap R hSA f φ) (continuousCyclicMap R hSA f ψ) =
      inner ℂ (spectralToLp R hSA f φ) (spectralToLp R hSA f ψ) := by
  rw [continuousCyclicMap_inner_integral, L2.inner_def]
  apply integral_congr_ae
  have hφ := φ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure R hSA f) (𝕜 := ℂ)
  have hψ := ψ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure R hSA f) (𝕜 := ℂ)
  filter_upwards [hφ, hψ] with t htφ htψ
  rw [htφ, htψ]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem continuousCyclicMap_norm_eq_L2 (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    ‖continuousCyclicMap R hSA f φ‖ = ‖spectralToLp R hSA f φ‖ := by
  have hinner := continuousCyclicMap_inner_eq_L2 R hSA f φ φ
  have hsq : ‖continuousCyclicMap R hSA f φ‖ ^ 2 = ‖spectralToLp R hSA f φ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  nlinarith [norm_nonneg (continuousCyclicMap R hSA f φ), norm_nonneg (spectralToLp R hSA f φ)]

def cyclicExtension (f : H) : ScalarL2 R hSA f →L[ℂ] H :=
  (continuousCyclicMap R hSA f).extendOfNorm (spectralToLp R hSA f).toLinearMap

private theorem continuousCyclicMap_bound (f : H) :
    ∀ φ, ‖continuousCyclicMap R hSA f φ‖ ≤ 1 * ‖spectralToLp R hSA f φ‖ := by
  intro φ
  rw [continuousCyclicMap_norm_eq_L2, one_mul]

theorem cyclicExtension_apply (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    cyclicExtension R hSA f (spectralToLp R hSA f φ) = continuousCyclicMap R hSA f φ :=
  LinearMap.extendOfNorm_eq (spectralToLp_denseRange R hSA f)
    ⟨1, continuousCyclicMap_bound R hSA f⟩ φ

theorem cyclicExtension_norm (f : H) (ξ : ScalarL2 R hSA f) :
    ‖cyclicExtension R hSA f ξ‖ = ‖ξ‖ := by
  have hcont : Continuous (fun η : ScalarL2 R hSA f => ‖cyclicExtension R hSA f η‖) :=
    continuous_norm.comp (cyclicExtension R hSA f).continuous
  have heq : (fun η : ScalarL2 R hSA f => ‖cyclicExtension R hSA f η‖) = (fun η => ‖η‖) := by
    apply hcont.ext_on
      (show Dense (Set.range (spectralToLp R hSA f)) from spectralToLp_denseRange R hSA f)
      continuous_norm
    rintro η ⟨φ, rfl⟩
    rw [cyclicExtension_apply]
    exact continuousCyclicMap_norm_eq_L2 R hSA f φ
  exact congrFun heq ξ

def cyclicIsometry (f : H) : ScalarL2 R hSA f →ₗᵢ[ℂ] H where
  toLinearMap := (cyclicExtension R hSA f).toLinearMap
  norm_map' := cyclicExtension_norm R hSA f

def cyclicSubspace (f : H) : Submodule ℂ H :=
  (LinearMap.range (continuousCyclicMap R hSA f)).topologicalClosure

theorem isClosed_cyclicSubspace (f : H) : IsClosed (cyclicSubspace R hSA f : Set H) :=
  (LinearMap.range (continuousCyclicMap R hSA f)).isClosed_topologicalClosure

theorem continuousCyclicMap_mem_cyclicSubspace (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    continuousCyclicMap R hSA f φ ∈ cyclicSubspace R hSA f :=
  (LinearMap.range (continuousCyclicMap R hSA f)).le_topologicalClosure ⟨φ, rfl⟩

theorem cyclicIsometry_range_eq (f : H) :
    (cyclicIsometry R hSA f).toLinearMap.range = cyclicSubspace R hSA f := by
  apply le_antisymm
  · rintro u ⟨ξ, rfl⟩
    have hclosed : IsClosed {η : ScalarL2 R hSA f |
        cyclicExtension R hSA f η ∈ cyclicSubspace R hSA f} :=
      (isClosed_cyclicSubspace R hSA f).preimage (cyclicExtension R hSA f).continuous
    have hsub : Set.range (spectralToLp R hSA f) ⊆ {η : ScalarL2 R hSA f |
        cyclicExtension R hSA f η ∈ cyclicSubspace R hSA f} := by
      rintro η ⟨φ, rfl⟩
      rw [cyclicExtension_apply]
      exact continuousCyclicMap_mem_cyclicSubspace R hSA f φ
    exact (closure_minimal hsub hclosed) (spectralToLp_denseRange R hSA f ξ)
  · apply (LinearMap.range (continuousCyclicMap R hSA f)).topologicalClosure_minimal
    · rintro u ⟨φ, rfl⟩
      exact ⟨spectralToLp R hSA f φ, cyclicExtension_apply R hSA f φ⟩
    · exact (cyclicIsometry R hSA f).isometry.isClosedEmbedding.isClosed_range

def cyclicIsometryToSubspace (f : H) : ScalarL2 R hSA f →ₗᵢ[ℂ] cyclicSubspace R hSA f where
  toLinearMap := (cyclicIsometry R hSA f).toLinearMap.codRestrict (cyclicSubspace R hSA f) (by
    intro ξ
    have h : cyclicIsometry R hSA f ξ ∈ (cyclicIsometry R hSA f).toLinearMap.range := ⟨ξ, rfl⟩
    rwa [cyclicIsometry_range_eq] at h)
  norm_map' := (cyclicIsometry R hSA f).norm_map

theorem cyclicIsometryToSubspace_surjective (f : H) :
    Function.Surjective (cyclicIsometryToSubspace R hSA f) := by
  intro u
  have hu : (u : H) ∈ (cyclicIsometry R hSA f).toLinearMap.range := by
    rw [cyclicIsometry_range_eq]
    exact u.property
  obtain ⟨ξ, hξ⟩ := hu
  refine ⟨ξ, ?_⟩
  apply Subtype.ext
  exact hξ

def cyclicRepresentation (f : H) : ScalarL2 R hSA f ≃ₗᵢ[ℂ] cyclicSubspace R hSA f :=
  LinearIsometryEquiv.ofSurjective (cyclicIsometryToSubspace R hSA f)
    (cyclicIsometryToSubspace_surjective R hSA f)

theorem cyclicRepresentation_continuous (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    (cyclicRepresentation R hSA f (spectralToLp R hSA f φ) : H) =
      continuousCyclicMap R hSA f φ := cyclicExtension_apply R hSA f φ

end

end ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
