import ImbalancedChen.Part3GenericResolventGlobalSpectralAssembly

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Every continuous complex CFC function is actual multiplication in the global
scalar spectral coordinates. The proof uses CFC multiplicativity on the dense
continuous-function image, then continuity in the L2 vector. In particular it
does not infer arbitrary-function conjugacy from coordinate-only conjugacy.
The final theorem supplies literal continuous-test scalar-measure identities.
Borel measure uniqueness and the identification of all-set effects remain separate.
-/

namespace ImbalancedChen.Part3.GenericGlobalContinuousCFC20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a
open ImbalancedChen.Part3.GenericResolventGlobalSpectralAssembly20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

private theorem multiply_memLp (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) :
    MemLp (fun t => φ t * ξ t) 2 (scalarMeasure R hSA f) := by
  apply (Lp.memLp ξ).of_le_mul
    (φ.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable ξ))
  exact Filter.Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)

def multiply (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) : ScalarL2 R hSA f :=
  (multiply_memLp R hSA f φ ξ).toLp (fun t => φ t * ξ t)

theorem multiply_coe_ae (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) :
    multiply R hSA f φ ξ =ᵐ[scalarMeasure R hSA f] (fun t => φ t * ξ t) :=
  (multiply_memLp R hSA f φ ξ).coeFn_toLp

def multiplyLinear (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    ScalarL2 R hSA f →ₗ[ℂ] ScalarL2 R hSA f where
  toFun := multiply R hSA f φ
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [multiply_coe_ae R hSA f φ (ξ + η), Lp.coeFn_add ξ η,
      Lp.coeFn_add (multiply R hSA f φ ξ) (multiply R hSA f φ η),
      multiply_coe_ae R hSA f φ ξ, multiply_coe_ae R hSA f φ η]
        with t hleft hin hright hξ hη
    rw [hleft, hright, hξ, hη, hin]
    ring
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [multiply_coe_ae R hSA f φ (c • ξ), Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (multiply R hSA f φ ξ), multiply_coe_ae R hSA f φ ξ]
        with t hleft hin hright hξ
    rw [hleft, hright, hξ, hin]
    simp only [smul_eq_mul]
    ring

theorem multiply_norm_le (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) : ‖multiply R hSA f φ ξ‖ ≤ ‖φ‖ * ‖ξ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiply_coe_ae R hSA f φ ξ] with t ht
  rw [ht, norm_mul]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)

def continuousMultiplier (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    ScalarL2 R hSA f →L[ℂ] ScalarL2 R hSA f :=
  (multiplyLinear R hSA f φ).mkContinuous ‖φ‖ (multiply_norm_le R hSA f φ)

theorem continuousMultiplier_opNorm_le (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    ‖continuousMultiplier R hSA f φ‖ ≤ ‖φ‖ :=
  (continuousMultiplier R hSA f φ).opNorm_le_bound (norm_nonneg φ)
    (multiply_norm_le R hSA f φ)

theorem continuousMultiplier_coe_ae (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) :
    continuousMultiplier R hSA f φ ξ =ᵐ[scalarMeasure R hSA f]
      (fun t => φ t * ξ t) := multiply_coe_ae R hSA f φ ξ

theorem continuousMultiplier_spectralToLp (f : H)
    (φ ψ : C(ResolventSpectrum R, ℂ)) :
    continuousMultiplier R hSA f φ (spectralToLp R hSA f ψ) =
      spectralToLp R hSA f (φ * ψ) := by
  apply Lp.ext
  have hψ := ψ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure R hSA f) (𝕜 := ℂ)
  have hprod := (φ * ψ).coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := scalarMeasure R hSA f) (𝕜 := ℂ)
  filter_upwards [multiply_coe_ae R hSA f φ (spectralToLp R hSA f ψ), hψ, hprod]
      with t hm htψ htprod
  simpa only [htψ, htprod] using hm

theorem continuousCyclicMap_mul (f : H) (φ ψ : C(ResolventSpectrum R, ℂ)) :
    continuousCyclicMap R hSA f (φ * ψ) =
      (complexResolventCFC R hSA φ) (continuousCyclicMap R hSA f ψ) := by
  change (complexResolventCFC R hSA (φ * ψ)) f =
    (complexResolventCFC R hSA φ) ((complexResolventCFC R hSA ψ) f)
  rw [map_mul]
  rfl

/-- Extension is in the L2 vector; no approximation or convergence premise
about the CFC function is required. Multiplicativity already covers every φ. -/
theorem cyclicExtension_intertwine_CFC (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) :
    cyclicExtension R hSA f (continuousMultiplier R hSA f φ ξ) =
      (complexResolventCFC R hSA φ) (cyclicExtension R hSA f ξ) := by
  have hcont : Continuous (fun η : ScalarL2 R hSA f =>
      cyclicExtension R hSA f (continuousMultiplier R hSA f φ η)) :=
    (cyclicExtension R hSA f).continuous.comp (continuousMultiplier R hSA f φ).continuous
  have heq : (fun η : ScalarL2 R hSA f =>
      cyclicExtension R hSA f (continuousMultiplier R hSA f φ η)) =
      (fun η => (complexResolventCFC R hSA φ) (cyclicExtension R hSA f η)) := by
    apply hcont.ext_on
      (show Dense (Set.range (spectralToLp R hSA f)) from spectralToLp_denseRange R hSA f)
      ((complexResolventCFC R hSA φ).continuous.comp (cyclicExtension R hSA f).continuous)
    rintro η ⟨ψ, rfl⟩
    rw [continuousMultiplier_spectralToLp, cyclicExtension_apply,
      continuousCyclicMap_mul, cyclicExtension_apply]
  exact congrFun heq ξ

def diagonalContinuous (φ : C(ResolventSpectrum R, ℂ)) :
    SpectralSum R hSA →L[ℂ] SpectralSum R hSA :=
  lp.mapCLM 2 (fun i : SpectralIndex R hSA => continuousMultiplier R hSA (i : H) φ)
    (norm_nonneg φ) (fun i => continuousMultiplier_opNorm_le R hSA (i : H) φ)

theorem diagonalContinuous_apply (φ : C(ResolventSpectrum R, ℂ))
    (ξ : SpectralSum R hSA) (i : SpectralIndex R hSA) :
    diagonalContinuous R hSA φ ξ i = continuousMultiplier R hSA (i : H) φ (ξ i) := rfl

theorem diagonalContinuous_opNorm_le (φ : C(ResolventSpectrum R, ℂ)) :
    ‖diagonalContinuous R hSA φ‖ ≤ ‖φ‖ :=
  lp.norm_mapCLM_le 2
    (fun i : SpectralIndex R hSA => continuousMultiplier R hSA (i : H) φ)
    (norm_nonneg φ) (fun i => continuousMultiplier_opNorm_le R hSA (i : H) φ)

theorem spectralUnitary_intertwine_CFC (φ : C(ResolventSpectrum R, ℂ))
    (ξ : SpectralSum R hSA) :
    spectralUnitary R hSA (diagonalContinuous R hSA φ ξ) =
      (complexResolventCFC R hSA φ) (spectralUnitary R hSA ξ) := by
  have hleft := spectralUnitary_hasSum R hSA (diagonalContinuous R hSA φ ξ)
  have hright := (complexResolventCFC R hSA φ).hasSum (spectralUnitary_hasSum R hSA ξ)
  have hterms : (fun i : SpectralIndex R hSA =>
      fiberEmbedding R hSA i (diagonalContinuous R hSA φ ξ i)) =
      (fun i : SpectralIndex R hSA =>
        (complexResolventCFC R hSA φ) (fiberEmbedding R hSA i (ξ i))) := by
    funext i
    exact cyclicExtension_intertwine_CFC R hSA (i : H) φ (ξ i)
  rw [hterms] at hleft
  exact hleft.unique hright

theorem CFC_spectral_coordinates (φ : C(ResolventSpectrum R, ℂ)) (u : H) :
    (spectralUnitary R hSA).symm ((complexResolventCFC R hSA φ) u) =
      diagonalContinuous R hSA φ ((spectralUnitary R hSA).symm u) := by
  apply (spectralUnitary R hSA).injective
  rw [(spectralUnitary R hSA).apply_symm_apply, spectralUnitary_intertwine_CFC,
    (spectralUnitary R hSA).apply_symm_apply]

theorem CFC_unitary_conjugacy (φ : C(ResolventSpectrum R, ℂ)) :
    complexResolventCFC R hSA φ =
      (spectralUnitary R hSA).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((diagonalContinuous R hSA φ).comp
          (spectralUnitary R hSA).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  ext u
  change (complexResolventCFC R hSA φ) u =
    spectralUnitary R hSA (diagonalContinuous R hSA φ ((spectralUnitary R hSA).symm u))
  rw [spectralUnitary_intertwine_CFC, (spectralUnitary R hSA).apply_symm_apply]

private theorem star_mul_self (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  calc
    star z * z = (Complex.normSq z : ℂ) := by
      simpa only [Complex.star_def] using (Complex.normSq_eq_conj_mul_self (z := z)).symm
    _ = _ := by rw [Complex.normSq_eq_norm_sq]

theorem continuousMultiplier_inner (f : H) (φ : C(ResolventSpectrum R, ℂ))
    (ξ : ScalarL2 R hSA f) :
    inner ℂ ξ (continuousMultiplier R hSA f φ ξ) =
      ∫ t, φ t * ((‖ξ t‖ ^ 2 : ℝ) : ℂ) ∂scalarMeasure R hSA f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [continuousMultiplier_coe_ae R hSA f φ ξ] with t ht
  rw [ht, RCLike.inner_apply']
  calc
    _ = φ t * (star (ξ t) * ξ t) := by ring
    _ = _ := by rw [star_mul_self]

/-- Actual RMK continuous tests equal the fiberwise weighted integrals.
This is the missing CFC input for finite-regular-measure uniqueness. -/
theorem scalarMeasure_continuous_test_sum (u : H) (φ : C(ResolventSpectrum R, ℂ)) :
    (∫ t, φ t ∂scalarMeasure R hSA u) =
      ∑' i : SpectralIndex R hSA,
        ∫ t, φ t * ((‖((spectralUnitary R hSA).symm u i) t‖ ^ 2 : ℝ) : ℂ)
          ∂scalarMeasure R hSA (i : H) := by
  rw [scalarMeasure_complexCFC_integral]
  have hinner := (spectralUnitary R hSA).symm.inner_map_map
    u ((complexResolventCFC R hSA φ) u)
  rw [CFC_spectral_coordinates] at hinner
  rw [← hinner, lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  exact continuousMultiplier_inner R hSA (i : H) φ ((spectralUnitary R hSA).symm u i)

end
end ImbalancedChen.Part3.GenericGlobalContinuousCFC20261025a