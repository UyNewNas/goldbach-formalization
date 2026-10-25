import ImbalancedChen.Part3GenericResolventGlobalSpectralAssembly

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Every continuous complex function on the real resolvent spectrum gives
literal bounded multiplication on each true scalar spectral L2. Its
cyclic embedding intertwines multiplication with the complex CFC on
ALL L2 vectors, by the genuine continuous-core density. Uniform bounds
then give multiplication on the existing global Hilbert sum, and the
existing onto spectral unitary intertwines it with the full physical
CFC. No density, unitary or intertwining supplier is assumed here.
-/

namespace ImbalancedChen.Part3.GenericResolventContinuousMultipliers20261025a

noncomputable section
open MeasureTheory
open GenericResolventScalarMeasure20261025a
open GenericResolventCyclicL2Representation20261025a
open GenericResolventGlobalSpectralAssembly20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H→L[ℂ]H) (hSA : IsSelfAdjoint R)

theorem continuousMultiply_memLp (φ : C(ResolventSpectrum R,ℂ))
    (f : H) (g : ScalarL2 R hSA f) :
    MemLp (fun t => φ t*g t) 2 (scalarMeasure R hSA f) := by
  apply (Lp.memLp g).of_le_mul (φ.continuous.aestronglyMeasurable.mul
    (Lp.aestronglyMeasurable g))
  exact Filter.Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)

def continuousMultiply (φ : C(ResolventSpectrum R,ℂ)) (f : H)
    (g : ScalarL2 R hSA f) : ScalarL2 R hSA f :=
  (continuousMultiply_memLp R hSA φ f g).toLp (fun t => φ t*g t)

theorem continuousMultiply_coe_ae (φ : C(ResolventSpectrum R,ℂ)) (f : H)
    (g : ScalarL2 R hSA f) :
    continuousMultiply R hSA φ f g=ᵐ[scalarMeasure R hSA f] (fun t => φ t*g t) :=
  (continuousMultiply_memLp R hSA φ f g).coeFn_toLp

def continuousMultiplyLinear (φ : C(ResolventSpectrum R,ℂ)) (f : H) :
    ScalarL2 R hSA f→ₗ[ℂ]ScalarL2 R hSA f where
  toFun := continuousMultiply R hSA φ f
  map_add' g h := by
    apply Lp.ext
    filter_upwards [continuousMultiply_coe_ae R hSA φ f (g+h),Lp.coeFn_add g h,
      Lp.coeFn_add (continuousMultiply R hSA φ f g) (continuousMultiply R hSA φ f h),
      continuousMultiply_coe_ae R hSA φ f g,continuousMultiply_coe_ae R hSA φ f h]
      with t hleft hin hright hg hh
    rw [hleft,hright,hg,hh,hin]
    ring
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [continuousMultiply_coe_ae R hSA φ f (c•g),Lp.coeFn_smul c g,
      Lp.coeFn_smul c (continuousMultiply R hSA φ f g),continuousMultiply_coe_ae R hSA φ f g]
      with t hleft hin hright hg
    rw [hleft,hright,hg,hin]
    simp only [smul_eq_mul]
    ring

theorem continuousMultiply_norm_le (φ : C(ResolventSpectrum R,ℂ)) (f : H)
    (g : ScalarL2 R hSA f) :
    ‖continuousMultiply R hSA φ f g‖≤‖φ‖*‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [continuousMultiply_coe_ae R hSA φ f g] with t ht
  rw [ht,norm_mul]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)

def continuousMultiplier (φ : C(ResolventSpectrum R,ℂ)) (f : H) :
    ScalarL2 R hSA f→L[ℂ]ScalarL2 R hSA f :=
  (continuousMultiplyLinear R hSA φ f).mkContinuous ‖φ‖
    (continuousMultiply_norm_le R hSA φ f)

theorem continuousMultiplier_opNorm_le (φ : C(ResolventSpectrum R,ℂ)) (f : H) :
    ‖continuousMultiplier R hSA φ f‖≤‖φ‖ :=
  (continuousMultiplier R hSA φ f).opNorm_le_bound (norm_nonneg φ)
    (continuousMultiply_norm_le R hSA φ f)

theorem continuousMultiplier_coe_ae (φ : C(ResolventSpectrum R,ℂ)) (f : H)
    (g : ScalarL2 R hSA f) :
    continuousMultiplier R hSA φ f g=ᵐ[scalarMeasure R hSA f] (fun t => φ t*g t) :=
  continuousMultiply_coe_ae R hSA φ f g

theorem continuousMultiplier_spectralToLp (φ ψ : C(ResolventSpectrum R,ℂ)) (f : H) :
    continuousMultiplier R hSA φ f (spectralToLp R hSA f ψ)=
      spectralToLp R hSA f (φ*ψ) := by
  apply Lp.ext
  have hψ := ψ.coeFn_toLp (p:=(2:ℝ≥0∞)) (μ:=scalarMeasure R hSA f) (𝕜:=ℂ)
  have hprod := (φ*ψ).coeFn_toLp (p:=(2:ℝ≥0∞)) (μ:=scalarMeasure R hSA f) (𝕜:=ℂ)
  filter_upwards [continuousMultiplier_coe_ae R hSA φ f (spectralToLp R hSA f ψ),hψ,hprod]
    with t hm hψt hprodt
  simpa only [hψt,hprodt] using hm

/-- Product compatibility on the genuine continuous cyclic core. -/
theorem continuousCyclicMap_multiply (φ ψ : C(ResolventSpectrum R,ℂ)) (f : H) :
    continuousCyclicMap R hSA f (φ*ψ)=
      complexResolventCFC R hSA φ (continuousCyclicMap R hSA f ψ) := by
  change complexResolventCFC R hSA (φ*ψ) f=
    complexResolventCFC R hSA φ (complexResolventCFC R hSA ψ f)
  rw [map_mul]
  rfl

/-- Full scalar-L2 intertwining, not merely an identity on C functions.
The density input is the supplier's already proved continuous L2 core. -/
theorem cyclicExtension_continuous_intertwine (φ : C(ResolventSpectrum R,ℂ))
    (f : H) (g : ScalarL2 R hSA f) :
    cyclicExtension R hSA f (continuousMultiplier R hSA φ f g)=
      complexResolventCFC R hSA φ (cyclicExtension R hSA f g) := by
  have hcont : Continuous (fun η : ScalarL2 R hSA f =>
      cyclicExtension R hSA f (continuousMultiplier R hSA φ f η)) :=
    (cyclicExtension R hSA f).continuous.comp (continuousMultiplier R hSA φ f).continuous
  have heq : (fun η : ScalarL2 R hSA f =>
      cyclicExtension R hSA f (continuousMultiplier R hSA φ f η))=
      (fun η => complexResolventCFC R hSA φ (cyclicExtension R hSA f η)) := by
    apply hcont.ext_on (show Dense (Set.range (spectralToLp R hSA f)) from
      spectralToLp_denseRange R hSA f)
      ((complexResolventCFC R hSA φ).continuous.comp (cyclicExtension R hSA f).continuous)
    rintro η ⟨ψ,rfl⟩
    rw [continuousMultiplier_spectralToLp,cyclicExtension_apply,
      continuousCyclicMap_multiply,cyclicExtension_apply]
  exact congrFun heq g

def diagonalContinuousMultiplier (φ : C(ResolventSpectrum R,ℂ)) :
    SpectralSum R hSA→L[ℂ]SpectralSum R hSA :=
  lp.mapCLM 2 (fun i : SpectralIndex R hSA => continuousMultiplier R hSA φ (i:H))
    (norm_nonneg φ) (fun i => continuousMultiplier_opNorm_le R hSA φ (i:H))

theorem diagonalContinuousMultiplier_apply (φ : C(ResolventSpectrum R,ℂ))
    (g : SpectralSum R hSA) (i : SpectralIndex R hSA) :
    diagonalContinuousMultiplier R hSA φ g i=continuousMultiplier R hSA φ (i:H) (g i) := rfl

theorem diagonalContinuousMultiplier_opNorm_le (φ : C(ResolventSpectrum R,ℂ)) :
    ‖diagonalContinuousMultiplier R hSA φ‖≤‖φ‖ :=
  lp.norm_mapCLM_le 2 (fun i : SpectralIndex R hSA => continuousMultiplier R hSA φ (i:H))
    (norm_nonneg φ) (fun i => continuousMultiplier_opNorm_le R hSA φ (i:H))

/-- Full physical-H intertwining through the EXISTING onto global
spectral unitary. Both sums converge by the true Hilbert-sum supplier. -/
theorem spectralUnitary_continuous_intertwine (φ : C(ResolventSpectrum R,ℂ))
    (g : SpectralSum R hSA) :
    spectralUnitary R hSA (diagonalContinuousMultiplier R hSA φ g)=
      complexResolventCFC R hSA φ (spectralUnitary R hSA g) := by
  have hleft := spectralUnitary_hasSum R hSA (diagonalContinuousMultiplier R hSA φ g)
  have hright := (complexResolventCFC R hSA φ).hasSum (spectralUnitary_hasSum R hSA g)
  have hterms : (fun i : SpectralIndex R hSA =>
      fiberEmbedding R hSA i (diagonalContinuousMultiplier R hSA φ g i))=
      (fun i : SpectralIndex R hSA =>
        complexResolventCFC R hSA φ (fiberEmbedding R hSA i (g i))) := by
    funext i
    exact cyclicExtension_continuous_intertwine R hSA φ (i:H) (g i)
  rw [hterms] at hleft
  exact hleft.unique hright

theorem cfc_spectral_coordinates (φ : C(ResolventSpectrum R,ℂ)) (f : H) :
    (spectralUnitary R hSA).symm (complexResolventCFC R hSA φ f)=
      diagonalContinuousMultiplier R hSA φ ((spectralUnitary R hSA).symm f) := by
  apply (spectralUnitary R hSA).injective
  rw [LinearIsometryEquiv.apply_symm_apply,spectralUnitary_continuous_intertwine,
    LinearIsometryEquiv.apply_symm_apply]

end
end ImbalancedChen.Part3.GenericResolventContinuousMultipliers20261025a
