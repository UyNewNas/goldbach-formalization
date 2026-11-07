import ImbalancedChen.Part3GenericResolventCyclicL2Representation

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
Actual coordinate multiplication and cyclic intertwining for every bounded
self-adjoint operator on every complex Hilbert space. The coordinate
multiplier is defined on the genuine scalar-measure L² quotient, with
literal pointwise representatives and bound ‖R‖. No positivity, contraction,
separability, density or spectral-representation premise is needed.
-/

namespace ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericResolventCyclicL2Representation20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

theorem coordinateComplex_norm_le (t : ResolventSpectrum R) :
    ‖coordinateComplex R t‖ ≤ ‖R‖ := by
  change ‖((t : ℝ) : ℂ)‖ ≤ ‖R‖
  rw [Complex.norm_real]
  calc
    _ ≤ ‖R‖ * ‖(1 : H →L[ℂ] H)‖ := spectrum.norm_le_norm_mul_of_mem t.property
    _ ≤ ‖R‖ * 1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg R)
    _ = _ := mul_one _

private theorem coordinateMultiply_memLp (f : H) (ξ : ScalarL2 R hSA f) :
    MemLp (fun t : ResolventSpectrum R => coordinateComplex R t * ξ t) 2
      (scalarMeasure R hSA f) := by
  apply (Lp.memLp ξ).of_le_mul
    ((coordinateComplex R).continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable ξ))
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (coordinateComplex_norm_le R t) (norm_nonneg _)

def coordinateMultiply (f : H) (ξ : ScalarL2 R hSA f) : ScalarL2 R hSA f :=
  (coordinateMultiply_memLp R hSA f ξ).toLp (fun t => coordinateComplex R t * ξ t)

theorem coordinateMultiply_coe_ae (f : H) (ξ : ScalarL2 R hSA f) :
    coordinateMultiply R hSA f ξ =ᵐ[scalarMeasure R hSA f]
      (fun t => coordinateComplex R t * ξ t) :=
  (coordinateMultiply_memLp R hSA f ξ).coeFn_toLp

def coordinateMultiplyLinear (f : H) : ScalarL2 R hSA f →ₗ[ℂ] ScalarL2 R hSA f where
  toFun := coordinateMultiply R hSA f
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [coordinateMultiply_coe_ae R hSA f (ξ + η), Lp.coeFn_add ξ η,
      Lp.coeFn_add (coordinateMultiply R hSA f ξ) (coordinateMultiply R hSA f η),
      coordinateMultiply_coe_ae R hSA f ξ, coordinateMultiply_coe_ae R hSA f η]
        with t hleft hin hright hξ hη
    rw [hleft, hright, hξ, hη, hin]
    ring
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [coordinateMultiply_coe_ae R hSA f (c • ξ), Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (coordinateMultiply R hSA f ξ), coordinateMultiply_coe_ae R hSA f ξ]
        with t hleft hin hright hξ
    rw [hleft, hright, hξ, hin]
    simp only [smul_eq_mul]
    ring

theorem coordinateMultiply_norm_le (f : H) (ξ : ScalarL2 R hSA f) :
    ‖coordinateMultiply R hSA f ξ‖ ≤ ‖R‖ * ‖ξ‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coordinateMultiply_coe_ae R hSA f ξ] with t ht
  rw [ht, norm_mul]
  exact mul_le_mul_of_nonneg_right (coordinateComplex_norm_le R t) (norm_nonneg _)

def coordinateMultiplier (f : H) : ScalarL2 R hSA f →L[ℂ] ScalarL2 R hSA f :=
  (coordinateMultiplyLinear R hSA f).mkContinuous ‖R‖ (coordinateMultiply_norm_le R hSA f)

theorem coordinateMultiplier_norm_le (f : H) (ξ : ScalarL2 R hSA f) :
    ‖coordinateMultiplier R hSA f ξ‖ ≤ ‖R‖ * ‖ξ‖ :=
  coordinateMultiply_norm_le R hSA f ξ

theorem coordinateMultiplier_opNorm_le (f : H) : ‖coordinateMultiplier R hSA f‖ ≤ ‖R‖ :=
  (coordinateMultiplier R hSA f).opNorm_le_bound (norm_nonneg R)
    (coordinateMultiplier_norm_le R hSA f)

theorem coordinateMultiplier_contraction (hnorm : ‖R‖ ≤ 1) (f : H) (ξ : ScalarL2 R hSA f) :
    ‖coordinateMultiplier R hSA f ξ‖ ≤ ‖ξ‖ := by
  calc
    _ ≤ ‖R‖ * ‖ξ‖ := coordinateMultiplier_norm_le R hSA f ξ
    _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg ξ)
    _ = _ := one_mul _

theorem coordinateMultiplier_coe_ae (f : H) (ξ : ScalarL2 R hSA f) :
    coordinateMultiplier R hSA f ξ =ᵐ[scalarMeasure R hSA f]
      (fun t : ResolventSpectrum R => ((t : ℝ) : ℂ) * ξ t) :=
  coordinateMultiply_coe_ae R hSA f ξ

theorem coordinateMultiplier_spectralToLp (f : H) (φ : C(ResolventSpectrum R, ℂ)) :
    coordinateMultiplier R hSA f (spectralToLp R hSA f φ) =
      spectralToLp R hSA f (coordinateComplex R * φ) := by
  apply Lp.ext
  have hφ := φ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure R hSA f) (𝕜 := ℂ)
  have hprod := (coordinateComplex R * φ).coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := scalarMeasure R hSA f) (𝕜 := ℂ)
  filter_upwards [coordinateMultiply_coe_ae R hSA f (spectralToLp R hSA f φ), hφ, hprod]
      with t hm htφ htprod
  simpa only [htφ, htprod] using hm

theorem cyclicExtension_intertwine (f : H) (ξ : ScalarL2 R hSA f) :
    cyclicExtension R hSA f (coordinateMultiplier R hSA f ξ) =
      R (cyclicExtension R hSA f ξ) := by
  have hcont : Continuous (fun η : ScalarL2 R hSA f =>
      cyclicExtension R hSA f (coordinateMultiplier R hSA f η)) :=
    (cyclicExtension R hSA f).continuous.comp (coordinateMultiplier R hSA f).continuous
  have heq : (fun η : ScalarL2 R hSA f =>
      cyclicExtension R hSA f (coordinateMultiplier R hSA f η)) =
      (fun η => R (cyclicExtension R hSA f η)) := by
    apply hcont.ext_on
      (show Dense (Set.range (spectralToLp R hSA f)) from spectralToLp_denseRange R hSA f)
      (R.continuous.comp (cyclicExtension R hSA f).continuous)
    rintro η ⟨φ, rfl⟩
    rw [coordinateMultiplier_spectralToLp, cyclicExtension_apply,
      continuousCyclicMap_coordinate, cyclicExtension_apply]
  exact congrFun heq ξ

theorem cyclicRepresentation_intertwine (f : H) (ξ : ScalarL2 R hSA f) :
    (cyclicRepresentation R hSA f (coordinateMultiplier R hSA f ξ) : H) =
      R (cyclicRepresentation R hSA f ξ : H) :=
  cyclicExtension_intertwine R hSA f ξ

end

end ImbalancedChen.Part3.GenericResolventCyclicIntertwining20261025a
