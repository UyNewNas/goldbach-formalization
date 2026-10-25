import ImbalancedChen.Part3ActualResolventCyclicL2Representation

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
The genuine bounded coordinate multiplier on the actual scalar-measure L²
space, defined by pointwise multiplication on representatives and descended
through the actual quotient. The actual cyclic representation intertwines
this multiplier and the actual energy resolvent, by true continuous L²
density. No multiplier, density or spectral-representation premise is used.
-/

namespace ImbalancedChen.Part3.ActualResolventCyclicIntertwining20261025a

noncomputable section

open MeasureTheory
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualResolventContinuousCyclic20261025a
open ImbalancedChen.Part3.ActualResolventCyclicL2Representation20261025a

theorem coordinateComplex_norm_le (t : ResolventSpectrum) : ‖coordinateComplex t‖ ≤ 1 := by
  have ht := spectrum_coordinate_mem_unitInterval t
  change ‖((t : ℝ) : ℂ)‖ ≤ 1
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

private theorem coordinateMultiply_memLp (f : HyperbolicL2) (ξ : ScalarL2 f) :
    MemLp (fun t : ResolventSpectrum => coordinateComplex t * ξ t) 2 (scalarMeasure f) := by
  apply (Lp.memLp ξ).of_le
    (coordinateComplex.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable ξ))
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖ξ t‖ := mul_le_mul_of_nonneg_right (coordinateComplex_norm_le t) (norm_nonneg _)
    _ = _ := one_mul _

def coordinateMultiply (f : HyperbolicL2) (ξ : ScalarL2 f) : ScalarL2 f :=
  (coordinateMultiply_memLp f ξ).toLp (fun t => coordinateComplex t * ξ t)

theorem coordinateMultiply_coe_ae (f : HyperbolicL2) (ξ : ScalarL2 f) :
    coordinateMultiply f ξ =ᵐ[scalarMeasure f] (fun t => coordinateComplex t * ξ t) :=
  (coordinateMultiply_memLp f ξ).coeFn_toLp

def coordinateMultiplyLinear (f : HyperbolicL2) : ScalarL2 f →ₗ[ℂ] ScalarL2 f where
  toFun := coordinateMultiply f
  map_add' ξ η := by
    apply Lp.ext
    filter_upwards [coordinateMultiply_coe_ae f (ξ + η), Lp.coeFn_add ξ η,
      Lp.coeFn_add (coordinateMultiply f ξ) (coordinateMultiply f η),
      coordinateMultiply_coe_ae f ξ, coordinateMultiply_coe_ae f η]
        with t hleft hin hright hξ hη
    rw [hleft, hright, hξ, hη, hin]
    ring
  map_smul' c ξ := by
    apply Lp.ext
    filter_upwards [coordinateMultiply_coe_ae f (c • ξ), Lp.coeFn_smul c ξ,
      Lp.coeFn_smul c (coordinateMultiply f ξ), coordinateMultiply_coe_ae f ξ]
        with t hleft hin hright hξ
    rw [hleft, hright, hξ, hin]
    simp only [smul_eq_mul]
    ring

theorem coordinateMultiply_norm_le (f : HyperbolicL2) (ξ : ScalarL2 f) :
    ‖coordinateMultiply f ξ‖ ≤ ‖ξ‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coordinateMultiply_coe_ae f ξ] with t ht
  rw [ht, norm_mul]
  calc
    _ ≤ 1 * ‖ξ t‖ := mul_le_mul_of_nonneg_right (coordinateComplex_norm_le t) (norm_nonneg _)
    _ = _ := one_mul _

/-- The actual bounded coordinate multiplier, with the genuine
pointwise multiplication formula on scalar-measure L² representatives. -/
def coordinateMultiplier (f : HyperbolicL2) : ScalarL2 f →L[ℂ] ScalarL2 f :=
  (coordinateMultiplyLinear f).mkContinuous 1 (by
    intro ξ
    simpa only [one_mul] using coordinateMultiply_norm_le f ξ)

theorem coordinateMultiplier_norm_le (f : HyperbolicL2) (ξ : ScalarL2 f) :
    ‖coordinateMultiplier f ξ‖ ≤ ‖ξ‖ :=
  coordinateMultiply_norm_le f ξ

theorem coordinateMultiplier_opNorm_le_one (f : HyperbolicL2) : ‖coordinateMultiplier f‖ ≤ 1 := by
  apply (coordinateMultiplier f).opNorm_le_bound zero_le_one
  intro ξ
  simpa only [one_mul] using coordinateMultiplier_norm_le f ξ

theorem coordinateMultiplier_coe_ae (f : HyperbolicL2) (ξ : ScalarL2 f) :
    coordinateMultiplier f ξ =ᵐ[scalarMeasure f] (fun t : ResolventSpectrum => (t : ℂ) * ξ t) :=
  coordinateMultiply_coe_ae f ξ

theorem coordinateMultiplier_spectralToLp (f : HyperbolicL2)
    (φ : C(ResolventSpectrum, ℂ)) :
    coordinateMultiplier f (spectralToLp f φ) = spectralToLp f (coordinateComplex * φ) := by
  apply Lp.ext
  have hφ := φ.coeFn_toLp (p := (2 : ℝ≥0∞)) (μ := scalarMeasure f) (𝕜 := ℂ)
  have hprod := (coordinateComplex * φ).coeFn_toLp
    (p := (2 : ℝ≥0∞)) (μ := scalarMeasure f) (𝕜 := ℂ)
  filter_upwards [coordinateMultiply_coe_ae f (spectralToLp f φ), hφ, hprod]
      with t hm htφ htprod
  simpa only [htφ, htprod] using hm

/-- The actual isometric extension intertwines the genuine scalar
coordinate multiplier and the actual bounded energy resolvent. -/
theorem cyclicExtension_intertwine (f : HyperbolicL2) (ξ : ScalarL2 f) :
    cyclicExtension f (coordinateMultiplier f ξ) =
      actualWeakResolvent (cyclicExtension f ξ) := by
  have hcont : Continuous (fun η : ScalarL2 f =>
      cyclicExtension f (coordinateMultiplier f η)) :=
    (cyclicExtension f).continuous.comp (coordinateMultiplier f).continuous
  have heq : (fun η : ScalarL2 f => cyclicExtension f (coordinateMultiplier f η)) =
      (fun η => actualWeakResolvent (cyclicExtension f η)) := by
    apply hcont.ext_on
      (show Dense (Set.range (spectralToLp f)) from spectralToLp_denseRange f)
      (actualWeakResolvent.continuous.comp (cyclicExtension f).continuous)
    rintro η ⟨φ, rfl⟩
    rw [coordinateMultiplier_spectralToLp, cyclicExtension_apply,
      continuousCyclicMap_coordinate, cyclicExtension_apply]
  exact congrFun heq ξ

/-- Genuine cyclic spectral representation of the actual resolvent:
the actual L² coordinate multiplier is conjugate to the actual operator
on the proved closed cyclic orbit. -/
theorem cyclicRepresentation_intertwine (f : HyperbolicL2) (ξ : ScalarL2 f) :
    (cyclicRepresentation f (coordinateMultiplier f ξ) : HyperbolicL2) =
      actualWeakResolvent (cyclicRepresentation f ξ : HyperbolicL2) :=
  cyclicExtension_intertwine f ξ

end

end ImbalancedChen.Part3.ActualResolventCyclicIntertwining20261025a
