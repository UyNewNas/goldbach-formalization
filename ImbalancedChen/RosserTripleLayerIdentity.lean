import ImbalancedChen.RosserTripleMeshIntegral
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserBoundarySourceSuccLayer

/-!
# Identification of the actual three-prime continuous boundary layer

Extracting the least coordinate and applying Fubini identifies the genuine
three-dimensional region integral with the first positive Rosser pair depth.
All region inequalities match the provider's strict shell pointwise. The
provider's proved source identity then gives Suzuki's source layer three.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open MeasureTheory Set
open MathlibNt.SieveTheory.LinearSieve

private theorem insert_last_fin3 (q x₀ x₁ : ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm
      (q, (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)).symm (x₀, x₁)) =
        ![x₀, x₁, q] := by
  ext i
  fin_cases i <;>
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth, Fin.succAboveCases, MeasurableEquiv.piFinTwo]

/-- Fubini with the final coordinate outermost and the first two coordinates
in their original order. Integrability is supplied for the actual integrand. -/
theorem integral_fin3_last_first (f : (Fin 3 → ℝ) → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ q : ℝ, ∫ x₀ : ℝ, ∫ x₁ : ℝ, f ![x₀, x₁, q] := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  let e₂ := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove _ 2
  have he₂ : MeasurePreserving e₂ := volume_preserving_piFinTwo _
  have hg : Integrable (fun z : ℝ × (Fin 2 → ℝ) => f (e.symm z)) :=
    he.symm.integrable_comp_of_integrable hf
  calc
    (∫ x, f x) = ∫ z : ℝ × (Fin 2 → ℝ), f (e.symm z) :=
      (he.symm.integral_comp' f).symm
    _ = ∫ q : ℝ, ∫ v : Fin 2 → ℝ, f (e.symm (q, v)) := integral_prod _ hg
    _ = ∫ q : ℝ, ∫ x₀ : ℝ, ∫ x₁ : ℝ, f ![x₀, x₁, q] := by
      apply integral_congr_ae
      filter_upwards [hg.prod_right_ae] with q hq
      have hq₂ : Integrable (fun z : ℝ × ℝ => f (e.symm (q, e₂.symm z))) :=
        he₂.symm.integrable_comp_of_integrable hq
      calc
        (∫ v : Fin 2 → ℝ, f (e.symm (q, v))) =
            ∫ z : ℝ × ℝ, f (e.symm (q, e₂.symm z)) :=
          (he₂.symm.integral_comp' (fun v => f (e.symm (q, v)))).symm
        _ = ∫ x₀ : ℝ, ∫ x₁ : ℝ, f (e.symm (q, e₂.symm (x₀, x₁))) :=
          integral_prod _ hq₂
        _ = _ := by simp only [e, e₂, insert_last_fin3]

private theorem triple_region_vector_iff (q x₀ x₁ : ℝ) :
    ![x₀, x₁, q] ∈ rosserTripleRegion ↔
      0 < q ∧ q < x₁ ∧ x₁ < x₀ ∧ x₀ < 1 ∧ 3 < x₀ + x₁ + 3 * q := by
  simp [rosserTripleRegion, Matrix.cons_val_two]

private theorem triple_kernel_vector (q x₀ x₁ : ℝ) :
    rosserTripleKernel ![x₀, x₁, q] =
      q⁻¹ * q⁻¹ * (x₀⁻¹ * x₁⁻¹) := by
  simp [rosserTripleKernel, rosserTripleLogDensity, Fin.prod_univ_succ,
    Matrix.cons_val_two, one_div]
  ring

/-- For a fixed positive least coordinate, the region slice is exactly the
depth-one boundary recursion, with the same strict terminal shell. -/
theorem integral_rosserTripleKernel_slice {q : ℝ} (hq : 0 < q) :
    (∫ x₀ : ℝ, ∫ x₁ : ℝ,
      rosserTripleRegion.indicator rosserTripleKernel ![x₀, x₁, q]) =
      q⁻¹ * q⁻¹ * upperRosserBoundaryMass 1 3 q := by
  calc
    (∫ x₀ : ℝ, ∫ x₁ : ℝ,
        rosserTripleRegion.indicator rosserTripleKernel ![x₀, x₁, q]) =
        ∫ x₀ in Ioo q 1, ∫ x₁ in Ioo q x₀,
          q⁻¹ * q⁻¹ * (x₀⁻¹ *
            (x₁⁻¹ * upperRosserBoundaryMassAux 0 (3 - x₀ - x₁) q x₁)) := by
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards [] with x₀
      by_cases hx₀ : x₀ ∈ Ioo q 1
      · rw [indicator_of_mem hx₀, ← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        filter_upwards [] with x₁
        by_cases hx₁ : x₁ ∈ Ioo q x₀
        · rw [indicator_of_mem hx₁, upperRosserBoundaryMassAux_zero]
          have hres : 0 ≤ 3 - x₀ - x₁ := by linarith [hx₀.2, hx₁.2]
          by_cases hs : 3 - x₀ - x₁ < 3 * q
          · have hm : ![x₀, x₁, q] ∈ rosserTripleRegion :=
              (triple_region_vector_iff q x₀ x₁).mpr ⟨hq, hx₁.1, hx₁.2, hx₀.2, by linarith⟩
            rw [indicator_of_mem hm, if_pos ⟨hres, hs⟩, mul_one,
              triple_kernel_vector]
          · have hm : ![x₀, x₁, q] ∉ rosserTripleRegion := by
              intro hm
              have hm' := (triple_region_vector_iff q x₀ x₁).mp hm
              exact hs (by linarith [hm'.2.2.2.2])
            rw [indicator_of_notMem hm, if_neg (by tauto)]
            simp
        · rw [indicator_of_notMem hx₁]
          have hm : ![x₀, x₁, q] ∉ rosserTripleRegion := by
            intro hm
            have hm' := (triple_region_vector_iff q x₀ x₁).mp hm
            exact hx₁ ⟨hm'.2.1, hm'.2.2.1⟩
          exact indicator_of_notMem hm _
      · rw [indicator_of_notMem hx₀]
        apply integral_eq_zero_of_ae
        filter_upwards [] with x₁
        have hm : ![x₀, x₁, q] ∉ rosserTripleRegion := by
          intro hm
          have hm' := (triple_region_vector_iff q x₀ x₁).mp hm
          exact hx₀ ⟨hm'.2.1.trans hm'.2.2.1, hm'.2.2.2.1⟩
        exact indicator_of_notMem hm _
    _ = q⁻¹ * q⁻¹ * upperRosserBoundaryMass 1 3 q := by
      rw [upperRosserBoundaryMass_succ]
      norm_num only [show (3 : ℝ) / 3 = 1 by norm_num, min_self]
      simp_rw [integral_const_mul]

/-- The finite-dimensional Lebesgue integral is the provider's actual first
positive continuous boundary layer, with outer density `q⁻²`. -/
theorem rosserTripleLayerIntegral_eq_boundaryMass :
    rosserTripleLayerIntegral =
      ∫ q in Ioo (0 : ℝ) 1, q⁻¹ * q⁻¹ * upperRosserBoundaryMass 1 3 q := by
  have hi : Integrable (rosserTripleRegion.indicator rosserTripleKernel) :=
    integrableOn_rosserTripleKernel_region.integrable_indicator measurableSet_rosserTripleRegion
  change (∫ x in rosserTripleRegion, rosserTripleKernel x) = _
  rw [← integral_indicator measurableSet_rosserTripleRegion,
    integral_fin3_last_first _ hi, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hq]
    exact integral_rosserTripleKernel_slice hq.1
  · rw [indicator_of_notMem hq]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x₀
    apply integral_eq_zero_of_ae
    filter_upwards [] with x₁
    have hm : ![x₀, x₁, q] ∉ rosserTripleRegion := by
      intro hm
      have hm' := (triple_region_vector_iff q x₀ x₁).mp hm
      exact hq ⟨hm'.1, hm'.2.1.trans (hm'.2.2.1.trans hm'.2.2.2.1)⟩
    exact indicator_of_notMem hm _

/-- The region integral is Suzuki's source layer three at residual `s = 3`.
The source identity is a proved provider theorem, with no analytic premise. -/
theorem rosserTripleLayerIntegral_eq_suzukiLayer :
    rosserTripleLayerIntegral = MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer 1 2 3 3 := by
  rw [rosserTripleLayerIntegral_eq_boundaryMass]
  simpa using suzukiUpperRosserBoundarySourceSuccLayerIdentity 0 3
    (by norm_num) (by norm_num)

end

end ImbalancedChen
