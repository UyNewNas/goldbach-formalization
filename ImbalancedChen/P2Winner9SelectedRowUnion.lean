import ImbalancedChen.P2Winner9SelectedRowCurvatureFloor
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Additivity for the two selected Winner9 physical simplices

An exact affine separator places the original ordered vertices of rows 21
and 22 on opposite closed sides. Their overlap lies in a null affine wall,
so Lebesgue integrals add over their union.
-/

namespace ImbalancedChen.P2Winner9SelectedRowUnion

noncomputable section

open Set MeasureTheory
open P2Winner9BarycentricMixedDegreeOne P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation P2Winner9SelectedRowAnalyticCaps
open P2Winner9SelectedRowEdgeGeometry P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowCurvatureFloor

def separatorCoefficients : Fin 8 → ℚ :=
  ![14367583123974080, 35994059171730144, 36012841021345440, 2612015548600898,
    40152764676910974, 0, 43102749371922240, 0]

def separatorOffset : ℚ := 12796128719789415

private def separatorValue (z : Ambient) : ℝ :=
  ∑ i, (separatorCoefficients i : ℝ) * z i

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem row21_vertex_le : ∀ k : Fin 9,
    (∑ i, separatorCoefficients i * row21 k i) ≤ separatorOffset := by
  unfold separatorCoefficients separatorOffset row21 P2Winner9Row21RawVertexData.coords
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem row22_vertex_ge : ∀ k : Fin 9,
    separatorOffset ≤ ∑ i, separatorCoefficients i * row22 k i := by
  unfold separatorCoefficients separatorOffset row22
  decide +kernel

private theorem separator_vertexMap (v : Fin 9 → Ambient) (x : Ambient) :
    separatorValue (vertexMap v x) = affine (fun k => separatorValue (v k)) x := by
  simp only [separatorValue, vertexMap_coordinate, affine]
  simp_rw [Finset.mul_sum, Finset.sum_mul, ← mul_assoc]
  exact Finset.sum_comm

private theorem affine_mono_on_support {a b : Fin 9 → ℝ} {x : Ambient}
    (hx : x ∈ canonicalSupport) (h : ∀ k, a k ≤ b k) : affine a x ≤ affine b x := by
  unfold affine
  exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (h k) (barycentric_nonneg hx k))

private theorem row21_support_le {z : Ambient} (hz : z ∈ sourceSupport row21) :
    separatorValue z ≤ (separatorOffset : ℝ) := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [separator_vertexMap, ← affine_constant (separatorOffset : ℝ) x]
  apply affine_mono_on_support hx
  intro k
  unfold separatorValue realVertices
  exact_mod_cast row21_vertex_le k

private theorem row22_support_ge {z : Ambient} (hz : z ∈ sourceSupport row22) :
    (separatorOffset : ℝ) ≤ separatorValue z := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [separator_vertexMap, ← affine_constant (separatorOffset : ℝ) x]
  apply affine_mono_on_support hx
  intro k
  unfold separatorValue realVertices
  exact_mod_cast row22_vertex_ge k

private def separatorLinear : Ambient →ₗ[ℝ] ℝ :=
  ∑ i : Fin 8, (separatorCoefficients i : ℝ) • LinearMap.proj i

private theorem separatorLinear_apply (z : Ambient) : separatorLinear z = separatorValue z := by
  simp only [separatorLinear, separatorValue, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]

private def separatingWall : AffineSubspace ℝ Ambient where
  carrier := {z | separatorLinear z = (separatorOffset : ℝ)}
  smul_vsub_vadd_mem' := by
    intro t x y z hx hy hz
    change separatorLinear (t • (x - y) + z) = _
    change separatorLinear x = _ at hx
    change separatorLinear y = _ at hy
    change separatorLinear z = _ at hz
    simp only [map_add, map_smul, map_sub, hx, hy, hz, sub_self, smul_zero, zero_add]

private theorem separatingWall_ne_top : separatingWall ≠ ⊤ := by
  intro h
  have h0 : (0 : Ambient) ∈ separatingWall := by rw [h]; trivial
  change separatorLinear 0 = (separatorOffset : ℝ) at h0
  rw [map_zero] at h0
  norm_num [separatorOffset] at h0

/-- The two closed physical supports overlap only on a Lebesgue-null set. -/
theorem row21_row22_overlap_null : volume (sourceSupport row21 ∩ sourceSupport row22) = 0 := by
  apply measure_mono_null (t := (separatingWall : Set Ambient)) _
    (Measure.addHaar_affineSubspace volume separatingWall separatingWall_ne_top)
  rintro z ⟨h21, h22⟩
  change separatorLinear z = (separatorOffset : ℝ)
  rw [separatorLinear_apply]
  exact le_antisymm (row21_support_le h21) (row22_support_ge h22)

/-- Additivity on the two original physical supports. -/
theorem row21_row22_union_integral {f : Ambient → ℝ}
    (h21 : IntegrableOn f (sourceSupport row21)) (h22 : IntegrableOn f (sourceSupport row22)) :
    (∫ z in sourceSupport row21 ∪ sourceSupport row22, f z) =
      (∫ z in sourceSupport row21, f z) + ∫ z in sourceSupport row22, f z :=
  setIntegral_union₀ row21_row22_overlap_null
    (sourceSupport_measurable row22 row22_det_ne_zero).nullMeasurableSet h21 h22

/-- The sum of the original directed curvature floors on this two-row union. -/
theorem row21_row22_curvature_Q96_union_lower :
    (39921728033098315871 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in sourceSupport row21 ∪ sourceSupport row22, physicalUpperIntegrand z := by
  have h21 : IntegrableOn physicalUpperIntegrand (sourceSupport row21) := by
    simpa [vertices] using density_integrable (0 : Fin 2)
  have h22 : IntegrableOn physicalUpperIntegrand (sourceSupport row22) := by
    simpa [vertices] using density_integrable (1 : Fin 2)
  rw [row21_row22_union_integral h21 h22]
  calc
    _ = (33473824252327663860 : ℝ) / 79228162514264337593543950336 +
        (6447903780770652011 : ℝ) / 79228162514264337593543950336 := by norm_num
    _ ≤ _ := add_le_add row21_original_curvature_Q96_integral_lower
      row22_original_curvature_Q96_integral_lower

end

end ImbalancedChen.P2Winner9SelectedRowUnion
