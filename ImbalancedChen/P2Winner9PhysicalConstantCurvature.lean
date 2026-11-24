import ImbalancedChen.P2Winner9ReciprocalProduct
import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps

/-! Constant transverse curvature and density normalization on the actual row supports. -/

namespace ImbalancedChen.P2Winner9PhysicalConstantCurvature

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2Winner9SelectedRowRealJacobian
open P2Winner9SelectedRowEdgeGeometry (edgeMatrix row21_det_ne_zero row22_det_ne_zero)
open P2Winner9SelectedRowAnalyticCaps
open P2Winner9PhysicalAffineTransfer
open P2Winner9ReciprocalProduct

def A (r : Fin 2) (j : Fin 10) (z : Ambient) : ℝ :=
  normalizedFactor (fun k => (means r k : ℝ)) j z

def V (r : Fin 2) (j : Fin 10) : ℝ := (transverseUpper r j : ℝ)

def B (r : Fin 2) (j : Fin 10) (z : Ambient) : ℝ :=
  physicalDeviation (fun k => (means r k : ℝ)) j z

def prodInv (r : Fin 2) (z : Ambient) : ℝ :=
  1 / ∏ j : Fin 10, A r j z

def constantCorrection (r : Fin 2) (z : Ambient) : ℝ :=
  (∑ j : Fin 10, (B r j z)^2 / (2 * (V r j)^2)) / (upper r : ℝ)^10

theorem V_typed (r : Fin 2) (j : Fin 10) :
    V r j = ((data r).maxima j : ℝ) / (data r).L := by
  simp [V, transverseUpper]

theorem upper_typed (r : Fin 2) :
    (upper r : ℝ) = ((data r).U : ℝ) / (data r).L := by
  have h : upper r = ((data r).U : ℚ) / (data r).L := by
    by_cases hr : r = 0 <;>
      simp only [upper, data, hr, if_true, if_false,
        P2Winner9SelectedRowIntegerScales.Row21.upper,
        P2Winner9SelectedRowIntegerScales.Row22.upper]
  simp only [h, Rat.cast_div, Rat.cast_natCast]

theorem pointwise_constant_curvature (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    1 / (physicalP (fun j => (means r j : ℝ)) z)^10 + constantCorrection r z ≤
      prodInv r z := by
  have caps := actual_support_caps r hz
  have hP : 0 < physicalP (fun j => (means r j : ℝ)) z :=
    lt_of_lt_of_le (by exact_mod_cast (actual_vertex_guards r).2.1) caps.2.2.1
  have hsum :
      ∑ j : Fin 10, A r j z = 10 * physicalP (fun j => (means r j : ℝ)) z := by
    unfold A physicalP
    ring
  exact reciprocal_product_constant_curvature (fun j => A r j z) (V r)
    (physicalP (fun j => (means r j : ℝ)) z) (upper r : ℝ)
    (fun j => (caps.2.2.2.2 j).1) hP caps.2.2.2.1
    (fun j => (caps.2.2.2.2 j).2.1) (fun j => (caps.2.2.2.2 j).2.2) hsum

theorem A_continuous (r : Fin 2) (j : Fin 10) : Continuous (A r j) :=
  (continuous_physicalFactor j).div_const _

theorem B_continuous (r : Fin 2) (j : Fin 10) : Continuous (B r j) := by
  have hA := A_continuous r
  unfold B physicalDeviation physicalP
  change Continuous (fun z => A r j z - (∑ i : Fin 10, A r i z) / 10)
  fun_prop

theorem constantCorrection_continuous (r : Fin 2) : Continuous (constantCorrection r) := by
  have hB := B_continuous r
  unfold constantCorrection
  fun_prop

theorem prodInv_continuousOn (r : Fin 2) :
    ContinuousOn (prodInv r) (sourceSupport (vertices r)) := by
  have hA := A_continuous r
  have hp : Continuous (fun z => ∏ j : Fin 10, A r j z) := by fun_prop
  apply continuous_const.continuousOn.div hp.continuousOn
  intro z hz
  exact ne_of_gt (Finset.prod_pos (fun j _ => ((actual_support_caps r hz).2.2.2.2 j).1))

def meanProduct (r : Fin 2) : ℝ := ∏ j : Fin 10, (means r j : ℝ)

theorem meanProduct_pos (r : Fin 2) : 0 < meanProduct r :=
  Finset.prod_pos (fun j _ => by exact_mod_cast ((actual_vertex_guards r).2.2.2.1 j).1)

theorem gap_mul_prodInv_eq_density (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    physicalGap z * prodInv r z = (meanProduct r / 4) * physicalUpperIntegrand z := by
  have hF : (∏ j : Fin 10, physicalFactor j z) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun j _ => ((actual_support_caps r hz).2.1 j).2))
  have hm := (meanProduct_pos r).ne'
  unfold prodInv A normalizedFactor physicalUpperIntegrand
  rw [Finset.prod_div_distrib]
  change physicalGap z * (1 / ((∏ j : Fin 10, physicalFactor j z) / meanProduct r)) =
    (meanProduct r / 4) * (4 * physicalGap z / ∏ j : Fin 10, physicalFactor j z)
  field_simp [hF, hm]

theorem weighted_prodInv_integral (r : Fin 2) :
    (∫ z in sourceSupport (vertices r), physicalGap z * prodInv r z) =
      (meanProduct r / 4) * ∫ z in sourceSupport (vertices r), physicalUpperIntegrand z := by
  have hdet : (edgeMatrix (vertices r)).det ≠ 0 := by
    fin_cases r
    · simpa [vertices] using row21_det_ne_zero
    · simpa [vertices] using row22_det_ne_zero
  rw [← integral_const_mul]
  exact setIntegral_congr_fun (sourceSupport_measurable (vertices r) hdet)
    (fun _ hz => gap_mul_prodInv_eq_density r hz)

end

end ImbalancedChen.P2Winner9PhysicalConstantCurvature
