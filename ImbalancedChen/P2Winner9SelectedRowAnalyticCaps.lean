import ImbalancedChen.P2Winner9SelectedRowIntegerScales
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual closed-support analytic licences for the two selected physical
rows: positive factors, nonnegative gap, P and normalized-factor caps,
a single uniform Y interval strictly below 1, and the precise positive
segment needed by the -log transverse Taylor remainder. No Jensen or
curvature inequality, inherited policy licence, or row floor is assumed.
-/

namespace ImbalancedChen.P2Winner9SelectedRowAnalyticCaps

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9SelectedRowEdgeGeometry
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9SimplexCoordinateSlice
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly

def vertices (r : Fin 2) : RationalVertices := if r = 0 then row21 else row22

def data (r : Fin 2) : SimplexData := if r = 0 then Row21.data else Row22.data

def means (r : Fin 2) : Fin 10 → ℚ := if r = 0 then Row21.means else Row22.means

def upper (r : Fin 2) : ℚ := if r = 0 then Row21.upper else Row22.upper

def factorLower (r : Fin 2) (j : Fin 10) : ℚ :=
  (List.ofFn (fun i : Fin 9 => rawFactor (vertices r) i j)).foldl min 1

def pLower (r : Fin 2) : ℚ :=
  (List.ofFn (fun i : Fin 9 => rawP (vertices r) (means r) i)).foldl min 1

def transverseUpper (r : Fin 2) (j : Fin 10) : ℚ :=
  ((data r).maxima j : ℚ) / (data r).L

def yUpper (r : Fin 2) : ℚ := 1 - pLower r / upper r

/-- These are actual finite inequalities of the original rational vertex
values and original U/L and v_j/L maxima. The closed proof is unevaluated. -/
def vertexGuards (r : Fin 2) : Prop :=
  0 < upper r ∧ 0 < pLower r ∧ pLower r ≤ upper r ∧
  (∀ j : Fin 10, 0 < means r j ∧ 0 < factorLower r j ∧
    0 < transverseUpper r j) ∧
  ∀ i : Fin 9,
    0 ≤ rawGap (vertices r) i ∧
    pLower r ≤ rawP (vertices r) (means r) i ∧
    rawP (vertices r) (means r) i ≤ upper r ∧
    ∀ j : Fin 10,
      factorLower r j ≤ rawFactor (vertices r) i j ∧
      rawFactor (vertices r) i j / means r j ≤ transverseUpper r j ∧
      rawP (vertices r) (means r) i ≤ transverseUpper r j

theorem actual_vertex_guards : ∀ r : Fin 2, vertexGuards r := by
  decide +kernel

theorem barycentric_nonneg {x : Ambient} (hx : x ∈ canonicalSupport)
    (i : Fin 9) : 0 ≤ barycentric i x := by
  change (∀ j : Fin 8, 0 ≤ x j) ∧ (∑ j : Fin 8, x j) ≤ 1 at hx
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [barycentric] using sub_nonneg.mpr hx.2
  · simpa [barycentric] using hx.1 j

theorem barycentric_sum (x : Ambient) : ∑ i : Fin 9, barycentric i x = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [barycentric, Fin.cases_zero, Fin.cases_succ]
  ring

/-- Affine finite vertex bounds extend to the true closed simplex. -/
theorem affine_lower {x : Ambient} (hx : x ∈ canonicalSupport)
    (v : Fin 9 → ℝ) (c : ℝ) (hv : ∀ i, c ≤ v i) : c ≤ affine v x := by
  rw [← affine_constant c x]
  unfold affine
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (hv i) (barycentric_nonneg hx i))

theorem affine_upper {x : Ambient} (hx : x ∈ canonicalSupport)
    (v : Fin 9 → ℝ) (c : ℝ) (hv : ∀ i, v i ≤ c) : affine v x ≤ c := by
  rw [← affine_constant c x]
  unfold affine
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (hv i) (barycentric_nonneg hx i))

/-- All analytic cap and positivity conditions are discharged on the
actual physical row images, including every boundary point. -/
theorem actual_support_caps (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    0 ≤ physicalGap z ∧
      (∀ j : Fin 10, (factorLower r j : ℝ) ≤ physicalFactor j z ∧
        0 < physicalFactor j z) ∧
      (pLower r : ℝ) ≤ physicalP (fun j => (means r j : ℝ)) z ∧
      physicalP (fun j => (means r j : ℝ)) z ≤ (upper r : ℝ) ∧
      ∀ j : Fin 10,
        0 < normalizedFactor (fun k => (means r k : ℝ)) j z ∧
        normalizedFactor (fun k => (means r k : ℝ)) j z ≤ (transverseUpper r j : ℝ) ∧
        physicalP (fun k => (means r k : ℝ)) z ≤ (transverseUpper r j : ℝ) := by
  have h := actual_vertex_guards r
  rcases hz with ⟨x, hx, rfl⟩
  have hgapV (i : Fin 9) : 0 ≤ physicalGap (realVertices (vertices r) i) := by
    rw [← rawGap_cast]
    exact_mod_cast (h.2.2.2.2 i).1
  have hfacV (j : Fin 10) (i : Fin 9) :
      (factorLower r j : ℝ) ≤ physicalFactor j (realVertices (vertices r) i) := by
    rw [← rawFactor_cast]
    exact_mod_cast ((h.2.2.2.2 i).2.2.2 j).1
  have hpLoV (i : Fin 9) :
      (pLower r : ℝ) ≤ physicalP (fun j => (means r j : ℝ)) (realVertices (vertices r) i) := by
    rw [← rawP_cast]
    exact_mod_cast (h.2.2.2.2 i).2.1
  have hpHiV (i : Fin 9) :
      physicalP (fun j => (means r j : ℝ)) (realVertices (vertices r) i) ≤ (upper r : ℝ) := by
    rw [← rawP_cast]
    exact_mod_cast (h.2.2.2.2 i).2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [physicalGap_vertexMap]
    exact affine_lower hx _ 0 hgapV
  · intro j
    have hl : (factorLower r j : ℝ) ≤ physicalFactor j
        (vertexMap (realVertices (vertices r)) x) := by
      rw [physicalFactor_vertexMap]
      exact affine_lower hx _ _ (hfacV j)
    exact ⟨hl, lt_of_lt_of_le (by exact_mod_cast (h.2.2.2.1 j).2.1) hl⟩
  · rw [physicalP_vertexMap]
    exact affine_lower hx _ _ hpLoV
  · rw [physicalP_vertexMap]
    exact affine_upper hx _ _ hpHiV
  · intro j
    have hmu : (0 : ℝ) < (means r j : ℝ) := by exact_mod_cast (h.2.2.2.1 j).1
    have hfpos : 0 < physicalFactor j (vertexMap (realVertices (vertices r)) x) := by
      rw [physicalFactor_vertexMap]
      exact lt_of_lt_of_le (by exact_mod_cast (h.2.2.2.1 j).2.1)
        (affine_lower hx _ _ (hfacV j))
    refine ⟨div_pos hfpos hmu, ?_, ?_⟩
    · rw [normalizedFactor_vertexMap]
      apply affine_upper hx
      intro i
      change physicalFactor j (realVertices (vertices r) i) / (means r j : ℝ) ≤ _
      rw [← rawFactor_cast]
      exact_mod_cast ((h.2.2.2.2 i).2.2.2 j).2.1
    · rw [physicalP_vertexMap]
      apply affine_upper hx
      intro i
      rw [← rawP_cast]
      exact_mod_cast ((h.2.2.2.2 i).2.2.2 j).2.2

/-- One explicit q<1 works uniformly on the whole closed physical cell. -/
theorem actual_uniform_Y (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    0 ≤ physicalY (fun j => (means r j : ℝ)) (upper r : ℝ) z ∧
      physicalY (fun j => (means r j : ℝ)) (upper r : ℝ) z ≤ (yUpper r : ℝ) ∧
      (yUpper r : ℝ) < 1 := by
  have h := actual_vertex_guards r
  have hc := actual_support_caps r hz
  have hU : (0 : ℝ) < (upper r : ℝ) := by exact_mod_cast h.1
  have hp : (0 : ℝ) < (pLower r : ℝ) := by exact_mod_cast h.2.1
  have hPU := hc.2.2.2.1
  have hLP := hc.2.2.1
  have hr : (yUpper r : ℝ) = 1 - (pLower r : ℝ) / (upper r : ℝ) := by
    simp [yUpper]
  rw [physicalY, hr]
  refine ⟨?_, ?_, ?_⟩
  · have hh := (div_le_one hU).2 hPU
    linarith
  · exact sub_le_sub_left ((div_le_div_iff_of_pos_right hU).2 hLP) 1
  · have hh := div_pos hp hU
    linarith

/-- This is exactly the positive bounded segment used by the source
Taylor remainder for -log, now licensed by the actual physical rows. -/
theorem actual_transverse_segment (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) (j : Fin 10) {t : ℝ}
    (ht : t ∈ Set.uIcc
      (normalizedFactor (fun k => (means r k : ℝ)) j z)
      (physicalP (fun k => (means r k : ℝ)) z)) :
    0 < t ∧ t ≤ (transverseUpper r j : ℝ) := by
  have hc := actual_support_caps r hz
  have ha := hc.2.2.2.2 j
  have hp : 0 < physicalP (fun k => (means r k : ℝ)) z := by
    exact lt_of_lt_of_le (by exact_mod_cast (actual_vertex_guards r).2.1) hc.2.2.1
  change min _ _ ≤ t ∧ t ≤ max _ _ at ht
  exact ⟨lt_of_lt_of_le (lt_min ha.1 hp) ht.1,
    le_trans ht.2 (max_le ha.2.1 ha.2.2)⟩

/-- The two literal raw cap ceilings are finite vertex facts. These
are only numerical cap ceilings, not the full inherited-policy licence. -/
theorem actual_raw_cap_guards : ∀ r : Fin 2, ∀ i : Fin 9,
    rawR (vertices r) i ≤ 153 / 256 ∧ rawM (vertices r) i ≤ 299 / 500 := by
  decide +kernel

/-- The true physical density denominators and old/new cap order are
positive on the whole actual cell. The literal cap ceilings also extend
from the same actual vertices, with no fresh affine-map hypothesis. -/
theorem actual_physical_cap_domain (r : Fin 2) {z : Ambient}
    (hz : z ∈ sourceSupport (vertices r)) :
    (∀ i : Fin 8, 0 < z i) ∧ coordinateSum z < physicalR z ∧
      physicalR z ≤ physicalM z ∧
      physicalR z ≤ 153 / 256 ∧ physicalM z ≤ 299 / 500 := by
  have hc := actual_support_caps r hz
  have hR : coordinateSum z < physicalR z := by
    have h := (hc.2.1 0).2
    rw [physicalFactor_zero] at h
    linarith
  have hRM : physicalR z ≤ physicalM z := by
    have h := hc.1
    rw [physicalGap] at h
    linarith
  refine ⟨?_, hR, hRM, ?_, ?_⟩
  · intro i
    simpa only [physicalFactor_succ_succ] using (hc.2.1 i.succ.succ).2
  · rcases hz with ⟨x, hx, rfl⟩
    rw [physicalR_vertexMap]
    apply affine_upper hx
    intro i
    rw [← rawR_cast]
    exact_mod_cast (actual_raw_cap_guards r i).1
  · rcases hz with ⟨x, hx, rfl⟩
    rw [physicalM_vertexMap]
    apply affine_upper hx
    intro i
    rw [← rawM_cast]
    exact_mod_cast (actual_raw_cap_guards r i).2

theorem continuous_physicalGap : Continuous physicalGap := by
  unfold physicalGap physicalM physicalR
  fun_prop

theorem continuous_physicalFactor (j : Fin 10) : Continuous (physicalFactor j) := by
  fin_cases j <;> dsimp [physicalFactor, physicalR, physicalM, coordinateSum] <;> fun_prop

/-- The actual density integral is well-defined on the compact closed
physical cells; denominator nonvanishing is proved above, not assumed. -/
theorem density_integrable (r : Fin 2) :
    IntegrableOn physicalUpperIntegrand (sourceSupport (vertices r)) := by
  have hfac : ∀ j : Fin 10, Continuous (physicalFactor j) := continuous_physicalFactor
  have hprod : Continuous (fun z : Ambient => ∏ j : Fin 10, physicalFactor j z) := by
    fun_prop
  have hnum : Continuous (fun z : Ambient => 4 * physicalGap z) :=
    continuous_const.mul continuous_physicalGap
  have hcont : ContinuousOn physicalUpperIntegrand (sourceSupport (vertices r)) := by
    apply hnum.continuousOn.div hprod.continuousOn
    intro z hz
    exact ne_of_gt (Finset.prod_pos (fun j _ => ((actual_support_caps r hz).2.1 j).2))
  have hdet : (edgeMatrix (vertices r)).det ≠ 0 := by
    fin_cases r
    · simpa [vertices] using row21_det_ne_zero
    · simpa [vertices] using row22_det_ne_zero
  exact hcont.integrableOn_compact (sourceSupport_compact (vertices r) hdet)

end

end ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
