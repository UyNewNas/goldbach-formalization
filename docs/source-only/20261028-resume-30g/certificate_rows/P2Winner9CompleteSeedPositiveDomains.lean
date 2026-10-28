import ImbalancedChen.P2Winner9CompleteSeedData
import ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual analytic domains for EVERY one of the11026 literal seed rows.
The sourceSupport is the image of its own nine original ordered vertices,
not an arbitrary model cell. Finite vertex checks are unevaluated source
terms. Positive density factors and compactness are proved without assuming
an all-row enclosure, a triangulation cover or a policy licence.
-/

namespace ImbalancedChen.P2Winner9CompleteSeedPositiveDomains

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open ImbalancedChen.P2Winner9CompleteSeedData
open ImbalancedChen.P2Winner9SelectedRowRealJacobian
open ImbalancedChen.P2Winner9SelectedRowIntegerScales
open ImbalancedChen.P2Winner9SelectedRowAnalyticCaps
open ImbalancedChen.P2Winner9PhysicalAffineTransfer
open ImbalancedChen.P2Winner9PhysicalVertexInterpolation
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne

abbrev VertexIndex := Fin 201

def originalPoint (v : VertexIndex) : Fin 8 → ℚ :=
  P2Winner9CompleteSeedVertices.coordinates[v.val]!

def constantFamily (p : Fin 8 → ℚ) : RationalVertices := fun _ => p

def minimumFactor (j : Fin 10) : ℚ :=
  (List.ofFn (fun v : VertexIndex => rawFactor (constantFamily (originalPoint v)) 0 j)).foldl min 1

/-- The common201 actual source vertices provide uniform strictly positive
factor bounds; no row is sampled and no matrix determinant is evaluated. -/
theorem original_vertex_analytic_guards :
    (∀ j : Fin 10, 0 < minimumFactor j ∧
      ∀ v : VertexIndex, minimumFactor j ≤ rawFactor (constantFamily (originalPoint v)) 0 j) ∧
    ∀ v : VertexIndex,
      0 ≤ rawGap (constantFamily (originalPoint v)) 0 ∧
      rawR (constantFamily (originalPoint v)) 0 ≤ 153 / 256 ∧
      rawM (constantFamily (originalPoint v)) 0 ≤ 299 / 500 := by
  decide +kernel

/-- Positivity of every actual literal stored mean, not a mean vector
postulated for a generic index family. The closed proof remains unexecuted. -/
theorem all_original_means_positive : ∀ i : RowIndex, ∀ j : Fin 10, 0 < (entry i).means j := by
  decide +kernel

theorem vertex_id_bound (i : RowIndex) (k : Fin 9) : (entry i).vertexIds k < 201 :=
  (full_source_shapes_and_chronology.2.2 i).2.2.2.2.1 k

theorem actual_vertex_lookup (i : RowIndex) (k : Fin 9) :
    physicalVertices i k = originalPoint ⟨(entry i).vertexIds k, vertex_id_bound i k⟩ := rfl

def actualSupport (i : RowIndex) : Set Ambient := sourceSupport (physicalVertices i)

theorem vertex_gap_nonneg (i : RowIndex) (k : Fin 9) :
    0 ≤ physicalGap (realVertices (physicalVertices i) k) := by
  let v : VertexIndex := ⟨(entry i).vertexIds k, vertex_id_bound i k⟩
  have he : physicalVertices i k = originalPoint v := actual_vertex_lookup i k
  have hraw := (original_vertex_analytic_guards.2 v).1
  have heq : rawGap (physicalVertices i) k = rawGap (constantFamily (originalPoint v)) 0 := by
    simp only [rawGap, rawM, rawR, constantFamily, he]
  rw [← rawGap_cast, heq]
  exact_mod_cast hraw

theorem vertex_factor_lower (i : RowIndex) (k : Fin 9) (j : Fin 10) :
    (minimumFactor j : ℝ) ≤ physicalFactor j (realVertices (physicalVertices i) k) := by
  let v : VertexIndex := ⟨(entry i).vertexIds k, vertex_id_bound i k⟩
  have he : physicalVertices i k = originalPoint v := actual_vertex_lookup i k
  have hraw := (original_vertex_analytic_guards.1 j).2 v
  have heq : rawFactor (physicalVertices i) k j =
      rawFactor (constantFamily (originalPoint v)) 0 j := by
    simp only [rawFactor, rawM, rawR, rawSum, constantFamily, he]
  rw [← rawFactor_cast, heq]
  exact_mod_cast hraw

/-- Every actual closed simplex has positive original factors and
nonnegative gap. This is an unconditional all-row analytic prerequisite,
not an assumed family enclosure. -/
theorem all_actual_support_positive (i : RowIndex) {z : Ambient}
    (hz : z ∈ actualSupport i) :
    0 ≤ physicalGap z ∧ ∀ j : Fin 10,
      (minimumFactor j : ℝ) ≤ physicalFactor j z ∧ 0 < physicalFactor j z := by
  rcases hz with ⟨x, hx, rfl⟩
  constructor
  · rw [physicalGap_vertexMap]
    exact affine_lower hx _ 0 (vertex_gap_nonneg i)
  · intro j
    have h : (minimumFactor j : ℝ) ≤ physicalFactor j
        (vertexMap (realVertices (physicalVertices i)) x) := by
      rw [physicalFactor_vertexMap]
      exact affine_lower hx _ _ (fun k => vertex_factor_lower i k j)
    exact ⟨h, lt_of_lt_of_le (by exact_mod_cast (original_vertex_analytic_guards.1 j).1) h⟩

theorem ordered_edge_continuous (v : Fin 9 → Ambient) : Continuous (vertexMap v) := by
  apply continuous_pi
  intro j
  unfold vertexMap
  fun_prop

theorem all_actual_support_compact (i : RowIndex) : IsCompact (actualSupport i) :=
  canonicalSupport_compact.image (ordered_edge_continuous (realVertices (physicalVertices i)))

theorem all_actual_support_measurable (i : RowIndex) : MeasurableSet (actualSupport i) :=
  (all_actual_support_compact i).isClosed.measurableSet

/-- All11026 actual density integrals are defined on their own positive
compact physical domains; no invertible-map proof or cover is assumed. -/
theorem all_actual_density_integrable (i : RowIndex) :
    IntegrableOn physicalUpperIntegrand (actualSupport i) := by
  have hfac : ∀ j : Fin 10, Continuous (physicalFactor j) := continuous_physicalFactor
  have hprod : Continuous (fun z : Ambient => ∏ j : Fin 10, physicalFactor j z) := by fun_prop
  have hnum : Continuous (fun z : Ambient => 4 * physicalGap z) :=
    continuous_const.mul continuous_physicalGap
  have hc : ContinuousOn physicalUpperIntegrand (actualSupport i) := by
    apply hnum.continuousOn.div hprod.continuousOn
    intro z hz
    exact ne_of_gt (Finset.prod_pos (fun j _ => ((all_actual_support_positive i hz).2 j).2))
  exact hc.integrableOn_compact (all_actual_support_compact i)

end

end ImbalancedChen.P2Winner9CompleteSeedPositiveDomains
