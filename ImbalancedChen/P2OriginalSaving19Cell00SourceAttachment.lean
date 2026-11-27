import ImbalancedChen.P2OriginalSaving19Cell00Packing
import ImbalancedChen.OriginalAscendingThirteenExportOwnershipJoin

/-! Candidate source attachment using every original one of the 97 gates.
Closed simplex boundaries are removed only along proved null affine walls. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00SourceAttachment
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19SourceMeasure
open P2OriginalSaving19Cell00PhysicalMomentRow
open P2OriginalSaving19Cell00Packing
open P2OriginalSaving19Geometry00Decoding
open P2OriginalSaving19Geometry00BoundedAccess
open P2OriginalSaving19RationalAffineSeparator
open OriginalAscendingThirteenLiteralAffineRows
open OriginalAscendingThirteenExportOwnershipJoin
open OriginalAscendingThirteenCellOwnership

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def vertexPoint (v : Fin 28) : P2OriginalSaving19RowNumericsPure.QPoint :=
  fun j => (concreteGeometry00.vertices[v.val]!)[j.val]!

theorem row_vertex_is_original (r : Fin 56) (i : Fin 9) :
    ∃ v : Fin 28, boundedRowVertex r i = vertexPoint v := by
  let v : Fin 28 := ⟨(vertexIndex r i).val, by
    have h := (vertexIndex r i).isLt
    exact lt_of_lt_of_eq h P2OriginalSaving19Geometry00Shape.vertex_count⟩
  refine ⟨v, ?_⟩
  funext j
  exact (coordinate_lookup_no_fallback (vertexIndex r i) j).symm

def gate (g : Fin 97) : Form := exportedCoefficients 0 g

theorem proper_gates : ∀ g : Fin 97, ∃ j : Fin 8, gate g j.succ ≠ 0 := by
  decide +kernel

theorem original_vertex_checks : ∀ v : Fin 28, ∀ g : Fin 97,
    0 ≤ evalQ (gate g) (vertexPoint v) := by
  decide +kernel

theorem support_closed_gates (r : Fin 56) {x : Point} (hx : x ∈ physicalSimplex r)
    (g : Fin 97) : 0 ≤ eval (gate g) x := by
  apply eval_nonneg_support (gate g) (row r).linear (row r).base _ hx
  intro i
  rw [simplex_vertices, eval_cast]
  obtain ⟨v, hv⟩ := row_vertex_is_original r i
  rw [hv]
  exact_mod_cast original_vertex_checks v g

def sourceWalls : Set Point := ⋃ g : Fin 97, {x | eval (gate g) x = 0}

theorem sourceWalls_null : volume sourceWalls = 0 :=
  measure_iUnion_null (fun g => proper_wall_null (gate g) (proper_gates g))

theorem support_off_walls_in_cell (r : Fin 56) :
    physicalSimplex r \ sourceWalls ⊆ cell 0 := by
  rintro x ⟨hx, hw⟩
  apply (strictExportedRows_iff_StrictRows 0 x).mp
  intro g
  have hn : eval (gate g) x ≠ 0 := fun he => hw (mem_iUnion.mpr ⟨g, he⟩)
  exact lt_of_le_of_ne (support_closed_gates r hx g) (Ne.symm hn)

theorem union_ae_in_cell : physicalUnion ≤ᵐ[volume] cell 0 := by
  have hw : ∀ᵐ x ∂volume, x ∉ sourceWalls := by
    rw [ae_iff]
    have hs : {x : Point | ¬ x ∉ sourceWalls} = sourceWalls := by
      ext x
      simp only [mem_ofPred_eq, not_not]
    rw [hs]
    exact sourceWalls_null
  filter_upwards [hw] with x hx
  intro hu
  obtain ⟨r, hr⟩ := mem_iUnion.mp hu
  exact support_off_walls_in_cell r ⟨hr, hx⟩

theorem original_cell_integral_bound :
    (∑ r : Fin 56,
      ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) ≤
      ∫ t in cell 0, conservativeDensity t := by
  apply stored_sum_le_union_integral.trans
  apply setIntegral_mono_set (cell_density_integrable 0) _ union_ae_in_cell
  filter_upwards [ae_restrict_mem (cell_measurable 0)] with t ht
  exact cell_density_nonneg ht

theorem saved_numerator :
    (∑ r : Fin 56, (originalMomentRow r).newFloorQ96 : ℤ) = 1055527309463438251 :=
  P2OriginalSaving19Cell00AllPrefixFloorChecks.saved_new_Q96_total

theorem concrete_cell_integral_bound :
    (((1055527309463438251 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ) ≤
      ∫ t in cell 0, conservativeDensity t := by
  calc
    _ = (∑ r : Fin 56,
        ((((originalMomentRow r).newFloorQ96 : ℚ) / (2 : ℚ)^96 : ℚ) : ℝ)) := by
      push_cast
      rw [← Finset.sum_div, ← Int.cast_sum, saved_numerator]
      norm_num
    _ ≤ _ := original_cell_integral_bound

#print axioms original_vertex_checks
#print axioms support_off_walls_in_cell
#print axioms original_cell_integral_bound
#print axioms concrete_cell_integral_bound
end
end ImbalancedChen.P2OriginalSaving19Cell00SourceAttachment
