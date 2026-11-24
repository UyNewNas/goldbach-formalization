import ImbalancedChen.P2Winner9OriginalSourceIntegral
import ImbalancedChen.P2Winner9OriginalTerminal
import ImbalancedChen.P2Winner9SelectedArchiveChecker
import ImbalancedChen.P2Winner9SelectedRowQ6Union
import ImbalancedChen.P2Winner9SelectedVertexBinding

/-! Transfer certified archive rows to the original Winner9 source integral. -/

namespace ImbalancedChen.P2Winner9ArchiveIntegral

open MeasureTheory
open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9SelectedRowRealJacobian (sourceSupport sourceSupport_measurable realVertices)
open P2Winner9SeedVertexAnalyticGuards (VertexIndex originalPoint)
open P2Winner9PhysicalAffineTransfer (physicalUpperIntegrand canonicalSupport_compact)
open P2Winner9PhysicalVertexInterpolation (vertexMap)
open P2Winner9OriginalSourceGates (originalPhysicalSource)
open P2Winner9OriginalSourceIntegral (sum_source_integrals_le_original)
open P2Winner9RowArithmeticChecker (archiveVertices)
open P2Winner9SelectedArchiveChecker

/-- The original source bounds the integral sum of an almost-disjoint family
from the original vertex table. Compactness follows from the affine image. -/
theorem archive_family_integrals_le_original {ι : Type*} [Fintype ι] (rows : ι → RawRow)
    (hids : ∀ i k, (rows i).vertexIds k < 201)
    (hoverlap : Pairwise fun i j => volume
      (sourceSupport (archiveVertices (rows i)) ∩ sourceSupport (archiveVertices (rows j))) = 0) :
    (∑ i, ∫ z in sourceSupport (archiveVertices (rows i)), physicalUpperIntegrand z) ≤
      ∫ z in originalPhysicalSource, physicalUpperIntegrand z := by
  let ids (i : ι) (k : Fin 9) : VertexIndex := ⟨(rows i).vertexIds k, hids i k⟩
  apply sum_source_integrals_le_original (fun i => archiveVertices (rows i)) ids
    (fun _ _ => rfl) _ hoverlap
  intro i
  have hc : Continuous (vertexMap (realVertices (archiveVertices (rows i)))) := by
    unfold vertexMap
    fun_prop
  exact (canonicalSupport_compact.image hc).isClosed.measurableSet

/-- A finite family of original rows bounds the original source integral
once each winning certificate and each null-overlap condition is checked. -/
theorem checked_family_floor {ι : Type*} [Fintype ι] (rows : ι → RawRow)
    (hids : ∀ i k, (rows i).vertexIds k < 201)
    (hmax : ∀ i, (rows i).mixedSelected = max (rows i).logSelected (rows i).mixedRaw)
    (hcheck : ∀ i, checkSelected (rows i) = true)
    (hoverlap : Pairwise fun i j => volume
      (sourceSupport (archiveVertices (rows i)) ∩ sourceSupport (archiveVertices (rows j))) = 0) :
    (∑ i, ((rows i).mixedSelected : ℝ) / (q96 : ℝ)) ≤
      ∫ z in originalPhysicalSource, physicalUpperIntegrand z := by
  exact (Finset.sum_le_sum fun i _ => checkSelected_sound (hcheck i) (hmax i)).trans
    (archive_family_integrals_le_original rows hids hoverlap)

open P2Winner9SelectedRowEdgeGeometry (row21 row22)
open P2Winner9PhysicalAffineTransfer (row21VertexIds row22VertexIds)
open P2Winner9CompleteSeedVertices (coordinates)
open P2Winner9SelectedRowAnalyticCaps (vertices density_integrable)
open P2Winner9SelectedPhysicalMeans (row_det_ne_zero)
open P2Winner9SelectedVertexBinding (row21_coordinates row22_coordinates)
open P2Winner9SelectedRowUnion (row21_row22_overlap_null row21_row22_union_integral)
open P2Winner9SelectedRowQ6Union (row21_row22_Q96_union_lower)

private def selectedId (i : Fin 2) (k : Fin 9) : ℕ :=
  if i = 0 then row21VertexIds k else row22VertexIds k

private theorem selected_id_lt : ∀ (i : Fin 2) (k : Fin 9), selectedId i k < 201 := by
  decide +kernel

private def selectedVertex (i : Fin 2) (k : Fin 9) : VertexIndex :=
  ⟨selectedId i k, selected_id_lt i k⟩

private theorem selected_vertex_eq (i : Fin 2) (k : Fin 9) :
    vertices i k = originalPoint (selectedVertex i k) := by
  fin_cases i
  · funext j
    change row21 k j = coordinates[row21VertexIds k]! j
    exact (row21_coordinates k).2 j
  · funext j
    change row22 k j = coordinates[row22VertexIds k]! j
    exact (row22_coordinates k).2 j

/-- The two already certified archive rows give a bound on the original
strict Winner9 source defined by its 97 indexed affine gates. -/
theorem row21_row22_Q96_original_source_lower :
    (40017007922393485130 : ℝ) / 79228162514264337593543950336 ≤
      ∫ z in originalPhysicalSource, physicalUpperIntegrand z := by
  have hp : Pairwise (fun i j : Fin 2 => volume
      (sourceSupport (vertices i) ∩ sourceSupport (vertices j)) = 0) := by
    intro i j hne
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · simpa [vertices] using row21_row22_overlap_null
    · rw [Set.inter_comm]
      simpa [vertices] using row21_row22_overlap_null
    · exact (hne rfl).elim
  have hsum := sum_source_integrals_le_original vertices selectedVertex selected_vertex_eq
    (fun i => sourceSupport_measurable _ (row_det_ne_zero i)) hp
  rw [Fin.sum_univ_two] at hsum
  have hint := row21_row22_union_integral
    (by simpa [vertices] using density_integrable (0 : Fin 2))
    (by simpa [vertices] using density_integrable (1 : Fin 2))
  have hfloor := row21_row22_Q96_union_lower
  rw [hint] at hfloor
  exact hfloor.trans (by simpa [vertices] using hsum)

/-- The corresponding contribution to terminal 41 of the original 87-cell archive. -/
theorem row21_row22_Q96_terminal41_lower :
    (40017007922393485130 : ℝ) / 79228162514264337593543950336 ≤
      P2Winner9OriginalTerminal.terminal41Integral := by
  rw [P2Winner9OriginalTerminal.terminal41_integral_eq]
  exact row21_row22_Q96_original_source_lower

end ImbalancedChen.P2Winner9ArchiveIntegral
