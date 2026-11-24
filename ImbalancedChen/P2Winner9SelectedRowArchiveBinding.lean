import ImbalancedChen.P2Winner9CompleteSeedBlock00
import ImbalancedChen.P2Winner9CompleteSeedVertices
import ImbalancedChen.P2Winner9SelectedRowQ6Floor

/-! Bind the two physical Q6 integral floors to their original Block00 entries. -/

namespace ImbalancedChen.P2Winner9SelectedRowArchiveBinding

noncomputable section

open MeasureTheory
open P2Winner9CompleteSeedTypes (RawRow)
open P2Winner9CurvatureExactMomentFloor (q96)
open P2Winner9PhysicalAffineTransfer (physicalUpperIntegrand)
open P2Winner9SelectedRowAnalyticCaps (vertices means)
open P2Winner9SelectedRowQ6Floor (originalQ6Floor original_Q6_floor_actual_integral)
open P2Winner9SelectedRowRealJacobian (sourceSupport)

/-- The two ordinals in the original seed block. -/
def sourceIndex (r : Fin 2) : ℕ := 21 + r.val

def archiveRow (r : Fin 2) : RawRow := P2Winner9CompleteSeedBlock00.rows[sourceIndex r]!

def archiveVertices (r : Fin 2) (i : Fin 9) : Fin 8 → ℚ :=
  P2Winner9CompleteSeedVertices.coordinates[(archiveRow r).vertexIds i]!

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem archive_row_identifiers : ∀ r : Fin 2,
    (archiveRow r).parentId = sourceIndex r ∧ (archiveRow r).mixedId = sourceIndex r := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem archive_vertex_lookup : ∀ (r : Fin 2) (i : Fin 9) (j : Fin 8),
    archiveVertices r i j = vertices r i j := by
  decide +kernel

/-- Every ordered coordinate agrees with the row used in the physical proof. -/
theorem archive_vertices_eq (r : Fin 2) : archiveVertices r = vertices r := by
  funext i j
  exact archive_vertex_lookup r i j

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
private theorem archive_means_lookup : ∀ (r : Fin 2) (j : Fin 10), (archiveRow r).means j = means r j := by
  decide +kernel

theorem archive_means_eq (r : Fin 2) : (archiveRow r).means = means r :=
  funext (archive_means_lookup r)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem archive_floor_fields : ∀ r : Fin 2,
    (archiveRow r).mixedRaw = originalQ6Floor r ∧
      (archiveRow r).mixedSelected = originalQ6Floor r := by
  decide +kernel

theorem archive_support_eq (r : Fin 2) :
    sourceSupport (archiveVertices r) = sourceSupport (vertices r) :=
  congrArg sourceSupport (archive_vertices_eq r)

/-- The selected Q96 value of either archive row bounds its own physical integral. -/
theorem archive_selected_floor (r : Fin 2) :
    ((archiveRow r).mixedSelected : ℝ) / (q96 : ℝ) ≤
      ∫ z in sourceSupport (archiveVertices r), physicalUpperIntegrand z := by
  rw [(archive_floor_fields r).2, archive_support_eq r]
  exact original_Q6_floor_actual_integral r

end

end ImbalancedChen.P2Winner9SelectedRowArchiveBinding
