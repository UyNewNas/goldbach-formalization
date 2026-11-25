import ImbalancedChen.P2OriginalSaving19OwnedSource
import ImbalancedChen.P2OriginalSaving19PullingFiniteCodes
import ImbalancedChen.P2Winner9LiftingGeometry

/-!
SOURCE CANDIDATE / UNCOMPILED / ZERO ORIGINAL-DATA ACCEPTANCE CREDIT.

The original thirteen-cell rows are connected to the existing checked pulling
theorem. Closed proof requests below still require the actual Archive, shape and
gate suppliers. No Winner9 points, flags, ranks or numerical certificates are used.
The old explicit adjugate/polynomial-face identities are not asserted here.
-/
namespace ImbalancedChen.P2OriginalSaving19PullingReuse

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open P2OriginalThirdMinorantLogDictionarySourceOnly
open P2OriginalSaving19SimplexMoments
open P2OriginalSaving19MomentFloorConsumer
open P2OriginalSaving19Archive
open P2OriginalSaving19Original28918
open P2OriginalSaving19OwnedSource
open P2OriginalSaving19PullingFiniteCodes
open P2Winner9LiftingGeometry

/-- Bounded positions in the actual global facet array. The distinct producer
`facetOriginalIndices` are not Fin 97 indices and are never coerced here. -/
abbrev FacetIndex (c : Fin 13) := Fin (geometry c).facetVertices.size

def rowID (c : Fin 13) (i : CellRow c) (k : Fin 9) : VertexIndex c :=
  ⟨vertexId ⟨c, i⟩ k, vertexId_bound ⟨c, i⟩ k⟩

def facetMask (c : Fin 13) (f : FacetIndex c) : Nat :=
  vertexMask (geometry c).facetVertices[f.val]!.toList

/-- This is a projection of actual records, not a replacement face table. -/
def originalLedger (c : Fin 13) : List LedgerFace :=
  (geometry c).faces.toList.map fun f =>
    ⟨f.vertices.toList, f.pivot, f.facetSets.toList.map (fun s => s.toList)⟩

def flagTrace (c : Fin 13) (i : CellRow c) : Option (List (FacetIndex c)) :=
  traceFlags (originalLedger c) (geometry c).facetVertices 9
    (List.range (geometry c).vertices.size) (List.ofFn (vertexId ⟨c, i⟩))

def rowFlags (c : Fin 13) (i : CellRow c) : List (FacetIndex c) :=
  (flagTrace c i).getD []

def rowKey (c : Fin 13) (i : CellRow c) : Nat :=
  vertexMask (List.ofFn (vertexId ⟨c, i⟩))

/-- Exact old original_pulling_checks.3 obligation, separated from the old
unevaluated guard. Every original vertex participates in the zero-set equality.
This closed proof request has not been evaluated in this candidate task. -/
theorem original_facet_gate_checks :
    ∀ c (f : FacetIndex c), ∃ g : Fin 97, ∀ v : VertexIndex c,
      (v.val ∈ (geometry c).facetVertices[f.val]!.toList ↔
        evalQ (gate c g) (originalPoint c v) = 0) := by
  intro c
  fin_cases c <;> decide +kernel

/-- Full original row scope. The first conjunct rejects the Option fallback;
the second certifies all eight steps against the exact facet masks and IDs.
No success, coverage or null-overlap statement is an input. -/
theorem original_ledger_flag_checks : ∀ c (i : CellRow c),
    flagTrace c i = some (rowFlags c i) ∧
    pullingCheck (facetMask c) (2 ^ (geometry c).vertices.size - 1)
      (rowID c i 0) (rowTail (rowID c i)) (rowFlags c i) = true := by
  intro c
  fin_cases c <;> decide +kernel

/-- All original row keys are retained through a proved sorting permutation.
Only adjacent strict comparisons are evaluated; no pairwise row enumeration. -/
theorem original_sorted_key_checks : ∀ c,
    (sortedCodes (rowKey c)).IsChain (· < ·) := by
  intro c
  fin_cases c <;> decide +kernel

def facetGate (c : Fin 13) (f : FacetIndex c) : Fin 97 :=
  Classical.choose (original_facet_gate_checks c f)

def facetPlane (c : Fin 13) (f : FacetIndex c) : LiftingPlane :=
  ⟨gate c (facetGate c f) 0, fun j => gate c (facetGate c f) j.succ⟩

theorem facetPlane_evalQ (c : Fin 13) (f : FacetIndex c) (v : VertexIndex c) :
    (facetPlane c f).evalQ (originalPoint c v) =
      evalQ (gate c (facetGate c f)) (originalPoint c v) := rfl

theorem facetMask_correct (c : Fin 13) (f : FacetIndex c) (v : VertexIndex c) :
    (facetMask c f).testBit v.val = true ↔
      (facetPlane c f).evalQ (originalPoint c v) = 0 := by
  rw [facetPlane_evalQ]
  exact (vertexMask_testBit _ _).trans
    (Classical.choose_spec (original_facet_gate_checks c f) v)

theorem facetPlane_nonneg (c : Fin 13) (f : FacetIndex c) (v : VertexIndex c) :
    0 ≤ (facetPlane c f).evalQ (originalPoint c v) := by
  rw [facetPlane_evalQ]
  exact original_gate_checks.2 c v (facetGate c f)

theorem rowKey_injective (c : Fin 13) : Function.Injective (rowKey c) :=
  code_injective_of_sorted_chain _ (original_sorted_key_checks c)

theorem row_vertex_sets_injective (c : Fin 13) :
    Function.Injective (fun i : CellRow c => vertexSet (rowID c i)) := by
  intro i j hs
  apply rowKey_injective c
  apply vertexMask_eq_of_mem_iff
  intro v
  constructor
  · intro hv
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hv
    have hm : rowID c i k ∈ vertexSet (rowID c j) := by
      rw [← hs]
      exact mem_vertexSet.mpr ⟨k, rfl⟩
    obtain ⟨l, hl⟩ := mem_vertexSet.mp hm
    exact List.mem_ofFn.mpr ⟨l, (congrArg Fin.val hl).trans hk⟩
  · intro hv
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hv
    have hm : rowID c j k ∈ vertexSet (rowID c i) := by
      rw [hs]
      exact mem_vertexSet.mpr ⟨k, rfl⟩
    obtain ⟨l, hl⟩ := mem_vertexSet.mp hm
    exact List.mem_ofFn.mpr ⟨l, (congrArg Fin.val hl).trans hk⟩

/-- The two existing barycentric-map conventions differ only by commuting
scalar multiplication inside their finite sum. -/
theorem vertexMap_eq_pointInterpolate (v : Fin 9 → Point) (x : Point) :
    P2Winner9PhysicalVertexInterpolation.vertexMap v x = pointInterpolate v x := by
  ext j
  rw [P2Winner9PhysicalVertexInterpolation.vertexMap_coordinate,
    pointInterpolate_apply]
  unfold P2Winner9BarycentricMixedDegreeOne.affine interpolate
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem cellSupport_eq_actualSupport (c : Fin 13) (i : CellRow c) :
    cellSupport (originalPoint c) (rowID c) i = actualSupport ⟨c, i⟩ := by
  have hv :
      P2Winner9SelectedRowRealJacobian.realVertices
        (cellVertices (originalPoint c) (rowID c) i) =
          vertices (rowLinear ⟨c, i⟩) (rowBase ⟨c, i⟩) := by
    funext k
    rw [row_vertices]
    change realPoint (originalPoint c (rowID c i k)) = realPoint (rawVertex ⟨c, i⟩ k)
    rw [rawVertex_lookup]
    rfl
  change
    P2Winner9PhysicalVertexInterpolation.vertexMap
      (P2Winner9SelectedRowRealJacobian.realVertices
        (cellVertices (originalPoint c) (rowID c) i)) ''
      P2Winner9PhysicalAffineTransfer.canonicalSupport =
        (fun x => rowBase ⟨c, i⟩ + rowLinear ⟨c, i⟩ x) '' canonical
  rw [hv]
  have hm :
      P2Winner9PhysicalVertexInterpolation.vertexMap
        (vertices (rowLinear ⟨c, i⟩) (rowBase ⟨c, i⟩)) =
          (fun x => rowBase ⟨c, i⟩ + rowLinear ⟨c, i⟩ x) := by
    funext x
    rw [vertexMap_eq_pointInterpolate, vertices_interpolate]
  rw [hm]
  rfl

/-- Same conclusion consumed by OwnedIntegral, over every actual original row.
The existing generic pulling proof supplies the geometry and measure argument. -/
theorem original_within_cell_null_overlap (c : Fin 13) (i j : CellRow c) (hij : i ≠ j) :
    volume (actualSupport ⟨c, i⟩ ∩ actualSupport ⟨c, j⟩) = 0 := by
  have h := checked_pulling_overlap_null (originalPoint c) (facetPlane c) (facetMask c)
    (rowID c) (rowFlags c) (facetMask_correct c) (facetPlane_nonneg c)
    (fun i => (original_ledger_flag_checks c i).2) (row_vertex_sets_injective c)
  simpa only [cellSupport_eq_actualSupport] using h hij

end
end ImbalancedChen.P2OriginalSaving19PullingReuse
