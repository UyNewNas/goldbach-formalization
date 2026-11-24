import ImbalancedChen.P2Winner9CompleteSeedVertices
import ImbalancedChen.P2Winner9SelectedRowRealJacobian

/-! Bind the physical affine maps for the two selected Winner9 rows to the
ordered vertices in the original parent-nine coordinate table. -/

namespace ImbalancedChen.P2Winner9SelectedVertexBinding

open P2Winner9CompleteSeedVertices P2Winner9PhysicalAffineTransfer
open P2Winner9PhysicalVertexInterpolation P2Winner9SelectedRowEdgeGeometry
open P2Winner9SelectedRowRealJacobian

noncomputable section

/-- The original table is indexed by witness vertex ID. -/
def archiveVertex (id : ℕ) : Ambient := fun j => (coordinates[id]! j : ℝ)

theorem row21_coordinates : ∀ i : Fin 9,
    row21VertexIds i < coordinates.size ∧
    ∀ j : Fin 8, row21 i j = coordinates[row21VertexIds i]! j := by
  decide +kernel

theorem row22_coordinates : ∀ i : Fin 9,
    row22VertexIds i < coordinates.size ∧
    ∀ j : Fin 8, row22 i j = coordinates[row22VertexIds i]! j := by
  decide +kernel

private theorem selectedVertexMatch_of_coordinates
    (v : RationalVertices) (hv : (edgeMatrix v).det ≠ 0) (ids : Fin 9 → ℕ)
    (h : ∀ i : Fin 9, ∀ j : Fin 8, v i j = coordinates[ids i]! j) :
    selectedVertexMatch (realCLE v hv) archiveVertex ids := by
  have hVertex (i : Fin 9) : realVertices v i = archiveVertex (ids i) := by
    funext j
    exact congrArg (fun q : ℚ => (q : ℝ)) (h i j)
  intro i
  change affinePoint (realCLE v hv) (archiveVertex (ids 0)) (Pi.single i 1) =
    archiveVertex (ids i.succ)
  calc
    _ = affinePoint (realCLE v hv) (realVertices v 0) (Pi.single i 1) :=
      congrArg (fun b => affinePoint (realCLE v hv) b (Pi.single i 1)) (hVertex 0).symm
    _ = vertexMap (realVertices v) (Pi.single i 1) :=
      affinePoint_eq_vertexMap v hv (Pi.single i 1)
    _ = realVertices v i.succ := vertexMap_single (realVertices v) i
    _ = archiveVertex (ids i.succ) := hVertex i.succ

theorem row21_selectedVertexMatch : selectedVertexMatch row21CLE archiveVertex row21VertexIds :=
  selectedVertexMatch_of_coordinates row21 row21_det_ne_zero row21VertexIds
    (fun i => (row21_coordinates i).2)

theorem row22_selectedVertexMatch : selectedVertexMatch row22CLE archiveVertex row22VertexIds :=
  selectedVertexMatch_of_coordinates row22 row22_det_ne_zero row22VertexIds
    (fun i => (row22_coordinates i).2)

end

end ImbalancedChen.P2Winner9SelectedVertexBinding
