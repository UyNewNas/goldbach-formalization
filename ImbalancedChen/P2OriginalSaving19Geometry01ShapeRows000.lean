import ImbalancedChen.P2OriginalSaving19Geometry01ShapeBase

/-! Original row shape, records 0 through 7.
These claims concern the concrete output of the original cell01 decoder.
Finite checks are split into at most eight records per theorem. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry01Decoding

theorem rows_block_000 : ∀ r : Fin 8,
    let g := concreteGeometry01.rows[(0 + r.val)]!
    g.simplexId = (0 + r.val) ∧
    g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, g.vertexIds[i.val]! < concreteGeometry01.vertices.size) ∧
    g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 := by
  decide +kernel

#print axioms rows_block_000
end ImbalancedChen.P2OriginalSaving19Geometry01Shape
