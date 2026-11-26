import ImbalancedChen.P2OriginalSaving19Geometry01ShapeBase

/-! Original vertex and factor-array shape, records 32 through 39.
These claims concern the concrete output of the original cell01 decoder.
Finite checks are split into at most eight records per theorem. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry01Decoding

theorem vertices_block_004 : ∀ r : Fin 8,
    (concreteGeometry01.vertices[(32 + r.val)]!).size = 8 ∧
    (concreteGeometry01.vertexValues[(32 + r.val)]!).factors.size = 10 := by
  decide +kernel

#print axioms vertices_block_004
end ImbalancedChen.P2OriginalSaving19Geometry01Shape
