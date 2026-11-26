import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows000
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows001
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows002
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows003
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows004
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows005
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows006
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows007
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows008
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows009
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows010
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows011
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows012
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows013
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows014
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows015
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows016
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeRows017
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeVertices000
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeVertices001
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeVertices002
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeVertices003
import ImbalancedChen.P2OriginalSaving19Geometry01ShapeVertices004

/-! Complete shape of all 144 original cell01 rows and all 40 original vertices.
These claims concern the concrete output of the original cell01 decoder.
Finite checks are split into at most eight records per theorem. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Geometry01Decoding

theorem all_rows : ∀ r : Fin 144,
    let g := concreteGeometry01.rows[r.val]!
    g.simplexId = r.val ∧
    g.vertexIds.size = 9 ∧ g.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, g.vertexIds[i.val]! < concreteGeometry01.vertices.size) ∧
    g.factorMaxima.size = 10 ∧ g.gapWeightedMeans.size = 10 := by
  intro r
  have hr := r.isLt
  by_cases h0 : r.val < 8
  · simpa only [Nat.zero_add] using rows_block_000 ⟨r.val, h0⟩
  ·
    by_cases h1 : r.val < 16
    · have hb : r.val - 8 < 8 := by omega
      have he : 8 + (r.val - 8) = r.val := by omega
      simpa only [he] using rows_block_001 ⟨r.val - 8, hb⟩
    ·
      by_cases h2 : r.val < 24
      · have hb : r.val - 16 < 8 := by omega
        have he : 16 + (r.val - 16) = r.val := by omega
        simpa only [he] using rows_block_002 ⟨r.val - 16, hb⟩
      ·
        by_cases h3 : r.val < 32
        · have hb : r.val - 24 < 8 := by omega
          have he : 24 + (r.val - 24) = r.val := by omega
          simpa only [he] using rows_block_003 ⟨r.val - 24, hb⟩
        ·
          by_cases h4 : r.val < 40
          · have hb : r.val - 32 < 8 := by omega
            have he : 32 + (r.val - 32) = r.val := by omega
            simpa only [he] using rows_block_004 ⟨r.val - 32, hb⟩
          ·
            by_cases h5 : r.val < 48
            · have hb : r.val - 40 < 8 := by omega
              have he : 40 + (r.val - 40) = r.val := by omega
              simpa only [he] using rows_block_005 ⟨r.val - 40, hb⟩
            ·
              by_cases h6 : r.val < 56
              · have hb : r.val - 48 < 8 := by omega
                have he : 48 + (r.val - 48) = r.val := by omega
                simpa only [he] using rows_block_006 ⟨r.val - 48, hb⟩
              ·
                by_cases h7 : r.val < 64
                · have hb : r.val - 56 < 8 := by omega
                  have he : 56 + (r.val - 56) = r.val := by omega
                  simpa only [he] using rows_block_007 ⟨r.val - 56, hb⟩
                ·
                  by_cases h8 : r.val < 72
                  · have hb : r.val - 64 < 8 := by omega
                    have he : 64 + (r.val - 64) = r.val := by omega
                    simpa only [he] using rows_block_008 ⟨r.val - 64, hb⟩
                  ·
                    by_cases h9 : r.val < 80
                    · have hb : r.val - 72 < 8 := by omega
                      have he : 72 + (r.val - 72) = r.val := by omega
                      simpa only [he] using rows_block_009 ⟨r.val - 72, hb⟩
                    ·
                      by_cases h10 : r.val < 88
                      · have hb : r.val - 80 < 8 := by omega
                        have he : 80 + (r.val - 80) = r.val := by omega
                        simpa only [he] using rows_block_010 ⟨r.val - 80, hb⟩
                      ·
                        by_cases h11 : r.val < 96
                        · have hb : r.val - 88 < 8 := by omega
                          have he : 88 + (r.val - 88) = r.val := by omega
                          simpa only [he] using rows_block_011 ⟨r.val - 88, hb⟩
                        ·
                          by_cases h12 : r.val < 104
                          · have hb : r.val - 96 < 8 := by omega
                            have he : 96 + (r.val - 96) = r.val := by omega
                            simpa only [he] using rows_block_012 ⟨r.val - 96, hb⟩
                          ·
                            by_cases h13 : r.val < 112
                            · have hb : r.val - 104 < 8 := by omega
                              have he : 104 + (r.val - 104) = r.val := by omega
                              simpa only [he] using rows_block_013 ⟨r.val - 104, hb⟩
                            ·
                              by_cases h14 : r.val < 120
                              · have hb : r.val - 112 < 8 := by omega
                                have he : 112 + (r.val - 112) = r.val := by omega
                                simpa only [he] using rows_block_014 ⟨r.val - 112, hb⟩
                              ·
                                by_cases h15 : r.val < 128
                                · have hb : r.val - 120 < 8 := by omega
                                  have he : 120 + (r.val - 120) = r.val := by omega
                                  simpa only [he] using rows_block_015 ⟨r.val - 120, hb⟩
                                ·
                                  by_cases h16 : r.val < 136
                                  · have hb : r.val - 128 < 8 := by omega
                                    have he : 128 + (r.val - 128) = r.val := by omega
                                    simpa only [he] using rows_block_016 ⟨r.val - 128, hb⟩
                                  ·
                                    have hb : r.val - 136 < 8 := by omega
                                    have he : 136 + (r.val - 136) = r.val := by omega
                                    simpa only [he] using rows_block_017 ⟨r.val - 136, hb⟩

theorem all_vertices_bang : ∀ r : Fin 40,
    (concreteGeometry01.vertices[r.val]!).size = 8 ∧
    (concreteGeometry01.vertexValues[r.val]!).factors.size = 10 := by
  intro r
  have hr := r.isLt
  by_cases h0 : r.val < 8
  · simpa only [Nat.zero_add] using vertices_block_000 ⟨r.val, h0⟩
  ·
    by_cases h1 : r.val < 16
    · have hb : r.val - 8 < 8 := by omega
      have he : 8 + (r.val - 8) = r.val := by omega
      simpa only [he] using vertices_block_001 ⟨r.val - 8, hb⟩
    ·
      by_cases h2 : r.val < 24
      · have hb : r.val - 16 < 8 := by omega
        have he : 16 + (r.val - 16) = r.val := by omega
        simpa only [he] using vertices_block_002 ⟨r.val - 16, hb⟩
      ·
        by_cases h3 : r.val < 32
        · have hb : r.val - 24 < 8 := by omega
          have he : 24 + (r.val - 24) = r.val := by omega
          simpa only [he] using vertices_block_003 ⟨r.val - 24, hb⟩
        ·
          have hb : r.val - 32 < 8 := by omega
          have he : 32 + (r.val - 32) = r.val := by omega
          simpa only [he] using vertices_block_004 ⟨r.val - 32, hb⟩

theorem all_vertices (v : Fin concreteGeometry01.vertices.size) :
    (concreteGeometry01.vertices[v]).size = 8 ∧
    (concreteGeometry01.vertexValues[v.val]!).factors.size = 10 := by
  have hv : v.val < 40 := by simpa only [vertex_count] using v.isLt
  have h := all_vertices_bang ⟨v.val, hv⟩
  rw [getElem!_pos concreteGeometry01.vertices v.val v.isLt] at h
  exact h

#print axioms all_rows
#print axioms all_vertices_bang
#print axioms all_vertices
end ImbalancedChen.P2OriginalSaving19Geometry01Shape
