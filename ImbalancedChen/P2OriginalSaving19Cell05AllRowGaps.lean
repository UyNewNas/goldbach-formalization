import ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape
import ImbalancedChen.P2OriginalSaving19RowNumericsPure

/-! The positive gap sum and the stored mean gap for all 56 original Cell05
geometry rows. Each point is selected by the row's own ordered vertex IDs. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps

open P2OriginalSaving19Archive
open P2OriginalSaving19Geometry05ScalableDecoding.Complete
open P2OriginalSaving19RowNumericsPure

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

private theorem row_bound (r : Fin 56) : r.val < concreteGeometry05.rows.size := by
  rw [P2OriginalSaving19Geometry05ScalableShape.row_count]
  exact r.isLt

def boundedRow05 (r : Fin 56) : GeometryRow :=
  concreteGeometry05.rows[r.val]'(row_bound r)

theorem boundedRow05_eq_raw (r : Fin 56) :
    boundedRow05 r = concreteGeometry05.rows[r.val]! :=
  (getElem!_pos concreteGeometry05.rows r.val (row_bound r)).symm

private theorem vertex_id_bound (r : Fin 56) (i : Fin 9) :
    i.val < (boundedRow05 r).vertexIds.size := by
  rw [boundedRow05_eq_raw, (P2OriginalSaving19Geometry05ScalableShape.all_rows r).2.1]
  exact i.isLt

private theorem vertex_id_eq_raw (r : Fin 56) (i : Fin 9) :
    (boundedRow05 r).vertexIds[i.val]'(vertex_id_bound r i) =
      (concreteGeometry05.rows[r.val]!).vertexIds[i.val]! := by
  calc
    _ = (boundedRow05 r).vertexIds[i.val]! :=
      (getElem!_pos (boundedRow05 r).vertexIds i.val (vertex_id_bound r i)).symm
    _ = _ := by rw [boundedRow05_eq_raw]

private def vertexIndex05 (r : Fin 56) (i : Fin 9) : Fin concreteGeometry05.vertices.size :=
  ⟨(boundedRow05 r).vertexIds[i.val]'(vertex_id_bound r i), by
    rw [vertex_id_eq_raw]
    exact (P2OriginalSaving19Geometry05ScalableShape.all_rows r).2.2.2.1 i⟩

private theorem coordinate_bound (v : Fin concreteGeometry05.vertices.size) (j : Fin 8) :
    j.val < (concreteGeometry05.vertices[v.val]'v.isLt).size := by
  have hv : v.val < 28 := by
    simpa only [P2OriginalSaving19Geometry05ScalableShape.vertex_count] using v.isLt
  have h := (P2OriginalSaving19Geometry05ScalableShape.all_vertices ⟨v.val, hv⟩).1
  calc
    j.val < 8 := j.isLt
    _ = (concreteGeometry05.vertices[v.val]'v.isLt).size := by
      rw [← getElem!_pos concreteGeometry05.vertices v.val v.isLt]
      exact (h.trans P2OriginalSaving19Geometry05ScalableShape.dimension).symm

def boundedRowVertex05 (r : Fin 56) (i : Fin 9) (j : Fin 8) : ℚ :=
  let v := vertexIndex05 r i
  (concreteGeometry05.vertices[v.val]'v.isLt)[j.val]'(coordinate_bound v j)

theorem boundedRowVertex05_eq_raw (r : Fin 56) (i : Fin 9) (j : Fin 8) :
    boundedRowVertex05 r i j =
      (concreteGeometry05.vertices[(concreteGeometry05.rows[r.val]!).vertexIds[i.val]!]!)[j.val]! := by
  let v := vertexIndex05 r i
  have hv : v.val = (concreteGeometry05.rows[r.val]!).vertexIds[i.val]! := vertex_id_eq_raw r i
  calc
    boundedRowVertex05 r i j = (concreteGeometry05.vertices[v.val]'v.isLt)[j.val]! :=
      (getElem!_pos (concreteGeometry05.vertices[v.val]'v.isLt) j.val (coordinate_bound v j)).symm
    _ = (concreteGeometry05.vertices[v.val]!)[j.val]! := by
      rw [getElem!_pos concreteGeometry05.vertices v.val v.isLt]
    _ = _ := by rw [hv]

private abbrev rawRowVertex (n : Nat) (i : Fin 9) (j : Fin 8) : ℚ :=
  (concreteGeometry05.vertices[(concreteGeometry05.rows[n]!).vertexIds[i.val]!]!)[j.val]!

private abbrev RawGapChecks (n : Nat) : Prop :=
  0 < gapSumOf (rawRowVertex n) ∧ (concreteGeometry05.rows[n]!).meanGap = gapSumOf (rawRowVertex n) / 9

private theorem gaps_00_07 : ∀ i : Fin 8, RawGapChecks i.val := by decide +kernel
private theorem gaps_08_15 : ∀ i : Fin 8, RawGapChecks (8 + i.val) := by decide +kernel
private theorem gaps_16_23 : ∀ i : Fin 8, RawGapChecks (16 + i.val) := by decide +kernel
private theorem gaps_24_31 : ∀ i : Fin 8, RawGapChecks (24 + i.val) := by decide +kernel
private theorem gaps_32_39 : ∀ i : Fin 8, RawGapChecks (32 + i.val) := by decide +kernel
private theorem gaps_40_47 : ∀ i : Fin 8, RawGapChecks (40 + i.val) := by decide +kernel
private theorem gaps_48_55 : ∀ i : Fin 8, RawGapChecks (48 + i.val) := by decide +kernel

private theorem append_blocks {P : Nat → Prop} (a b : Nat)
    (left : ∀ i : Fin a, P i.val) (right : ∀ i : Fin b, P (a + i.val))
    (i : Fin (a + b)) : P i.val := by
  by_cases h : i.val < a
  · exact left ⟨i.val, h⟩
  · have hi := i.isLt
    have hb : i.val - a < b := by omega
    have he : a + (i.val - a) = i.val := by omega
    simpa only [he] using right ⟨i.val - a, hb⟩

theorem all_row_gaps (r : Fin 56) :
    0 < gapSumOf (boundedRowVertex05 r) ∧
      (boundedRow05 r).meanGap = gapSumOf (boundedRowVertex05 r) / 9 := by
  have h16 := append_blocks (P := RawGapChecks) 8 8 gaps_00_07 gaps_08_15
  have h24 := append_blocks (P := RawGapChecks) 16 8 h16 gaps_16_23
  have h32 := append_blocks (P := RawGapChecks) 24 8 h24 gaps_24_31
  have h40 := append_blocks (P := RawGapChecks) 32 8 h32 gaps_32_39
  have h48 := append_blocks (P := RawGapChecks) 40 8 h40 gaps_40_47
  have h56 := append_blocks (P := RawGapChecks) 48 8 h48 gaps_48_55
  have hv : boundedRowVertex05 r = rawRowVertex r.val := by
    funext i j
    exact boundedRowVertex05_eq_raw r i j
  rw [hv, boundedRow05_eq_raw]
  exact h56 r

#print axioms row_bound
#print axioms boundedRow05
#print axioms boundedRow05_eq_raw
#print axioms vertex_id_bound
#print axioms vertex_id_eq_raw
#print axioms vertexIndex05
#print axioms coordinate_bound
#print axioms boundedRowVertex05
#print axioms boundedRowVertex05_eq_raw
#print axioms rawRowVertex
#print axioms RawGapChecks
#print axioms gaps_00_07
#print axioms gaps_08_15
#print axioms gaps_16_23
#print axioms gaps_24_31
#print axioms gaps_32_39
#print axioms gaps_40_47
#print axioms gaps_48_55
#print axioms append_blocks
#print axioms all_row_gaps

end
end ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps
