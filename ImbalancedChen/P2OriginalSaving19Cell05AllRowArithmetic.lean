import ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps
import ImbalancedChen.P2Winner9FastDetPure

/-! Ten finite geometry checks for the 56 original Cell05 rows.
The ordered points come from each decoded row's own vertex IDs.
The Q96 integer in this theorem belongs to the geometry Jensen record. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05AllRowArithmetic

open P2OriginalSaving19Archive
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19Geometry05ScalableDecoding
open P2OriginalSaving19Geometry05ScalableDecoding.Complete
open P2OriginalSaving19Cell05AllRowGaps

set_option maxRecDepth 1000000
set_option Elab.async false

noncomputable section

private def rowVertices (row : GeometryRow) (i : Fin 9) (j : Fin 8) : ℚ :=
  (concreteGeometry05.vertices[row.vertexIds[i.val]!]!)[j.val]!

/-- The finite arithmetic still needed once the two gap facts are available.
Positive stored volume and the kernel-computable determinant formula imply
both the standard volume equation and nondegeneracy. -/
private abbrev Remaining (v : Fin 9 → QPoint) (g : GeometryRow) : Prop :=
  0 < g.physicalVolume ∧
  (∀ i : Fin 9, PhysicalQ (v i)) ∧
  g.physicalVolume = |P2Winner9FastDetPure.fastDet (edgeOf v)| / (Nat.factorial 8 : ℚ) ∧
  (∀ j : Fin 10, meansOf g j = computedMeanOf v j) ∧
  (∀ i : Fin 9, ∀ j : Fin 10, factorsQ (v i) j ≤ topsOf g j) ∧
  (∀ j : Fin 10, ∃ i : Fin 9, factorsQ (v i) j = topsOf g j) ∧
  g.jensenBound = oldEvaluator (massOf g) (meansOf g) ∧
  g.jensenFloorQ96 = oldFloorQ96 (massOf g) (meansOf g)

private abbrev RemainingForRow (row : GeometryRow) : Prop :=
  Remaining (rowVertices row) row

private theorem assemble {v : Fin 9 → QPoint} {g : GeometryRow}
    (remaining : Remaining v g)
    (gaps : 0 < gapSumOf v ∧ g.meanGap = gapSumOf v / 9) : RowDataChecksFor v g := by
  rcases remaining with ⟨hpos, hphys, hvol, hmeans, hdom, hatt, hjensen, hfloor⟩
  rw [P2Winner9FastDetPure.fastDet_eq (edgeOf v)] at hvol
  have hdet : (edgeOf v).det ≠ 0 := by
    intro hz
    have hzero := hvol
    rw [hz, abs_zero, zero_div] at hzero
    exact (ne_of_gt hpos) hzero
  exact ⟨hdet, hphys, gaps.1, hvol, gaps.2, hmeans, hdom, hatt, hjensen, hfloor⟩

private theorem rows_00_07 : ∀ row ∈ geometryRowsTypedBlock000, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock000, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rows_08_15 : ∀ row ∈ geometryRowsTypedBlock001, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock001, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rows_16_23 : ∀ row ∈ geometryRowsTypedBlock002, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock002, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rows_24_31 : ∀ row ∈ geometryRowsTypedBlock003, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock003, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rows_32_39 : ∀ row ∈ geometryRowsTypedBlock004, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock004, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rows_40_47 : ∀ row ∈ geometryRowsTypedBlock005, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock005, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem rows_48_55 : ∀ row ∈ geometryRowsTypedBlock006, RemainingForRow row := by
  intro row h
  simp only [geometryRowsTypedBlock006, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem append_rows {xs ys : List GeometryRow}
    (left : ∀ row ∈ xs, RemainingForRow row) (right : ∀ row ∈ ys, RemainingForRow row) :
    ∀ row ∈ xs ++ ys, RemainingForRow row := by
  intro row h
  exact (List.mem_append.mp h).elim (left row) (right row)

private theorem all_remaining : ∀ row ∈ Node000To006.typedRows, RemainingForRow row := by
  have h01 : ∀ row ∈ Node000To001.typedRows, RemainingForRow row :=
    append_rows rows_00_07 rows_08_15
  have h23 : ∀ row ∈ Node002To003.typedRows, RemainingForRow row :=
    append_rows rows_16_23 rows_24_31
  have h45 : ∀ row ∈ Node004To005.typedRows, RemainingForRow row :=
    append_rows rows_32_39 rows_40_47
  have h03 : ∀ row ∈ Node000To003.typedRows, RemainingForRow row := append_rows h01 h23
  have h46 : ∀ row ∈ Node004To006.typedRows, RemainingForRow row := append_rows h45 rows_48_55
  exact append_rows h03 h46

theorem all_bounded_row_data_checks (r : Fin 56) :
    RowDataChecksFor (boundedRowVertex05 r) (boundedRow05 r) := by
  have h : RemainingForRow (boundedRow05 r) := by
    rw [boundedRow05_eq_raw]
    change RemainingForRow (Node000To006.typedRows.toArray[r.val]!)
    exact P2OriginalSaving19Geometry05ScalableShape.property_of_list_toArray
      Node000To006.typedRows RemainingForRow all_remaining r.val (by
        change r.val < 56
        exact r.isLt)
  have hv : rowVertices (boundedRow05 r) = boundedRowVertex05 r := by
    funext i j
    exact (congrArg (fun row : GeometryRow => rowVertices row i j) (boundedRow05_eq_raw r)).trans
      (boundedRowVertex05_eq_raw r i j).symm
  change Remaining (rowVertices (boundedRow05 r)) (boundedRow05 r) at h
  rw [hv] at h
  exact assemble h (all_row_gaps r)

theorem all_raw_row_data_checks (r : Fin 56) :
    RowDataChecksFor
      (fun i j =>
        (concreteGeometry05.vertices[(concreteGeometry05.rows[r.val]!).vertexIds[i.val]!]!)[j.val]!)
      (concreteGeometry05.rows[r.val]!) := by
  have hv : boundedRowVertex05 r = rowVertices (concreteGeometry05.rows[r.val]!) := by
    funext i j
    exact boundedRowVertex05_eq_raw r i j
  have h := all_bounded_row_data_checks r
  rw [hv, boundedRow05_eq_raw] at h
  exact h

#print axioms rowVertices
#print axioms Remaining
#print axioms RemainingForRow
#print axioms assemble
#print axioms rows_00_07
#print axioms rows_08_15
#print axioms rows_16_23
#print axioms rows_24_31
#print axioms rows_32_39
#print axioms rows_40_47
#print axioms rows_48_55
#print axioms append_rows
#print axioms all_remaining
#print axioms all_bounded_row_data_checks
#print axioms all_raw_row_data_checks

end
end ImbalancedChen.P2OriginalSaving19Cell05AllRowArithmetic
