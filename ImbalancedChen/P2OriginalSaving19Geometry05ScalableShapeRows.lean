import ImbalancedChen.P2OriginalSaving19Geometry05ScalableRowsNode000To006

/-! Finite shape for all 56 original typed rows, by existing local facts and balanced membership.
All input lists come from the original parser-bound typed leaf networks.
This source-only candidate has no geometric or integral interpretation. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape.Rows
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding

noncomputable def RowShape (vertexCount : Nat) (row : GeometryRow) : Prop :=
  row.vertexIds.size = 9 ∧ row.vertexIds.toList.Nodup ∧
  (∀ i : Fin 9, row.vertexIds[i.val]! < vertexCount) ∧
  row.factorMaxima.size = 10 ∧ row.gapWeightedMeans.size = 10

theorem rows_000_to_000_shape : ∀ row ∈ geometryRowsTypedBlock000, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock000, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow000_shape.2
  · exact geometryRow001_shape.2
  · exact geometryRow002_shape.2
  · exact geometryRow003_shape.2
  · exact geometryRow004_shape.2
  · exact geometryRow005_shape.2
  · exact geometryRow006_shape.2
  · exact geometryRow007_shape.2

theorem rows_001_to_001_shape : ∀ row ∈ geometryRowsTypedBlock001, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock001, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow008_shape.2
  · exact geometryRow009_shape.2
  · exact geometryRow010_shape.2
  · exact geometryRow011_shape.2
  · exact geometryRow012_shape.2
  · exact geometryRow013_shape.2
  · exact geometryRow014_shape.2
  · exact geometryRow015_shape.2

theorem rows_002_to_002_shape : ∀ row ∈ geometryRowsTypedBlock002, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock002, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow016_shape.2
  · exact geometryRow017_shape.2
  · exact geometryRow018_shape.2
  · exact geometryRow019_shape.2
  · exact geometryRow020_shape.2
  · exact geometryRow021_shape.2
  · exact geometryRow022_shape.2
  · exact geometryRow023_shape.2

theorem rows_003_to_003_shape : ∀ row ∈ geometryRowsTypedBlock003, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock003, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow024_shape.2
  · exact geometryRow025_shape.2
  · exact geometryRow026_shape.2
  · exact geometryRow027_shape.2
  · exact geometryRow028_shape.2
  · exact geometryRow029_shape.2
  · exact geometryRow030_shape.2
  · exact geometryRow031_shape.2

theorem rows_004_to_004_shape : ∀ row ∈ geometryRowsTypedBlock004, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock004, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow032_shape.2
  · exact geometryRow033_shape.2
  · exact geometryRow034_shape.2
  · exact geometryRow035_shape.2
  · exact geometryRow036_shape.2
  · exact geometryRow037_shape.2
  · exact geometryRow038_shape.2
  · exact geometryRow039_shape.2

theorem rows_005_to_005_shape : ∀ row ∈ geometryRowsTypedBlock005, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock005, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow040_shape.2
  · exact geometryRow041_shape.2
  · exact geometryRow042_shape.2
  · exact geometryRow043_shape.2
  · exact geometryRow044_shape.2
  · exact geometryRow045_shape.2
  · exact geometryRow046_shape.2
  · exact geometryRow047_shape.2

theorem rows_006_to_006_shape : ∀ row ∈ geometryRowsTypedBlock006, RowShape 28 row := by
  intro item hitem
  simp only [geometryRowsTypedBlock006, List.mem_cons, List.not_mem_nil, or_false] at hitem
  rcases hitem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geometryRow048_shape.2
  · exact geometryRow049_shape.2
  · exact geometryRow050_shape.2
  · exact geometryRow051_shape.2
  · exact geometryRow052_shape.2
  · exact geometryRow053_shape.2
  · exact geometryRow054_shape.2
  · exact geometryRow055_shape.2

theorem rows_000_to_001_shape : ∀ row ∈ Node000To001.typedRows, RowShape 28 row := by
  intro row hrow
  change row ∈ geometryRowsTypedBlock000 ++ geometryRowsTypedBlock001 at hrow
  exact (List.mem_append.mp hrow).elim (rows_000_to_000_shape row) (rows_001_to_001_shape row)

theorem rows_002_to_003_shape : ∀ row ∈ Node002To003.typedRows, RowShape 28 row := by
  intro row hrow
  change row ∈ geometryRowsTypedBlock002 ++ geometryRowsTypedBlock003 at hrow
  exact (List.mem_append.mp hrow).elim (rows_002_to_002_shape row) (rows_003_to_003_shape row)

theorem rows_004_to_005_shape : ∀ row ∈ Node004To005.typedRows, RowShape 28 row := by
  intro row hrow
  change row ∈ geometryRowsTypedBlock004 ++ geometryRowsTypedBlock005 at hrow
  exact (List.mem_append.mp hrow).elim (rows_004_to_004_shape row) (rows_005_to_005_shape row)

theorem rows_000_to_003_shape : ∀ row ∈ Node000To003.typedRows, RowShape 28 row := by
  intro row hrow
  change row ∈ Node000To001.typedRows ++ Node002To003.typedRows at hrow
  exact (List.mem_append.mp hrow).elim (rows_000_to_001_shape row) (rows_002_to_003_shape row)

theorem rows_004_to_006_shape : ∀ row ∈ Node004To006.typedRows, RowShape 28 row := by
  intro row hrow
  change row ∈ Node004To005.typedRows ++ geometryRowsTypedBlock006 at hrow
  exact (List.mem_append.mp hrow).elim (rows_004_to_005_shape row) (rows_006_to_006_shape row)

theorem rows_000_to_006_shape : ∀ row ∈ Node000To006.typedRows, RowShape 28 row := by
  intro row hrow
  change row ∈ Node000To003.typedRows ++ Node004To006.typedRows at hrow
  exact (List.mem_append.mp hrow).elim (rows_000_to_003_shape row) (rows_004_to_006_shape row)

theorem row_identifiers_block_000 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[0 + r.val]!).simplexId = 0 + r.val := by
  decide +kernel

theorem row_identifiers_block_001 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[8 + r.val]!).simplexId = 8 + r.val := by
  decide +kernel

theorem row_identifiers_block_002 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[16 + r.val]!).simplexId = 16 + r.val := by
  decide +kernel

theorem row_identifiers_block_003 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[24 + r.val]!).simplexId = 24 + r.val := by
  decide +kernel

theorem row_identifiers_block_004 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[32 + r.val]!).simplexId = 32 + r.val := by
  decide +kernel

theorem row_identifiers_block_005 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[40 + r.val]!).simplexId = 40 + r.val := by
  decide +kernel

theorem row_identifiers_block_006 : ∀ r : Fin 8,
    (Node000To006.typedRows.toArray[48 + r.val]!).simplexId = 48 + r.val := by
  decide +kernel

theorem all_row_identifiers : ∀ r : Fin 56,
    (Node000To006.typedRows.toArray[r.val]!).simplexId = r.val := by
  intro r
  have hr := r.isLt
  by_cases h0 : r.val < 8
  · simpa only [Nat.zero_add] using row_identifiers_block_000 ⟨r.val, h0⟩
  ·
    by_cases h1 : r.val < 16
    · have hb : r.val - 8 < 8 := by omega
      have he : 8 + (r.val - 8) = r.val := by omega
      simpa only [he] using row_identifiers_block_001 ⟨r.val - 8, hb⟩
    ·
      by_cases h2 : r.val < 24
      · have hb : r.val - 16 < 8 := by omega
        have he : 16 + (r.val - 16) = r.val := by omega
        simpa only [he] using row_identifiers_block_002 ⟨r.val - 16, hb⟩
      ·
        by_cases h3 : r.val < 32
        · have hb : r.val - 24 < 8 := by omega
          have he : 24 + (r.val - 24) = r.val := by omega
          simpa only [he] using row_identifiers_block_003 ⟨r.val - 24, hb⟩
        ·
          by_cases h4 : r.val < 40
          · have hb : r.val - 32 < 8 := by omega
            have he : 32 + (r.val - 32) = r.val := by omega
            simpa only [he] using row_identifiers_block_004 ⟨r.val - 32, hb⟩
          ·
            by_cases h5 : r.val < 48
            · have hb : r.val - 40 < 8 := by omega
              have he : 40 + (r.val - 40) = r.val := by omega
              simpa only [he] using row_identifiers_block_005 ⟨r.val - 40, hb⟩
            ·
              have hb : r.val - 48 < 8 := by omega
              have he : 48 + (r.val - 48) = r.val := by omega
              simpa only [he] using row_identifiers_block_006 ⟨r.val - 48, hb⟩

#print axioms rows_000_to_000_shape
#print axioms rows_001_to_001_shape
#print axioms rows_002_to_002_shape
#print axioms rows_003_to_003_shape
#print axioms rows_004_to_004_shape
#print axioms rows_005_to_005_shape
#print axioms rows_006_to_006_shape
#print axioms rows_000_to_001_shape
#print axioms rows_002_to_003_shape
#print axioms rows_004_to_005_shape
#print axioms rows_000_to_003_shape
#print axioms rows_004_to_006_shape
#print axioms rows_000_to_006_shape
#print axioms row_identifiers_block_000
#print axioms row_identifiers_block_001
#print axioms row_identifiers_block_002
#print axioms row_identifiers_block_003
#print axioms row_identifiers_block_004
#print axioms row_identifiers_block_005
#print axioms row_identifiers_block_006
#print axioms all_row_identifiers
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape.Rows
