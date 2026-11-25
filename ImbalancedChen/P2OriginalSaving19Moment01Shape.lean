import ImbalancedChen.P2OriginalSaving19Moment01Decoded

/-! Exact shape of the already decoded original moment cell01.
All 144 original rows are included. The assertions only bind metadata,
row IDs, array sizes and bounded lookups; no saved floor validity is asserted. -/
namespace ImbalancedChen.P2OriginalSaving19Moment01Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Moment01Decoding

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01_SHAPE before_metadata"
  err.flush

theorem metadata :
    momentConcrete01.cellId = 1 ∧
    momentConcrete01.sourceWitness =
      "eighth-third-minorant-extension-20261009-a23-s23_low-01-cell.witness.json" ∧
    momentConcrete01.dimension = 8 ∧
    momentConcrete01.verticesPerSimplex = 9 ∧
    momentConcrete01.factorCount = 10 ∧
    momentConcrete01.logDegree = 6 ∧
    momentConcrete01.expDegree = 3 ∧
    momentConcrete01.logDenominator = 2^80 ∧
    momentConcrete01.finalDenominator = 2^96 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01_SHAPE metadata_complete"
  err.flush

theorem row_count : momentConcrete01.rows.size = 144 := by rfl

theorem row_bound (i : Fin 144) : i.val < momentConcrete01.rows.size := by
  rw [row_count]
  exact i.isLt

theorem row_lookup_no_fallback (i : Fin 144) :
    momentConcrete01.rows[i.val]! = momentConcrete01.rows[i.val]'(row_bound i) :=
  getElem!_pos momentConcrete01.rows i.val (row_bound i)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01_SHAPE before_all_row_ids_and_sizes"
  err.flush

theorem row_ids_and_floor_sizes : ∀ i : Fin 144,
    (momentConcrete01.rows[i.val]!).simplexId = i.val ∧
    (momentConcrete01.rows[i.val]!).factorFloorsQ80.size = 10 := by
  decide +kernel

theorem row_ids_and_floor_sizes_bounded (i : Fin 144) :
    (momentConcrete01.rows[i.val]'(row_bound i)).simplexId = i.val ∧
    (momentConcrete01.rows[i.val]'(row_bound i)).factorFloorsQ80.size = 10 := by
  rw [← row_lookup_no_fallback]
  exact row_ids_and_floor_sizes i

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT01_SHAPE all_144_rows_complete"
  err.flush

#print axioms metadata
#print axioms row_count
#print axioms row_bound
#print axioms row_lookup_no_fallback
#print axioms row_ids_and_floor_sizes
#print axioms row_ids_and_floor_sizes_bounded
end ImbalancedChen.P2OriginalSaving19Moment01Shape
