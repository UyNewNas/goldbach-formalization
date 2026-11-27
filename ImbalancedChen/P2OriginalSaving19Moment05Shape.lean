import ImbalancedChen.P2OriginalSaving19Moment05Decoded

/-! Exact shape of the already decoded original moment cell05.
All 56 original rows are included. The assertions only bind metadata,
row IDs, array sizes and bounded lookups; no saved floor validity is asserted. -/
namespace ImbalancedChen.P2OriginalSaving19Moment05Shape
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Moment05Decoding

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05_SHAPE before_metadata"
  err.flush

theorem metadata :
    momentConcrete05.cellId = 5 ∧
    momentConcrete05.sourceWitness =
      "eighth-third-minorant-extension-20261009-a23-s23_low-05-cell.witness.json" ∧
    momentConcrete05.dimension = 8 ∧
    momentConcrete05.verticesPerSimplex = 9 ∧
    momentConcrete05.factorCount = 10 ∧
    momentConcrete05.logDegree = 6 ∧
    momentConcrete05.expDegree = 3 ∧
    momentConcrete05.logDenominator = 2^80 ∧
    momentConcrete05.finalDenominator = 2^96 := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05_SHAPE metadata_complete"
  err.flush

theorem row_count : momentConcrete05.rows.size = 56 := by rfl

theorem row_bound (i : Fin 56) : i.val < momentConcrete05.rows.size := by
  rw [row_count]
  exact i.isLt

theorem row_lookup_no_fallback (i : Fin 56) :
    momentConcrete05.rows[i.val]! = momentConcrete05.rows[i.val]'(row_bound i) :=
  getElem!_pos momentConcrete05.rows i.val (row_bound i)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05_SHAPE before_all_row_ids_and_sizes"
  err.flush

theorem row_ids_and_floor_sizes : ∀ i : Fin 56,
    (momentConcrete05.rows[i.val]!).simplexId = i.val ∧
    (momentConcrete05.rows[i.val]!).factorFloorsQ80.size = 10 := by
  decide +kernel

theorem row_ids_and_floor_sizes_bounded (i : Fin 56) :
    (momentConcrete05.rows[i.val]'(row_bound i)).simplexId = i.val ∧
    (momentConcrete05.rows[i.val]'(row_bound i)).factorFloorsQ80.size = 10 := by
  rw [← row_lookup_no_fallback]
  exact row_ids_and_floor_sizes i

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT05_SHAPE all_56_rows_complete"
  err.flush

#print axioms metadata
#print axioms row_count
#print axioms row_bound
#print axioms row_lookup_no_fallback
#print axioms row_ids_and_floor_sizes
#print axioms row_ids_and_floor_sizes_bounded
end ImbalancedChen.P2OriginalSaving19Moment05Shape
