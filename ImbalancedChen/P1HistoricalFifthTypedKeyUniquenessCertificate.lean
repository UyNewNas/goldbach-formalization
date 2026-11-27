import ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore

namespace ImbalancedChen.P1HistoricalFifthTypedKeyPartition
open P1OriginalPrefixRowDecodeSoundness P1FifthGrid400UnitBoxPartition

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
/-- This is a closed term about all292633 actual typed source positions.
It is neither a supplied checker flag nor an archived-byte identity.
No decision reduction, checker or compiler was invoked by the author. -/
theorem actual_sorted_codes_strict : AdjacentStrict sortedCodes := by
  unfold sortedCodes
  rw [List.MergeSort.Internal.mergeSort_eq_mergeSortTR₂]
  run_tac
    Lean.Elab.Tactic.closeMainGoalUsing `p14_key_kernel_diagnostic fun expectedType _ => do
      let expectedType ← Lean.instantiateMVars expectedType
      if expectedType.hasMVar || expectedType.hasFVar then
        throwError "P1.4 kernel diagnostic requires the original closed target"
      let pf ← Lean.Meta.mkDecideProof expectedType
      let levelsInType := (Lean.collectLevelParams {} expectedType).params
      let lemmaLevels :=
        (← Lean.Elab.Term.getLevelNames).reverse.filter levelsInType.contains
      let lemmaName ← Lean.withOptions (Lean.Elab.async.set · false) do
        Lean.Meta.mkAuxLemma lemmaLevels expectedType pf
      return Lean.mkConst lemmaName (lemmaLevels.map .param)

theorem actual_typed_codes_nodup : typedCodes.Nodup := by
  exact (List.mergeSort_perm typedCodes (fun a b => decide (a ≤ b))).nodup_iff.mp
    (adjacentStrict_nodup sortedCodes actual_sorted_codes_strict)

/-- The uniqueness conclusion is for the ORIGINAL unsorted geometry keys. -/
theorem actual_typed_keys_nodup :
    (Data.P1HistoricalFifthSavedTableData.rows.toList.map rowKey).Nodup := by
  apply List.Nodup.of_map codeOfKey
  simpa only [List.map_map, Function.comp_def, typedCodes] using actual_typed_codes_nodup

end ImbalancedChen.P1HistoricalFifthTypedKeyPartition
