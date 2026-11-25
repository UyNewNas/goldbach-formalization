import ImbalancedChen.P1HistoricalFifthTypedKeyUniquenessCore

namespace ImbalancedChen.P1HistoricalFifthTypedKeyPartition
open P1OriginalPrefixRowDecodeSoundness P1FifthGrid400UnitBoxPartition

/-- This is a closed term about all292633 actual typed source positions.
It is neither a supplied checker flag nor an archived-byte identity.
No decision reduction, checker or compiler was invoked by the author. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 400000000 in
theorem actual_sorted_codes_strict : AdjacentStrict sortedCodes := by
  decide +kernel

theorem actual_typed_codes_nodup : typedCodes.Nodup := by
  exact (List.mergeSort_perm typedCodes (fun a b => decide (a ≤ b))).nodup_iff.mp
    (adjacentStrict_nodup sortedCodes actual_sorted_codes_strict)

/-- The uniqueness conclusion is for the ORIGINAL unsorted geometry keys. -/
theorem actual_typed_keys_nodup :
    (Data.P1HistoricalFifthSavedTableData.rows.toList.map rowKey).Nodup := by
  apply List.Nodup.of_map codeOfKey
  simpa only [List.map_map, Function.comp_def, typedCodes] using actual_typed_codes_nodup

end ImbalancedChen.P1HistoricalFifthTypedKeyPartition
