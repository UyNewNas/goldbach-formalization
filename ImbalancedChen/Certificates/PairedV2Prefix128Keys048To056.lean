import ImbalancedChen.Certificates.PairedV2Prefix128Data

/-! Adjacent actual-grid keys with left ordinal in [48,56). -/
namespace ImbalancedChen.Certificates.PairedV2.Prefix128

set_option maxHeartbeats 4000000 in
theorem rowKey_adjacent_048_056 (i : Fin 8) :
    rowKey (⟨48 + i.val, by have hi := i.isLt; omega⟩ : Fin 128) <
      rowKey (⟨48 + i.val + 1, by have hi := i.isLt; omega⟩ : Fin 128) := by
  fin_cases i <;>
    norm_num [rowKey, rowIndices, Fin.append, Fin.addCases,
      Prefix64.rowIndices, Prefix4.rowIndices,
      Batch4To64.rowIndices, Batch64To128.rowIndices]

end ImbalancedChen.Certificates.PairedV2.Prefix128
