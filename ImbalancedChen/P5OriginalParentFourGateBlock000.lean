import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlock000
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlock000

/-! Original block000 parent gate and all64-child input facts.
Only the new parent gate is checked here. Existing original grid and lower-key
proofs are reused without another normal/kernel execution. -/
set_option autoImplicit false
namespace ImbalancedChen.P5OriginalParentFourGateBlock000

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block000_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock000.rows.toList, parentFourGate row := by
  decide +kernel

/-- Every actual row in the original block, and every one of its64 children.
No original d/A/B/floor/vertex input is assumed or numerically enumerated. -/
theorem block000_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock000.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block000_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block000_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block000_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlock000
