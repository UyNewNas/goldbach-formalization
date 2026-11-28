import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks141142
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks141142

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks141142

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block141_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock141.rows.toList, parentFourGate row := by
  decide +kernel

theorem block141_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock141.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block141_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block141_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block141_parent_four_gate row hrow) c

theorem block142_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock142.rows.toList, parentFourGate row := by
  decide +kernel

theorem block142_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock142.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block142_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block142_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block142_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks141142
