import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks031040
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks031040

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks031040

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block031_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock031.rows.toList, parentFourGate row := by
  decide +kernel

theorem block031_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock031.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block031_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block031_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block031_parent_four_gate row hrow) c

theorem block032_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock032.rows.toList, parentFourGate row := by
  decide +kernel

theorem block032_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock032.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block032_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block032_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block032_parent_four_gate row hrow) c

theorem block033_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock033.rows.toList, parentFourGate row := by
  decide +kernel

theorem block033_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock033.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block033_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block033_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block033_parent_four_gate row hrow) c

theorem block034_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock034.rows.toList, parentFourGate row := by
  decide +kernel

theorem block034_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock034.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block034_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block034_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block034_parent_four_gate row hrow) c

theorem block035_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock035.rows.toList, parentFourGate row := by
  decide +kernel

theorem block035_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock035.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block035_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block035_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block035_parent_four_gate row hrow) c

theorem block036_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock036.rows.toList, parentFourGate row := by
  decide +kernel

theorem block036_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock036.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block036_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block036_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block036_parent_four_gate row hrow) c

theorem block037_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock037.rows.toList, parentFourGate row := by
  decide +kernel

theorem block037_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock037.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block037_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block037_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block037_parent_four_gate row hrow) c

theorem block038_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock038.rows.toList, parentFourGate row := by
  decide +kernel

theorem block038_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock038.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block038_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block038_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block038_parent_four_gate row hrow) c

theorem block039_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock039.rows.toList, parentFourGate row := by
  decide +kernel

theorem block039_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock039.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block039_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block039_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block039_parent_four_gate row hrow) c

theorem block040_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock040.rows.toList, parentFourGate row := by
  decide +kernel

theorem block040_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock040.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block040_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block040_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block040_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks031040
