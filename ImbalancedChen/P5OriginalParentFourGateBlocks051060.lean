import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks051060
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks051060

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks051060

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block051_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock051.rows.toList, parentFourGate row := by
  decide +kernel

theorem block051_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock051.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block051_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block051_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block051_parent_four_gate row hrow) c

theorem block052_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock052.rows.toList, parentFourGate row := by
  decide +kernel

theorem block052_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock052.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block052_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block052_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block052_parent_four_gate row hrow) c

theorem block053_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock053.rows.toList, parentFourGate row := by
  decide +kernel

theorem block053_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock053.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block053_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block053_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block053_parent_four_gate row hrow) c

theorem block054_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock054.rows.toList, parentFourGate row := by
  decide +kernel

theorem block054_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock054.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block054_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block054_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block054_parent_four_gate row hrow) c

theorem block055_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock055.rows.toList, parentFourGate row := by
  decide +kernel

theorem block055_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock055.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block055_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block055_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block055_parent_four_gate row hrow) c

theorem block056_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock056.rows.toList, parentFourGate row := by
  decide +kernel

theorem block056_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock056.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block056_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block056_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block056_parent_four_gate row hrow) c

theorem block057_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock057.rows.toList, parentFourGate row := by
  decide +kernel

theorem block057_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock057.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block057_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block057_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block057_parent_four_gate row hrow) c

theorem block058_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock058.rows.toList, parentFourGate row := by
  decide +kernel

theorem block058_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock058.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block058_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block058_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block058_parent_four_gate row hrow) c

theorem block059_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock059.rows.toList, parentFourGate row := by
  decide +kernel

theorem block059_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock059.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block059_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block059_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block059_parent_four_gate row hrow) c

theorem block060_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock060.rows.toList, parentFourGate row := by
  decide +kernel

theorem block060_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock060.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block060_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block060_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block060_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks051060
