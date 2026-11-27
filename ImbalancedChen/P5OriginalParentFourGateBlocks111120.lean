import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks111120
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks111120

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks111120

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block111_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock111.rows.toList, parentFourGate row := by
  decide +kernel

theorem block111_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock111.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block111_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block111_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block111_parent_four_gate row hrow) c

theorem block112_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock112.rows.toList, parentFourGate row := by
  decide +kernel

theorem block112_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock112.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block112_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block112_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block112_parent_four_gate row hrow) c

theorem block113_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock113.rows.toList, parentFourGate row := by
  decide +kernel

theorem block113_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock113.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block113_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block113_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block113_parent_four_gate row hrow) c

theorem block114_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock114.rows.toList, parentFourGate row := by
  decide +kernel

theorem block114_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock114.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block114_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block114_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block114_parent_four_gate row hrow) c

theorem block115_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock115.rows.toList, parentFourGate row := by
  decide +kernel

theorem block115_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock115.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block115_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block115_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block115_parent_four_gate row hrow) c

theorem block116_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock116.rows.toList, parentFourGate row := by
  decide +kernel

theorem block116_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock116.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block116_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block116_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block116_parent_four_gate row hrow) c

theorem block117_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock117.rows.toList, parentFourGate row := by
  decide +kernel

theorem block117_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock117.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block117_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block117_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block117_parent_four_gate row hrow) c

theorem block118_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock118.rows.toList, parentFourGate row := by
  decide +kernel

theorem block118_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock118.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block118_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block118_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block118_parent_four_gate row hrow) c

theorem block119_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock119.rows.toList, parentFourGate row := by
  decide +kernel

theorem block119_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock119.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block119_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block119_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block119_parent_four_gate row hrow) c

theorem block120_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock120.rows.toList, parentFourGate row := by
  decide +kernel

theorem block120_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock120.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block120_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block120_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block120_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks111120
