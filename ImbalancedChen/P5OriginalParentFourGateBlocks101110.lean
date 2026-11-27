import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks101110
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks101110

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks101110

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block101_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock101.rows.toList, parentFourGate row := by
  decide +kernel

theorem block101_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock101.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block101_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block101_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block101_parent_four_gate row hrow) c

theorem block102_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock102.rows.toList, parentFourGate row := by
  decide +kernel

theorem block102_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock102.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block102_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block102_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block102_parent_four_gate row hrow) c

theorem block103_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock103.rows.toList, parentFourGate row := by
  decide +kernel

theorem block103_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock103.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block103_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block103_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block103_parent_four_gate row hrow) c

theorem block104_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock104.rows.toList, parentFourGate row := by
  decide +kernel

theorem block104_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock104.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block104_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block104_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block104_parent_four_gate row hrow) c

theorem block105_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock105.rows.toList, parentFourGate row := by
  decide +kernel

theorem block105_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock105.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block105_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block105_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block105_parent_four_gate row hrow) c

theorem block106_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock106.rows.toList, parentFourGate row := by
  decide +kernel

theorem block106_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock106.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block106_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block106_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block106_parent_four_gate row hrow) c

theorem block107_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock107.rows.toList, parentFourGate row := by
  decide +kernel

theorem block107_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock107.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block107_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block107_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block107_parent_four_gate row hrow) c

theorem block108_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock108.rows.toList, parentFourGate row := by
  decide +kernel

theorem block108_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock108.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block108_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block108_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block108_parent_four_gate row hrow) c

theorem block109_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock109.rows.toList, parentFourGate row := by
  decide +kernel

theorem block109_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock109.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block109_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block109_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block109_parent_four_gate row hrow) c

theorem block110_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock110.rows.toList, parentFourGate row := by
  decide +kernel

theorem block110_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock110.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block110_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block110_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block110_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks101110
