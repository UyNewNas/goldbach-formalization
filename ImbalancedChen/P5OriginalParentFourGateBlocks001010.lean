import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks001010
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks001010

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks001010

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block001_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock001.rows.toList, parentFourGate row := by
  decide +kernel

theorem block001_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock001.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block001_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block001_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block001_parent_four_gate row hrow) c

theorem block002_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock002.rows.toList, parentFourGate row := by
  decide +kernel

theorem block002_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock002.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block002_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block002_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block002_parent_four_gate row hrow) c

theorem block003_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock003.rows.toList, parentFourGate row := by
  decide +kernel

theorem block003_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock003.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block003_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block003_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block003_parent_four_gate row hrow) c

theorem block004_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock004.rows.toList, parentFourGate row := by
  decide +kernel

theorem block004_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock004.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block004_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block004_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block004_parent_four_gate row hrow) c

theorem block005_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock005.rows.toList, parentFourGate row := by
  decide +kernel

theorem block005_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock005.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block005_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block005_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block005_parent_four_gate row hrow) c

theorem block006_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock006.rows.toList, parentFourGate row := by
  decide +kernel

theorem block006_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock006.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block006_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block006_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block006_parent_four_gate row hrow) c

theorem block007_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock007.rows.toList, parentFourGate row := by
  decide +kernel

theorem block007_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock007.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block007_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block007_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block007_parent_four_gate row hrow) c

theorem block008_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock008.rows.toList, parentFourGate row := by
  decide +kernel

theorem block008_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock008.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block008_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block008_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block008_parent_four_gate row hrow) c

theorem block009_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock009.rows.toList, parentFourGate row := by
  decide +kernel

theorem block009_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock009.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block009_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block009_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block009_parent_four_gate row hrow) c

theorem block010_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock010.rows.toList, parentFourGate row := by
  decide +kernel

theorem block010_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock010.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block010_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block010_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block010_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks001010
