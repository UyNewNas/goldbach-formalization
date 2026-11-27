import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks021030
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks021030

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks021030

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block021_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock021.rows.toList, parentFourGate row := by
  decide +kernel

theorem block021_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock021.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block021_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block021_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block021_parent_four_gate row hrow) c

theorem block022_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock022.rows.toList, parentFourGate row := by
  decide +kernel

theorem block022_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock022.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block022_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block022_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block022_parent_four_gate row hrow) c

theorem block023_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock023.rows.toList, parentFourGate row := by
  decide +kernel

theorem block023_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock023.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block023_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block023_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block023_parent_four_gate row hrow) c

theorem block024_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock024.rows.toList, parentFourGate row := by
  decide +kernel

theorem block024_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock024.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block024_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block024_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block024_parent_four_gate row hrow) c

theorem block025_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock025.rows.toList, parentFourGate row := by
  decide +kernel

theorem block025_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock025.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block025_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block025_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block025_parent_four_gate row hrow) c

theorem block026_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock026.rows.toList, parentFourGate row := by
  decide +kernel

theorem block026_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock026.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block026_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block026_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block026_parent_four_gate row hrow) c

theorem block027_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock027.rows.toList, parentFourGate row := by
  decide +kernel

theorem block027_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock027.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block027_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block027_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block027_parent_four_gate row hrow) c

theorem block028_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock028.rows.toList, parentFourGate row := by
  decide +kernel

theorem block028_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock028.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block028_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block028_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block028_parent_four_gate row hrow) c

theorem block029_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock029.rows.toList, parentFourGate row := by
  decide +kernel

theorem block029_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock029.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block029_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block029_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block029_parent_four_gate row hrow) c

theorem block030_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock030.rows.toList, parentFourGate row := by
  decide +kernel

theorem block030_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock030.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block030_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block030_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block030_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks021030
