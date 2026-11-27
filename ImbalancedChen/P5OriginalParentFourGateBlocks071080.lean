import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks071080
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks071080

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks071080

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block071_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock071.rows.toList, parentFourGate row := by
  decide +kernel

theorem block071_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock071.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block071_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block071_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block071_parent_four_gate row hrow) c

theorem block072_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock072.rows.toList, parentFourGate row := by
  decide +kernel

theorem block072_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock072.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block072_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block072_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block072_parent_four_gate row hrow) c

theorem block073_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock073.rows.toList, parentFourGate row := by
  decide +kernel

theorem block073_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock073.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block073_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block073_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block073_parent_four_gate row hrow) c

theorem block074_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock074.rows.toList, parentFourGate row := by
  decide +kernel

theorem block074_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock074.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block074_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block074_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block074_parent_four_gate row hrow) c

theorem block075_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock075.rows.toList, parentFourGate row := by
  decide +kernel

theorem block075_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock075.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block075_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block075_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block075_parent_four_gate row hrow) c

theorem block076_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock076.rows.toList, parentFourGate row := by
  decide +kernel

theorem block076_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock076.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block076_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block076_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block076_parent_four_gate row hrow) c

theorem block077_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock077.rows.toList, parentFourGate row := by
  decide +kernel

theorem block077_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock077.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block077_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block077_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block077_parent_four_gate row hrow) c

theorem block078_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock078.rows.toList, parentFourGate row := by
  decide +kernel

theorem block078_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock078.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block078_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block078_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block078_parent_four_gate row hrow) c

theorem block079_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock079.rows.toList, parentFourGate row := by
  decide +kernel

theorem block079_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock079.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block079_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block079_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block079_parent_four_gate row hrow) c

theorem block080_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock080.rows.toList, parentFourGate row := by
  decide +kernel

theorem block080_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock080.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block080_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block080_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block080_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks071080
