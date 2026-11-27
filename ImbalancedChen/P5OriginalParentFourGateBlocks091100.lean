import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks091100
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks091100

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks091100

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block091_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock091.rows.toList, parentFourGate row := by
  decide +kernel

theorem block091_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock091.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block091_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block091_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block091_parent_four_gate row hrow) c

theorem block092_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock092.rows.toList, parentFourGate row := by
  decide +kernel

theorem block092_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock092.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block092_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block092_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block092_parent_four_gate row hrow) c

theorem block093_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock093.rows.toList, parentFourGate row := by
  decide +kernel

theorem block093_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock093.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block093_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block093_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block093_parent_four_gate row hrow) c

theorem block094_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock094.rows.toList, parentFourGate row := by
  decide +kernel

theorem block094_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock094.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block094_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block094_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block094_parent_four_gate row hrow) c

theorem block095_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock095.rows.toList, parentFourGate row := by
  decide +kernel

theorem block095_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock095.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block095_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block095_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block095_parent_four_gate row hrow) c

theorem block096_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock096.rows.toList, parentFourGate row := by
  decide +kernel

theorem block096_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock096.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block096_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block096_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block096_parent_four_gate row hrow) c

theorem block097_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock097.rows.toList, parentFourGate row := by
  decide +kernel

theorem block097_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock097.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block097_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block097_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block097_parent_four_gate row hrow) c

theorem block098_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock098.rows.toList, parentFourGate row := by
  decide +kernel

theorem block098_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock098.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block098_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block098_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block098_parent_four_gate row hrow) c

theorem block099_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock099.rows.toList, parentFourGate row := by
  decide +kernel

theorem block099_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock099.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block099_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block099_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block099_parent_four_gate row hrow) c

theorem block100_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock100.rows.toList, parentFourGate row := by
  decide +kernel

theorem block100_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock100.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block100_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block100_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block100_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks091100
