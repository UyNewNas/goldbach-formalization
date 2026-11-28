import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks131140
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks131140

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks131140

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block131_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock131.rows.toList, parentFourGate row := by
  decide +kernel

theorem block131_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock131.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block131_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block131_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block131_parent_four_gate row hrow) c

theorem block132_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock132.rows.toList, parentFourGate row := by
  decide +kernel

theorem block132_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock132.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block132_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block132_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block132_parent_four_gate row hrow) c

theorem block133_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock133.rows.toList, parentFourGate row := by
  decide +kernel

theorem block133_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock133.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block133_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block133_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block133_parent_four_gate row hrow) c

theorem block134_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock134.rows.toList, parentFourGate row := by
  decide +kernel

theorem block134_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock134.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block134_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block134_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block134_parent_four_gate row hrow) c

theorem block135_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock135.rows.toList, parentFourGate row := by
  decide +kernel

theorem block135_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock135.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block135_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block135_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block135_parent_four_gate row hrow) c

theorem block136_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock136.rows.toList, parentFourGate row := by
  decide +kernel

theorem block136_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock136.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block136_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block136_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block136_parent_four_gate row hrow) c

theorem block137_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock137.rows.toList, parentFourGate row := by
  decide +kernel

theorem block137_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock137.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block137_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block137_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block137_parent_four_gate row hrow) c

theorem block138_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock138.rows.toList, parentFourGate row := by
  decide +kernel

theorem block138_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock138.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block138_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block138_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block138_parent_four_gate row hrow) c

theorem block139_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock139.rows.toList, parentFourGate row := by
  decide +kernel

theorem block139_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock139.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block139_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block139_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block139_parent_four_gate row hrow) c

theorem block140_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock140.rows.toList, parentFourGate row := by
  decide +kernel

theorem block140_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock140.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block140_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block140_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block140_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks131140
