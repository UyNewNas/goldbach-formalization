import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks121130
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks121130

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks121130

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block121_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock121.rows.toList, parentFourGate row := by
  decide +kernel

theorem block121_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock121.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block121_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block121_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block121_parent_four_gate row hrow) c

theorem block122_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock122.rows.toList, parentFourGate row := by
  decide +kernel

theorem block122_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock122.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block122_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block122_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block122_parent_four_gate row hrow) c

theorem block123_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock123.rows.toList, parentFourGate row := by
  decide +kernel

theorem block123_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock123.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block123_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block123_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block123_parent_four_gate row hrow) c

theorem block124_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock124.rows.toList, parentFourGate row := by
  decide +kernel

theorem block124_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock124.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block124_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block124_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block124_parent_four_gate row hrow) c

theorem block125_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock125.rows.toList, parentFourGate row := by
  decide +kernel

theorem block125_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock125.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block125_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block125_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block125_parent_four_gate row hrow) c

theorem block126_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock126.rows.toList, parentFourGate row := by
  decide +kernel

theorem block126_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock126.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block126_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block126_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block126_parent_four_gate row hrow) c

theorem block127_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock127.rows.toList, parentFourGate row := by
  decide +kernel

theorem block127_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock127.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block127_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block127_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block127_parent_four_gate row hrow) c

theorem block128_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock128.rows.toList, parentFourGate row := by
  decide +kernel

theorem block128_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock128.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block128_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block128_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block128_parent_four_gate row hrow) c

theorem block129_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock129.rows.toList, parentFourGate row := by
  decide +kernel

theorem block129_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock129.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block129_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block129_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block129_parent_four_gate row hrow) c

theorem block130_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock130.rows.toList, parentFourGate row := by
  decide +kernel

theorem block130_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock130.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block130_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block130_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block130_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks121130
