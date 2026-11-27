import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks061070
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks061070

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks061070

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block061_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock061.rows.toList, parentFourGate row := by
  decide +kernel

theorem block061_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock061.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block061_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block061_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block061_parent_four_gate row hrow) c

theorem block062_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock062.rows.toList, parentFourGate row := by
  decide +kernel

theorem block062_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock062.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block062_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block062_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block062_parent_four_gate row hrow) c

theorem block063_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock063.rows.toList, parentFourGate row := by
  decide +kernel

theorem block063_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock063.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block063_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block063_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block063_parent_four_gate row hrow) c

theorem block064_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock064.rows.toList, parentFourGate row := by
  decide +kernel

theorem block064_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock064.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block064_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block064_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block064_parent_four_gate row hrow) c

theorem block065_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock065.rows.toList, parentFourGate row := by
  decide +kernel

theorem block065_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock065.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block065_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block065_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block065_parent_four_gate row hrow) c

theorem block066_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock066.rows.toList, parentFourGate row := by
  decide +kernel

theorem block066_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock066.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block066_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block066_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block066_parent_four_gate row hrow) c

theorem block067_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock067.rows.toList, parentFourGate row := by
  decide +kernel

theorem block067_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock067.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block067_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block067_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block067_parent_four_gate row hrow) c

theorem block068_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock068.rows.toList, parentFourGate row := by
  decide +kernel

theorem block068_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock068.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block068_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block068_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block068_parent_four_gate row hrow) c

theorem block069_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock069.rows.toList, parentFourGate row := by
  decide +kernel

theorem block069_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock069.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block069_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block069_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block069_parent_four_gate row hrow) c

theorem block070_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock070.rows.toList, parentFourGate row := by
  decide +kernel

theorem block070_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock070.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block070_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block070_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block070_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks061070
