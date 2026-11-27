import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks081090
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks081090

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks081090

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block081_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock081.rows.toList, parentFourGate row := by
  decide +kernel

theorem block081_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock081.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block081_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block081_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block081_parent_four_gate row hrow) c

theorem block082_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock082.rows.toList, parentFourGate row := by
  decide +kernel

theorem block082_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock082.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block082_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block082_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block082_parent_four_gate row hrow) c

theorem block083_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock083.rows.toList, parentFourGate row := by
  decide +kernel

theorem block083_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock083.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block083_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block083_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block083_parent_four_gate row hrow) c

theorem block084_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock084.rows.toList, parentFourGate row := by
  decide +kernel

theorem block084_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock084.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block084_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block084_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block084_parent_four_gate row hrow) c

theorem block085_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock085.rows.toList, parentFourGate row := by
  decide +kernel

theorem block085_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock085.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block085_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block085_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block085_parent_four_gate row hrow) c

theorem block086_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock086.rows.toList, parentFourGate row := by
  decide +kernel

theorem block086_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock086.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block086_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block086_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block086_parent_four_gate row hrow) c

theorem block087_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock087.rows.toList, parentFourGate row := by
  decide +kernel

theorem block087_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock087.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block087_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block087_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block087_parent_four_gate row hrow) c

theorem block088_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock088.rows.toList, parentFourGate row := by
  decide +kernel

theorem block088_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock088.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block088_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block088_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block088_parent_four_gate row hrow) c

theorem block089_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock089.rows.toList, parentFourGate row := by
  decide +kernel

theorem block089_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock089.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block089_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block089_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block089_parent_four_gate row hrow) c

theorem block090_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock090.rows.toList, parentFourGate row := by
  decide +kernel

theorem block090_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock090.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block090_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block090_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block090_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks081090
