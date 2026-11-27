import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks011020
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks011020

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks011020

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block011_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock011.rows.toList, parentFourGate row := by
  decide +kernel

theorem block011_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock011.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block011_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block011_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block011_parent_four_gate row hrow) c

theorem block012_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock012.rows.toList, parentFourGate row := by
  decide +kernel

theorem block012_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock012.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block012_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block012_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block012_parent_four_gate row hrow) c

theorem block013_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock013.rows.toList, parentFourGate row := by
  decide +kernel

theorem block013_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock013.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block013_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block013_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block013_parent_four_gate row hrow) c

theorem block014_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock014.rows.toList, parentFourGate row := by
  decide +kernel

theorem block014_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock014.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block014_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block014_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block014_parent_four_gate row hrow) c

theorem block015_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock015.rows.toList, parentFourGate row := by
  decide +kernel

theorem block015_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock015.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block015_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block015_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block015_parent_four_gate row hrow) c

theorem block016_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock016.rows.toList, parentFourGate row := by
  decide +kernel

theorem block016_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock016.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block016_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block016_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block016_parent_four_gate row hrow) c

theorem block017_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock017.rows.toList, parentFourGate row := by
  decide +kernel

theorem block017_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock017.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block017_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block017_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block017_parent_four_gate row hrow) c

theorem block018_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock018.rows.toList, parentFourGate row := by
  decide +kernel

theorem block018_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock018.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block018_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block018_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block018_parent_four_gate row hrow) c

theorem block019_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock019.rows.toList, parentFourGate row := by
  decide +kernel

theorem block019_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock019.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block019_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block019_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block019_parent_four_gate row hrow) c

theorem block020_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock020.rows.toList, parentFourGate row := by
  decide +kernel

theorem block020_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock020.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block020_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block020_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block020_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks011020
