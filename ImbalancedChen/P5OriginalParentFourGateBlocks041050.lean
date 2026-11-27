import ImbalancedChen.P5OriginalParentFourGate
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks041050
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks041050

/-! New original parent-gate certificates only. Existing original grid/key
proofs and unchanged Data artifacts are reused. No child d/AB/floor enumeration. -/
set_option autoImplicit false
set_option Elab.async false
namespace ImbalancedChen.P5OriginalParentFourGateBlocks041050

open P1OriginalPrefixRowDecodeSoundness
open P5OriginalParentFourGate P5OriginalGenericWireFloorReceiver
open P5OldFifthExact64ChildTiling
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange

theorem block041_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock041.rows.toList, parentFourGate row := by
  decide +kernel

theorem block041_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock041.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block041_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block041_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block041_parent_four_gate row hrow) c

theorem block042_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock042.rows.toList, parentFourGate row := by
  decide +kernel

theorem block042_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock042.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block042_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block042_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block042_parent_four_gate row hrow) c

theorem block043_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock043.rows.toList, parentFourGate row := by
  decide +kernel

theorem block043_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock043.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block043_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block043_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block043_parent_four_gate row hrow) c

theorem block044_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock044.rows.toList, parentFourGate row := by
  decide +kernel

theorem block044_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock044.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block044_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block044_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block044_parent_four_gate row hrow) c

theorem block045_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock045.rows.toList, parentFourGate row := by
  decide +kernel

theorem block045_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock045.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block045_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block045_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block045_parent_four_gate row hrow) c

theorem block046_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock046.rows.toList, parentFourGate row := by
  decide +kernel

theorem block046_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock046.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block046_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block046_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block046_parent_four_gate row hrow) c

theorem block047_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock047.rows.toList, parentFourGate row := by
  decide +kernel

theorem block047_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock047.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block047_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block047_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block047_parent_four_gate row hrow) c

theorem block048_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock048.rows.toList, parentFourGate row := by
  decide +kernel

theorem block048_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock048.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block048_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block048_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block048_parent_four_gate row hrow) c

theorem block049_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock049.rows.toList, parentFourGate row := by
  decide +kernel

theorem block049_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock049.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block049_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block049_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block049_parent_four_gate row hrow) c

theorem block050_parent_four_gate :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock050.rows.toList, parentFourGate row := by
  decide +kernel

theorem block050_all_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock050.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  have hk := block050_lower_key_bounds row hrow
  have hg : row.grid = 400 := (block050_typed_valid row hrow).1
  have hp : ∀ i : Fin 5, 1 ≤ row.lo i := fun i => (hk i).1
  have hu : ∀ i : Fin 5, 96 * (row.lo i + 1) ≤ 19 * row.grid := by
    intro i
    rw [hg]
    have hb := (hk i).2
    omega
  exact all_child_source_facts row hg hp hu (block050_parent_four_gate row hrow) c

end ImbalancedChen.P5OriginalParentFourGateBlocks041050
