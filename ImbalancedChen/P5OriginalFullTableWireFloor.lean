import ImbalancedChen.P5OriginalFullTableChildSourceFacts
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryRows
import ImbalancedChen.P1HistoricalFifthTypedArchiveRange

/-! Original Q80 child-floor soundness specialized to every original source row.
The actual selected-owner reserve remains explicit; no cross-parent gain,
stored parent maximum, archive byte authenticity or zero residual is claimed. -/
set_option autoImplicit false
namespace ImbalancedChen.P5OriginalFullTableWireFloor
noncomputable section
open Set MeasureTheory
open scoped BigOperators
open P1OriginalPrefixRowDecodeSoundness P5OldFifthExact64ChildTiling
open P5OriginalGenericWireFloorReceiver P5OriginalFullTableChildSourceFacts
open P1HistoricalFifthTypedBaseGeometry P1HistoricalFifthTypedArchiveRange
open P5ChildSelectedOwnerJensenReserve
open P5OldFifthFrozenUpperSurrogate P5NamedFifthPayloadSemantics
open P1FifthPositivePartActualOwner (literalPositiveRawOwnerIntegral)

/-- No per-child domain, vertex, Jensen or floor premise remains. -/
theorem original_saved_child_floor_le_actual_child
    (raw : FifthWireRow) (hrow : raw ∈ Data.P1HistoricalFifthSavedTableData.rows.toList)
    (c : ChildIndex) :
    (rowFloorQ raw c : ℝ) ≤
      ∫ t in childBox raw c, frozenUpperPositiveKernel (sourcePicks raw) raw t := by
  exact original_wire_floor_le_actual_child raw c
    (fun i => (rows_lower_key_bounds raw hrow i).1)
    (all_original_rows_child_source_facts raw hrow c)

/-- The complete64 sum uses the same actual selected-owner domains/reserve. -/
theorem original_saved_parent64_floor_minus_actual_reserve
    (raw : FifthWireRow) (hrow : raw ∈ Data.P1HistoricalFifthSavedTableData.rows.toList)
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J5 : Finset (P5ChildSelectedOwnerJensenReserve.Owner m)) :
    (∑ c : ChildIndex, (rowFloorQ raw c : ℝ)) -
        (∑ c : ChildIndex, childOwnerReserve raw c e chi m omega J5) ≤
      ∑ j ∈ P1OriginalCoarseFifthContinuation.selectedFifthCells e chi m omega J5,
        literalPositiveRawOwnerIntegral raw e chi m omega j := by
  exact original_parent64_wire_floor_sub_reserve raw (rows_grid_eq400 raw hrow)
    (fun i => (rows_lower_key_bounds raw hrow i).1)
    (all_original_rows_child_source_facts raw hrow) e chi m omega J5

end
end ImbalancedChen.P5OriginalFullTableWireFloor
