import ImbalancedChen.OriginalPairedN48WholeHighArchive
import ImbalancedChen.OriginalPairedN48RequiredRowQ112Bridge

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
All original high-band method-zero rows, including rows outside the old
retained crop. Original Q112 weights/query/endpoints and Q80 max-clamped
floors share the SAME complete SourceRow. All finite proposals below and
in imported producer/log guards remain UNEXECUTED. No JSON bytes or
endpoint/numerator dump are claimed formally recovered or checked.
-/
namespace ImbalancedChen.OriginalPairedN48WholeHighQ112Evidence
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48MethodZeroQ112SwitchReduction
open OriginalN48Q112LocalProduct OriginalPairedN48WholeHighArchive
open OriginalPairedN48AllNativeQueryGeometry OriginalPairedN48Q112ClampedReceiver
open OriginalPairedN48RequiredRowQ112Bridge P2N48OriginalHighBlockWeights
open P5Z.U11Integral P5Z.U11Canonical

/-- The real archived row is carried beside every exact original field.
These are expression definitions, not materialized numerical endpoints. -/
structure WholeHighDirectedFields where
  row : SourceRow
  queryNumerator : ℤ
  weight : Token
  endpoint : DirectedMethodZeroRow

def wholeHighDirectedFields (r : SourceRow) : WholeHighDirectedFields :=
  ⟨r, rowOriginalNumerator r, originalRowZToken r, originalRowEndpoint r⟩

def wholeHighMethodZeroEvidence : List WholeHighDirectedFields :=
  wholeHighMethodZeroRows.map wholeHighDirectedFields

theorem whole_high_evidence_contains (r : SourceRow)
    (hr : r ∈ wholeHighMethodZeroRows) :
    wholeHighDirectedFields r ∈ wholeHighMethodZeroEvidence :=
  List.mem_map.mpr ⟨r, hr, rfl⟩

theorem full_high_archive_count : fullHighArchiveRows.length = 940800 := by
  simp only [fullHighArchiveRows, List.length_map, List.length_range]

/-- Literal count proposal, not a fresh numerical verification. -/
theorem whole_high_method_zero_count_proposal :
    wholeHighMethodZeroRows.length = 873004 := by
  decide +kernel

/-- Unlike the F crop, this exact check traverses the COMPLETE original
high-band row archive, selecting its own original method=0 fields. -/
def wholeHighOriginalFloorCheck : Bool :=
  fullHighArchiveRows.all (fun r =>
    if r.method = 0 then originalRequiredRowFloorCheck r else true)

theorem whole_high_floor_check_sound (hcheck : wholeHighOriginalFloorCheck = true) :
    ∀ r ∈ wholeHighMethodZeroRows, originalRequiredRowFloorCheck r = true := by
  intro r hr
  have hp := whole_high_method_zero_policy r hr
  have h := (List.all_eq_true.mp hcheck) r hp.1
  simpa only [if_pos hp.2] using h

/-- UNEXECUTED complete-high method-zero original integer floor proposal.
No actual row, query, arithmetic result or kernel acceptance is reported. -/
theorem whole_high_original_floor_proposal : wholeHighOriginalFloorCheck = true := by
  decide +kernel

theorem whole_high_same_parent_directions (r : SourceRow)
    (hr : r ∈ wholeHighMethodZeroRows) :
    ((originalRowEndpoint r).switchBaselineLo : ℝ) / (replayP : ℝ) ≤
        anchorK * omegaCap * parentUnweightedMass (fullParent r) ∧
    anchorK * uniformOmegaUpper (rowOriginalQueryToken r) * parentUnweightedMass (fullParent r) ≤
      ((originalRowEndpoint r).omegaCostHi : ℝ) / (replayP : ℝ) := by
  have hd := full_high_row_decoded r (whole_high_method_zero_policy r hr).1
  exact all_high_row_same_parent_directions r hd.1 ⟨hd.2.1, hd.2.2.1⟩

/-- The data premise is ONLY the row's literal finite integer comparison;
true Z, actual raw query and producer-field identities are independently
supplied by frozen source proofs/proposals, not by a desired cost premise. -/
theorem whole_high_original_cost_of_check (r : SourceRow)
    (hr : r ∈ wholeHighMethodZeroRows)
    (hcheck : originalRequiredRowFloorCheck r = true) :
    anchorK * parentSwitchedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  have hd := whole_high_same_parent_directions r hr
  exact q112_original_max_floor_sound r (originalRowEndpoint r)
    (uniformOmegaUpper (rowOriginalQueryToken r)) hd.1 hd.2
    (fun v hv => all_physical_parent_query_upper_proposal r hv) hcheck

theorem whole_high_original_cost_proposal (r : SourceRow)
    (hr : r ∈ wholeHighMethodZeroRows) :
    anchorK * parentSwitchedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) :=
  whole_high_original_cost_of_check r hr
    (whole_high_floor_check_sound whole_high_original_floor_proposal r hr)

/-- Key-based independent port for the real functional's highKeys sum.
The original saved method/floor remain literal source fields. Ordinary
methods are NOT assigned an omega floor bound by this theorem. -/
theorem archiveRowForKey_original_cost_proposal (x y z w : Fin 48)
    (hwz : w ≤ z) (hzy : z ≤ y)
    (hm : (archiveRowForKey x y z w).method = 0) :
    anchorK * parentSwitchedMass (fullParent (archiveRowForKey x y z w)) ≤
      savedParent (archiveRowForKey x y z w)
        (parentUnweightedMass (fullParent (archiveRowForKey x y z w))) := by
  apply whole_high_original_cost_proposal
  apply List.mem_filter.mpr
  exact ⟨archiveRowForKey_mem_full x y z w hwz hzy, by simpa only [decide_eq_true_eq] using hm⟩
end ImbalancedChen.OriginalPairedN48WholeHighQ112Evidence
