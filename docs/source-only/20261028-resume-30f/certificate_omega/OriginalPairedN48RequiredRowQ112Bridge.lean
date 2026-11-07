import ImbalancedChen.OriginalPairedN48Q112ClampedReceiver
import ImbalancedChen.P2N48OriginalHighBlockWeights

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual required retained-row family, original same-parent J112 endpoints,
and literal Q80 floor comparison.  The independent all-pattern true-Z
supplier and the independent original global-array query are consumed.
No hZ, hOldCost, hCertificate, or desired query bound is assumed.

The closed all-row decision term is an UNEXECUTED SOURCE PROPOSAL.
The finite numerator table below is a definition, not a recovered dump or
a list of numerals certified by running the original evaluator.
-/

namespace ImbalancedChen.OriginalPairedN48RequiredRowQ112Bridge

noncomputable section
open Set
open scoped BigOperators
open LiLiuPrereqBuchstab
open OriginalN48Q112LocalProduct
open OriginalPairedN48RawQueryFamily
open OriginalPairedN48AllNativeQueryGeometry
open OriginalPairedN48Q112ClampedReceiver
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48MethodZeroQ112SwitchReduction
open P2N48OriginalHighBlockWeights
open P5Z.U11Integral P5Z.U11Canonical

def originalRowEndpoint (r : SourceRow) : DirectedMethodZeroRow :=
  computedDirectedEndpoint (rowOriginalQueryToken r) (originalRowZToken r)

def originalRequiredRowFloorCheck (r : SourceRow) : Bool :=
  originalRowMaxFloorCheck r (originalRowEndpoint r)

/-- Every row carries its original ordinal, term, indices, method, floor
and exact original query expression, not an arbitrary per-key number. -/
def requiredOriginalNumeratorTable : List (SourceRow × ℤ) :=
  actualRetainedRows.toList.map (fun r => (r, rowOriginalNumerator r))

theorem required_numerator_table_contains (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    (r, rowOriginalNumerator r) ∈ requiredOriginalNumeratorTable :=
  List.mem_map.mpr ⟨r, Finset.mem_toList.mpr hr, rfl⟩

/-- Complete original same-parent interval directions for every high-band
ordered key, with every one of the four actual tie moment formulas. -/
theorem all_high_row_same_parent_directions (r : SourceRow) (ht : r.term.val = 1)
    (hchron : r.iw ≤ r.iz ∧ r.iz ≤ r.iy) :
    ((originalRowEndpoint r).switchBaselineLo : ℝ) / (replayP : ℝ) ≤
        anchorK * omegaCap * parentUnweightedMass (fullParent r) ∧
    anchorK * uniformOmegaUpper (rowOriginalQueryToken r) * parentUnweightedMass (fullParent r) ≤
      ((originalRowEndpoint r).omegaCostHi : ℝ) / (replayP : ℝ) := by
  exact computed_endpoints_uniform_directions (rowOriginalQueryToken r) (originalRowZToken r)
    (original_high_row_token_contains_trueMass r ht hchron) le_rfl

/-- This scope is the ACTUAL required retained finite row family from the
frozen source archive; no caller supplies a desired real mass enclosure. -/
theorem actual_required_same_parent_directions (r : SourceRow) (hr : r ∈ actualRetainedRows) :
    ((originalRowEndpoint r).switchBaselineLo : ℝ) / (replayP : ℝ) ≤
        anchorK * omegaCap * parentUnweightedMass (fullParent r) ∧
    anchorK * uniformOmegaUpper (rowOriginalQueryToken r) * parentUnweightedMass (fullParent r) ≤
      ((originalRowEndpoint r).omegaCostHi : ℝ) / (replayP : ℝ) := by
  exact computed_endpoints_uniform_directions (rowOriginalQueryToken r) (originalRowZToken r)
    (original_retained_row_token_contains_trueMass r hr) le_rfl

/-- Every actual required row receives a real original-domain old-cost
bound from its own finite max-clamped comparison.  This includes floor0. -/
theorem actual_required_row_old_cost_of_check (r : SourceRow) (hr : r ∈ actualRetainedRows)
    (hcheck : originalRequiredRowFloorCheck r = true) :
    anchorK * parentSwitchedMass (fullParent r) ≤
      savedParent r (parentUnweightedMass (fullParent r)) := by
  have hd := actual_required_same_parent_directions r hr
  exact q112_original_max_floor_sound r (originalRowEndpoint r)
    (uniformOmegaUpper (rowOriginalQueryToken r)) hd.1 hd.2
    (fun v hv => all_physical_parent_query_upper_proposal r hv) hcheck

def allRequiredOriginalFloorCheck : Bool :=
  actualRetainedRows.toList.all originalRequiredRowFloorCheck

theorem all_required_original_floor_check_sound
    (hcheck : allRequiredOriginalFloorCheck = true) :
    ∀ r ∈ actualRetainedRows, originalRequiredRowFloorCheck r = true := by
  intro r hr
  exact (List.all_eq_true.mp hcheck) r (Finset.mem_toList.mpr hr)

/-- UNEXECUTED closed finite proposal on exactly the required actual row
list and original Q112/Q80 expressions.  No successful run is claimed. -/
theorem all_required_original_floor_proposal : allRequiredOriginalFloorCheck = true := by
  decide +kernel

/-- The all-required-family source proof pipeline, including true moments,
actual raw query, original endpoint directions and the max-floor check.
The referenced finite producer/log/floor terms have NOT been evaluated. -/
theorem actual_required_all_row_old_cost_proposal :
    ∀ r ∈ actualRetainedRows,
      anchorK * parentSwitchedMass (fullParent r) ≤
        savedParent r (parentUnweightedMass (fullParent r)) := by
  intro r hr
  exact actual_required_row_old_cost_of_check r hr
    (all_required_original_floor_check_sound all_required_original_floor_proposal r hr)

end
end ImbalancedChen.OriginalPairedN48RequiredRowQ112Bridge
