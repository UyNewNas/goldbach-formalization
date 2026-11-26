import ImbalancedChen.P2OriginalCompactConcreteRun

/-!
SOURCEONLY / UNCOMPILED. The original stop test uses a source-computed
fixedUpper supplied by the concrete Q80 module. This file defines the actual
bounded computation, not an existence assertion for K.Run or an event file.
The two-million-step term is NEVER evaluated during source authoring.
-/
namespace ImbalancedChen.P2OriginalCompactConcreteLoopSourceOnly

open MeasureTheory
open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P2OriginalEfficientPriorityHeapSourceOnly
open P2OriginalCompactConcreteRunSourceOnly

/-- Original full-run arguments, distinct from the manuscript's selected K. -/
def maxSplits : ℕ := 2000000
def target : ℚ := 6809 / 1000
abbrev fixedUpper := P2OriginalCompactQ80EncloserSourceOnly.fixedUpper

def keepRunning (st : DriverState) : Prop :=
  st.splits < maxSplits ∧ target ≤ fixedUpper + (st.totalUpper : ℚ) / 2^80

instance (st : DriverState) : Decidable (keepRunning st) := inferInstanceAs
  (Decidable (st.splits < maxSplits ∧ target ≤ fixedUpper + (st.totalUpper : ℚ) / 2^80))

inductive StopReason where
  | budget
  | belowTarget
  deriving DecidableEq, Repr

inductive Result where
  | stopped (reason : StopReason) (state : DriverState)
  | failed (reason : DriverFailure) (state : DriverState)

def Result.state : Result → DriverState
  | .stopped _ st => st
  | .failed _ st => st

/-- The strict crossing is tested only after negating the original >= gate.
At the budget boundary the source's first while-condition already stops. -/
def stopResult (st : DriverState) : Result :=
  .stopped (if st.splits < maxSplits then .belowTarget else .budget) st

/-- Every successful iteration performs exactly one original split. Fuel is
an implementation termination bound, not a changed early-stop criterion. -/
def runFuel : ℕ → DriverState → Result :=
  Nat.rec (motive := fun _ => DriverState → Result)
    (fun st =>
      if keepRunning st then .failed .exhaustedFuel st else stopResult st)
    (fun _ previous st =>
      if keepRunning st then
        match driverStep st with
        | .error reason => .failed reason st
        | .ok next => previous next
      else stopResult st)

/-- Concrete original computation. No run witness or per-leaf data argument. -/
def originalRun : Result := runFuel maxSplits initialDriverState

theorem runFuel_ledger (fuel : ℕ) (st : DriverState) (hi : LedgerInvariant st) :
    LedgerInvariant (runFuel fuel st).state := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : driverStep st with
        | error reason => simpa [runFuel,hg,hs,Result.state] using hi
        | ok next =>
            simpa [runFuel,hg,hs] using ih next (driverStep_ledger st next hs hi)
      · simpa [runFuel,hg,stopResult,Result.state] using hi

theorem runFuel_heap (fuel : ℕ) (st : DriverState) (hi : AddressHeapInvariant st) :
    AddressHeapInvariant (runFuel fuel st).state := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : driverStep st with
        | error reason => simpa [runFuel,hg,hs,Result.state] using hi
        | ok next =>
            simpa [runFuel,hg,hs] using ih next (driverStep_heap st next hs hi)
      · simpa [runFuel,hg,stopResult,Result.state] using hi

theorem runFuel_serial (fuel : ℕ) (st : DriverState)
    (hi : SerialDiscipline (contents st.queue) st.serial) :
    SerialDiscipline (contents (runFuel fuel st).state.queue) (runFuel fuel st).state.serial := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : driverStep st with
        | error reason => simpa [runFuel,hg,hs,Result.state] using hi
        | ok next =>
            simpa [runFuel,hg,hs] using ih next (driverStep_serial st next hs hi)
      · simpa [runFuel,hg,stopResult,Result.state] using hi

theorem originalRun_serial : SerialDiscipline (contents originalRun.state.queue) originalRun.state.serial :=
  runFuel_serial _ _ initial_serial
theorem runFuel_leaf_count (fuel : ℕ) (st : DriverState)
    (hi : (entries st.forest).length = 21 + st.splits) :
    (entries (runFuel fuel st).state.forest).length = 21 + (runFuel fuel st).state.splits := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : driverStep st with
        | error reason => simpa [runFuel,hg,hs,Result.state] using hi
        | ok next =>
            obtain ⟨p,href,hcount,_⟩ := driverStep_source st next hs
            have hn := driverStep_leaf_count st next hs
            have hi' : (entries next.forest).length = 21 + next.splits := by omega
            simpa [runFuel,hg,hs] using ih next hi'
      · simpa [runFuel,hg,stopResult,Result.state] using hi

theorem originalRun_ledger : LedgerInvariant originalRun.state :=
  runFuel_ledger _ _ initial_ledger

theorem originalRun_heap : AddressHeapInvariant originalRun.state :=
  runFuel_heap _ _ initial_heap

theorem originalRun_leaf_count :
    (entries originalRun.state.forest).length = 21 + originalRun.state.splits := by
  apply runFuel_leaf_count
  change (entries (seedForest originalEnclose initialSeeds 0).1).length = 21 + 0
  rw [seedForest_entries_length,initialSeeds_eq_records,records_length]

/-- Exact ordered charges include EVERY leaf. No positive-error filter. -/
def orderedUpperCharges : List ℤ :=
  (entries originalRun.state.forest).map fun p => p.bounds.upper

def orderedLowerCharges : List ℤ :=
  (entries originalRun.state.forest).map fun p => p.bounds.lower

theorem orderedUpperCharges_sum : orderedUpperCharges.sum = originalRun.state.totalUpper :=
  originalRun_ledger.2.symm

theorem orderedLowerCharges_sum : orderedLowerCharges.sum = originalRun.state.totalLower :=
  originalRun_ledger.1.symm

theorem orderedCharges_length :
    orderedUpperCharges.length = 21 + originalRun.state.splits ∧
      orderedLowerCharges.length = 21 + originalRun.state.splits := by
  simp only [orderedUpperCharges,orderedLowerCharges,List.length_map,originalRun_leaf_count,and_self]

/-- The original source integral, not a later independent partition or kernel. -/
theorem originalRun_source_integral :
    OriginalThirdCompactPartitionSourceOnly.originalCompactThirdCorrection =
      ((entries originalRun.state.forest).map (fun p =>
        ∫ t in rootCell p.cell, OriginalThirdCompactPartitionSourceOnly.compactKernel t)).sum :=
  complete_integral_identity originalRun.state.forest

def historicalUpper : ℤ := 144590669409566793572719

/-- The original endpoint predicate, shared before inserting a closed run. -/
def historicalEndpointCheckFor (result : Result) : Bool :=
  match result with
  | .stopped .budget st =>
      decide (st.splits = maxSplits ∧ st.totalUpper = historicalUpper ∧
        Batteries.PairingHeap.size st.queue = 1852040 ∧ st.assertionsPassed = true)
  | _ => false

/-- The entire decisive finite claim. `true` requires the actual original
stop/budget computation to finish without failure at 2M, with the historical
upper sum and heap occupancy. No cached result is imported from JSON. -/
abbrev historicalEndpointCheck : Bool :=
  historicalEndpointCheckFor originalRun

private theorem historical_check_fields_result (result : Result)
    (hc : historicalEndpointCheckFor result = true) :
    result.state.splits = maxSplits ∧
    result.state.totalUpper = historicalUpper ∧
    Batteries.PairingHeap.size result.state.queue = 1852040 ∧
    result.state.assertionsPassed = true := by
  unfold historicalEndpointCheckFor at hc
  cases result with
  | failed reason st => simp at hc
  | stopped reason st =>
      cases reason with
      | belowTarget => simp at hc
      | budget => exact of_decide_eq_true hc

/-- Logical extraction only; the separate candidate file supplies the closed
finite proof term, left UNEVALUATED for user-owned compilation. -/
theorem historical_check_fields (hc : historicalEndpointCheck = true) :
    originalRun.state.splits = maxSplits ∧
    originalRun.state.totalUpper = historicalUpper ∧
    Batteries.PairingHeap.size originalRun.state.queue = 1852040 ∧
    originalRun.state.assertionsPassed = true := by
  exact historical_check_fields_result originalRun hc

theorem historical_ordered_charge_fields (hc : historicalEndpointCheck = true) :
    orderedUpperCharges.sum = historicalUpper ∧
    orderedUpperCharges.length = 2000021 := by
  have hf := historical_check_fields hc
  refine ⟨orderedUpperCharges_sum.trans hf.2.1,?_⟩
  rw [orderedCharges_length.1,hf.1]
  rfl


open P4AOriginalClosedTreeStructuralAggregationSourceOnly in
private theorem forest_upper_charges_length (forest : OriginalForest initialSeeds) :
    ((entries forest).map (fun p => p.bounds.upper)).length =
      splitCount (completeTree forest) + 1 := by
  have hlen := closedLeaves_length (completeTree forest)
    OriginalThirdCompactPartitionSourceOnly.compactRegion
  rw [completeTree_closedLeaves,List.length_map] at hlen
  simpa only [List.length_map] using hlen

/-- Shape-preserving attachment at the concrete complete original forest.
This includes zero-error leaves that never enter the active heap. -/
noncomputable abbrev originalChargeTree : P4AOriginalClosedTreeStructuralAggregationSourceOnly.ChargedCutTree :=
  (P4AClosedCutTreePositionalChargeBindingSourceOnly.attachCharges
    (completeTree originalRun.state.forest) orderedUpperCharges
      (forest_upper_charges_length originalRun.state.forest)).val

open P4AOriginalClosedTreeStructuralAggregationSourceOnly
  P4AClosedCutTreePositionalChargeBindingSourceOnly in
private noncomputable abbrev attachedChargeValue
    (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree) (charges : List ℤ)
    (hsize : charges.length = splitCount tree + 1) : ChargedCutTree :=
  (attachCharges tree charges hsize).val

open P4AOriginalClosedTreeStructuralAggregationSourceOnly
  P4AClosedCutTreePositionalChargeBindingSourceOnly in
/-- Establish both projections before inserting the closed run or charge list. -/
private theorem attached_charge_fields :
    (fun (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree) (charges : List ℤ)
      (hsize : charges.length = splitCount tree + 1) =>
      (totalCharge (attachedChargeValue tree charges hsize),
        eraseCharges (attachedChargeValue tree charges hsize))) =
    (fun (tree : OriginalThirdCompactPartitionSourceOnly.ClosedCutTree) (charges : List ℤ)
      (_ : charges.length = splitCount tree + 1) =>
      (charges.sum,tree)) := by
  funext tree charges hsize
  apply Prod.ext
  · exact (totalCharge_eq_leafCharges_sum
      (attachCharges tree charges hsize).val).trans
        (congrArg (fun qs : List ℤ => qs.sum)
          (attachCharges_list tree charges hsize))
  · exact attachCharges_erase tree charges hsize

theorem originalChargeTree_total :
    P4AOriginalClosedTreeStructuralAggregationSourceOnly.totalCharge originalChargeTree =
      originalRun.state.totalUpper := by
  have h := congrFun (congrFun (congrFun attached_charge_fields
    (completeTree originalRun.state.forest)) orderedUpperCharges)
      (forest_upper_charges_length originalRun.state.forest)
  exact (congrArg Prod.fst h).trans orderedUpperCharges_sum

theorem originalChargeTree_erase :
    P4AOriginalClosedTreeStructuralAggregationSourceOnly.eraseCharges originalChargeTree =
      completeTree originalRun.state.forest := by
  have h := congrFun (congrFun (congrFun attached_charge_fields
    (completeTree originalRun.state.forest)) orderedUpperCharges)
      (forest_upper_charges_length originalRun.state.forest)
  exact congrArg Prod.snd h

/-- The complete computation proves active-serial uniqueness, including
multiplicity. Python's later cell/lo/hi tuple fields can never break a tie. -/
theorem runFuel_serial_nodup (fuel : ℕ) (st : DriverState)
    (hb : SerialDiscipline (contents st.queue) st.serial)
    (hi : SerialNodup (contents st.queue)) :
    SerialNodup (contents (runFuel fuel st).state.queue) := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;> simpa [runFuel,hg,stopResult,Result.state] using hi
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : driverStep st with
        | error reason => simpa [runFuel,hg,hs,Result.state] using hi
        | ok next =>
            simpa [runFuel,hg,hs] using ih next
              (driverStep_serial st next hs hb) (driverStep_serial_nodup st next hs hb hi)
      · simpa [runFuel,hg,stopResult,Result.state] using hi

theorem originalRun_serial_nodup : SerialNodup (contents originalRun.state.queue) :=
  runFuel_serial_nodup _ _ initial_serial initial_serial_nodup
end ImbalancedChen.P2OriginalCompactConcreteLoopSourceOnly



