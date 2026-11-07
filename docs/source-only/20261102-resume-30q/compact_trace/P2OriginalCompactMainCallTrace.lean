import ImbalancedChen.P2OriginalCompactConcreteLoop
import ImbalancedChen.P2OriginalCompactQ80CompleteSoundness

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNCHECKED / NO FINITE RUN EVALUATED.

The missing chronological enclosure-call history for the original main loop.
This instruments the concrete heap/address computation, rather than accepting
a run witness. Erasure is the existing L driverStep/runFuel, including every
failure and stop branch. Calls include retired parents' earlier evaluations,
zero-error children and empty children. They are not the final leaf list.

One event means one Python-level call to enclosure, not every recomputation
of a pure Lean subexpression. The Python arithmetic-primitive trace inside
enclosure is a separate obligation. In particular the existing partial
sourceAssertions inventory is not renamed to a full primitive certificate.
-/
namespace ImbalancedChen.P2OriginalCompactMainCallTraceSourceOnly

open P4AOriginalInitialSeedInventorySourceOnly
open P2OriginalAdaptiveSourceSplitSourceOnly
open P2OriginalPrioritySerialQueueSourceOnly
open P2OriginalPriorityForestLedgerSourceOnly
open P2OriginalEfficientPriorityHeapSourceOnly
open P2OriginalCompactConcreteRunSourceOnly
open P2OriginalCompactConcreteLoopSourceOnly
open P2OriginalCompactQ80LeafSourceOnly
open P2OriginalCompactQ80ReachabilitySourceOnly

structure StepTrace where
  outcome : Except DriverFailure DriverState
  calls : List SeedCell

/-- Literal driverStep with two chronological semantic-call events added.
The successful branch retains precisely the same forest, pairing heap,
serial, split count, integer totals and partial assertion accumulator. -/
def tracedStep (st : DriverState) : StepTrace :=
  match Batteries.PairingHeap.deleteMin st.queue with
  | none => ⟨.error .emptyHeap,[]⟩
  | some (job,rest) =>
      match splitForestAt st.serial st.forest job.seed job.path with
      | none => ⟨.error .badAddressOrMidpoint,[]⟩
      | some (parent,forest') =>
          if SameEntry parent job.entry then
            let childEntries := children originalEnclose st.serial parent.cell
            let childJobs := spawnJobs st.serial parent job.seed job.path
            ⟨.ok ⟨forest',putJobs rest childJobs,
              afterChildren originalEnclose st.serial parent.cell,st.splits + 1,
              st.totalLower - job.entry.bounds.lower + lowerSum childEntries,
              st.totalUpper - job.entry.bounds.upper + upperSum childEntries,
              st.assertionsPassed && sourceCheck (sourceLeft parent.cell) &&
                sourceCheck (sourceRight parent.cell)⟩,
              [sourceLeft parent.cell,sourceRight parent.cell]⟩
          else ⟨.error .cachedParentMismatch,[]⟩

/-- This is an equation about every state, not an assumed successful run or
an assumed primitive guard. The positional forest refinement is inherited
from L's actual successful address update. -/
theorem tracedStep_spec (st : DriverState) :
    (tracedStep st).outcome = driverStep st ∧
      match (tracedStep st).outcome with
      | .error _ => (tracedStep st).calls = []
      | .ok next => ∃ parent,
          ForestRefines originalEnclose st.serial parent st.forest next.forest ∧
          next.splits = st.splits + 1 ∧
          (tracedStep st).calls = [sourceLeft parent.cell,sourceRight parent.cell] ∧
          next.assertionsPassed =
            st.assertionsPassed && (tracedStep st).calls.all sourceCheck := by
  cases hp : Batteries.PairingHeap.deleteMin st.queue with
  | none => simp [tracedStep,driverStep,hp]
  | some result =>
      rcases result with ⟨job,rest⟩
      cases hs : splitForestAt st.serial st.forest job.seed job.path with
      | none => simp [tracedStep,driverStep,hp,hs]
      | some result =>
          rcases result with ⟨parent,forest'⟩
          by_cases he : SameEntry parent job.entry
          · simp only [tracedStep,driverStep,hp,hs,if_pos he]
            refine ⟨rfl,parent,splitForestAt_refines _ _ _ _ _ _ hs,rfl,rfl,?_⟩
            simp [Bool.and_assoc]
          · simp [tracedStep,driverStep,hp,hs,he]

theorem tracedStep_outcome (st : DriverState) :
    (tracedStep st).outcome = driverStep st := (tracedStep_spec st).1

theorem tracedStep_error_calls (st : DriverState) (reason : DriverFailure)
    (h : (tracedStep st).outcome = .error reason) : (tracedStep st).calls = [] := by
  have hs := (tracedStep_spec st).2
  rw [h] at hs
  exact hs

theorem tracedStep_ok_fields (st next : DriverState)
    (h : (tracedStep st).outcome = .ok next) : ∃ parent,
    ForestRefines originalEnclose st.serial parent st.forest next.forest ∧
    next.splits = st.splits + 1 ∧
    (tracedStep st).calls = [sourceLeft parent.cell,sourceRight parent.cell] ∧
    next.assertionsPassed =
      st.assertionsPassed && (tracedStep st).calls.all sourceCheck := by
  have hs := (tracedStep_spec st).2
  rw [h] at hs
  exact hs

/-- Every new call is an actual child in the resulting complete forest.
This remains true when that child has zero error and is absent from the heap.
No caller-supplied geometry or assertion premise is used. -/
theorem tracedStep_call_geometry (st next : DriverState)
    (h : (tracedStep st).outcome = .ok next) :
    ∀ box ∈ (tracedStep st).calls, Geometry box := by
  obtain ⟨parent,href,_,hcalls,_⟩ := tracedStep_ok_fields st next h
  obtain ⟨pre,post,_,hnew⟩ := forest_refines_entries href
  intro box hb
  have hchild : ∃ p ∈ children originalEnclose st.serial parent.cell, p.cell = box := by
    rw [hcalls] at hb
    simp only [List.mem_cons,List.mem_singleton] at hb
    rcases hb with rfl | rfl
    · exact ⟨issue originalEnclose (sourceLeft parent.cell) st.serial,
        by simp [children],rfl⟩
    · exact ⟨issue originalEnclose (sourceRight parent.cell)
          (advance originalEnclose (sourceLeft parent.cell) st.serial),
        by simp [children],rfl⟩
  obtain ⟨p,hp,hbox⟩ := hchild
  have hm : p ∈ entries next.forest := by
    rw [hnew]
    simp only [List.mem_append,hp,or_true,true_or]
  rw [← hbox]
  exact forestEntry_geometry next.forest geometry_mem_initialSeeds p hm

structure RunTrace where
  result : Result
  calls : List SeedCell

/-- The original bounded while loop, instrumented in chronological order.
Fuel exhaustion and either ordinary stop produce no additional enclosure
call. A failed administrative step also contributes no completed child call. -/
def tracedRunFuel : ℕ → DriverState → RunTrace
  | 0, st =>
      ⟨if keepRunning st then .failed .exhaustedFuel st else stopResult st,[]⟩
  | fuel + 1, st =>
      if keepRunning st then
        let one := tracedStep st
        match one.outcome with
        | .error reason => ⟨.failed reason st,one.calls⟩
        | .ok next =>
            let rest := tracedRunFuel fuel next
            ⟨rest.result,one.calls ++ rest.calls⟩
      else ⟨stopResult st,[]⟩

/-- Erasure retains the *exact* L Result, not just its integral or final sum.
The proof is symbolic induction and does not reduce the 2M computation. -/
theorem tracedRunFuel_result (fuel : ℕ) (st : DriverState) :
    (tracedRunFuel fuel st).result = runFuel fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : (tracedStep st).outcome with
        | error reason =>
            have hd : driverStep st = .error reason := (tracedStep_outcome st).symm.trans hs
            simp [tracedRunFuel,runFuel,hg,hs,hd]
        | ok next =>
            have hd : driverStep st = .ok next := (tracedStep_outcome st).symm.trans hs
            simpa [tracedRunFuel,runFuel,hg,hs,hd] using ih next
      · simp [tracedRunFuel,runFuel,hg]

/-- Exactly two calls per completed split, even for zero/empty enclosures.
The equality also covers early stops and failures, without assuming the
historical 2M-split guard. -/
theorem tracedRunFuel_call_count (fuel : ℕ) (st : DriverState) :
    (tracedRunFuel fuel st).calls.length + 2 * st.splits =
      2 * (tracedRunFuel fuel st).result.state.splits := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;>
        simp [tracedRunFuel,hg,stopResult,Result.state]
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : (tracedStep st).outcome with
        | error reason =>
            have hc := tracedStep_error_calls st reason hs
            simp [tracedRunFuel,hg,hs,hc,Result.state]
        | ok next =>
            obtain ⟨parent,_,hn,hcalls,_⟩ := tracedStep_ok_fields st next hs
            have hc : (tracedStep st).calls.length = 2 := by rw [hcalls]; rfl
            have hi := ih next
            simp only [tracedRunFuel,if_pos hg,hs,List.length_append]
            omega
      · simp [tracedRunFuel,hg,stopResult,Result.state]

/-- The exact Boolean meaning of L's accumulator is universal over the
chronological call history, including calls on parents subsequently retired.
It is deliberately a theorem about the *partial* sourceCheck inventory. -/
theorem tracedRunFuel_assertions (fuel : ℕ) (st : DriverState) :
    (tracedRunFuel fuel st).result.state.assertionsPassed =
      st.assertionsPassed && (tracedRunFuel fuel st).calls.all sourceCheck := by
  induction fuel generalizing st with
  | zero =>
      by_cases hg : keepRunning st <;>
        simp [tracedRunFuel,hg,stopResult,Result.state]
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : (tracedStep st).outcome with
        | error reason =>
            have hc := tracedStep_error_calls st reason hs
            simp [tracedRunFuel,hg,hs,hc,Result.state]
        | ok next =>
            obtain ⟨_,_,_,_,hflags⟩ := tracedStep_ok_fields st next hs
            simpa [tracedRunFuel,hg,hs,hflags,List.all_append,Bool.and_assoc] using ih next
      · simp [tracedRunFuel,hg,stopResult,Result.state]

/-- Reachability for every completed semantic call, including the entire
history rather than only the final forest. Reuses the existing geometry
supplier and therefore introduces no primitive-check hypothesis. -/
theorem tracedRunFuel_call_geometry (fuel : ℕ) (st : DriverState) :
    ∀ box ∈ (tracedRunFuel fuel st).calls, Geometry box := by
  induction fuel generalizing st with
  | zero => simp [tracedRunFuel]
  | succ fuel ih =>
      by_cases hg : keepRunning st
      · cases hs : (tracedStep st).outcome with
        | error reason =>
            have hc := tracedStep_error_calls st reason hs
            simp [tracedRunFuel,hg,hs,hc]
        | ok next =>
            intro box hb
            have hm : box ∈ (tracedStep st).calls ∨
                box ∈ (tracedRunFuel fuel next).calls := by
              simpa [tracedRunFuel,hg,hs] using hb
            rcases hm with hm | hm
            · exact tracedStep_call_geometry st next hs box hm
            · exact ih next box hm
      · simp [tracedRunFuel,hg]

/-- Initial calls are kept in the original normalized21 seed order. -/
def originalCallTrace : List SeedCell :=
  initialSeeds ++ (tracedRunFuel maxSplits initialDriverState).calls

/-- Source result records for each event. The kind records are not promoted
to the Python counts dictionary: Python counts only child calls, not seeds. -/
def originalCallResults : List P2OriginalCompactQ80EncloserSourceOnly.Result :=
  originalCallTrace.map P2OriginalCompactQ80EncloserSourceOnly.enclosureResult

theorem originalCallTrace_count :
    originalCallTrace.length = 21 + 2 * originalRun.state.splits := by
  have hc := tracedRunFuel_call_count maxSplits initialDriverState
  have hz : initialDriverState.splits = 0 := rfl
  have hr : (tracedRunFuel maxSplits initialDriverState).result = originalRun :=
    tracedRunFuel_result maxSplits initialDriverState
  have hi : initialSeeds.length = 21 := by
    rw [initialSeeds_eq_records,records_length]
  simp only [originalCallTrace,List.length_append,hi]
  rw [hr,hz] at hc
  omega

theorem originalCallTrace_geometry : ∀ box ∈ originalCallTrace, Geometry box := by
  intro box hb
  rcases List.mem_append.mp hb with hi | ht
  · exact geometry_mem_initialSeeds box hi
  · exact tracedRunFuel_call_geometry maxSplits initialDriverState box ht

theorem sourceCheck_of_geometry (box : SeedCell) (g : Geometry box) :
    sourceCheck box = true := by
  exact decide_eq_true
    (P2OriginalCompactQ80CompleteSoundnessSourceOnly.sourceAssertions_of_geometry box g)

/-- All per-call checks in L's existing partial inventory are already supplied
by the analytic source chain, even on historical calls no longer in the forest.
This does not assert tableAssertions or any missing internal primitive check. -/
theorem originalCallTrace_sourceChecks : originalCallTrace.all sourceCheck = true := by
  apply List.all_eq_true.mpr
  intro box hb
  exact sourceCheck_of_geometry box (originalCallTrace_geometry box hb)

/-- Exact accumulator accounting, before using the per-call supplier. -/
theorem originalRun_assertions_trace :
    originalRun.state.assertionsPassed =
      P2OriginalCompactQ80EncloserSourceOnly.tableAssertions &&
        originalCallTrace.all sourceCheck := by
  have h := tracedRunFuel_assertions maxSplits initialDriverState
  rw [tracedRunFuel_result] at h
  change originalRun.state.assertionsPassed = _ at h
  simpa [initialDriverState,originalCallTrace,List.all_append,Bool.and_assoc] using h

/-- The residual Boolean is exactly the table initialization diagnostics.
No closed guard is evaluated and no assertion truth is supplied as a premise. -/
theorem originalRun_assertions_eq_tableAssertions :
    originalRun.state.assertionsPassed =
      P2OriginalCompactQ80EncloserSourceOnly.tableAssertions := by
  rw [originalRun_assertions_trace,originalCallTrace_sourceChecks]
  simp

end ImbalancedChen.P2OriginalCompactMainCallTraceSourceOnly
