import ImbalancedChen.P2OriginalCompactCachedRun

/-!
Independent, uncompiled design draft for a possible B prefix certificate.

Source definitions were read at commit
6e616f4e0372555f7a78bcdba3e198d0e277eec8.  This file imports the existing
cached driver; it does not copy or alter its evaluator, guards, state, fuel
semantics, endpoint predicate, constants, or project import graph.

An empty prefix suspends BEFORE the next guard.  In particular, it is not
the original `cachedRunFuel ... 0`, which can fail with `exhaustedFuel`.
Every prefix successor calls the original guard and complete original
cached step.  Actual early stops and failures retain their whole Result.
The original zero-fuel operation is used only by the final continuation.

This is a semantic composition draft, not a compilation, resource, or
canonical B result.  No closed state or computed charge is installed here.
-/

namespace P24CachedRunPrefixCompositionDraft

open ImbalancedChen.P2OriginalCompactConcreteRunSourceOnly
open ImbalancedChen.P2OriginalCompactConcreteLoopSourceOnly
open ImbalancedChen.P2OriginalCompactCachedRunSourceOnly

private inductive CachedPrefixResult where
  | suspended (state : DriverState)
  | terminal (result : Result)

private def cachedPrefix (nodes : Nodes) (fixed : ℚ) (count : ℕ) :
    DriverState → CachedPrefixResult :=
  Nat.rec (motive := fun _ => DriverState → CachedPrefixResult)
    (fun st => .suspended st)
    (fun _ previous st =>
      if cachedKeepRunning fixed st then
        match cachedStep nodes st with
        | .error reason => .terminal (.failed reason st)
        | .ok next => previous next
      else .terminal (stopResult st)) count

private def resumeCachedPrefix (nodes : Nodes) (fixed : ℚ) (remaining : ℕ) :
    CachedPrefixResult → Result
  | .suspended st => cachedRunFuel nodes fixed remaining st
  | .terminal result => result

private def continueCachedPrefix (nodes : Nodes) (fixed : ℚ) (count : ℕ) :
    CachedPrefixResult → CachedPrefixResult
  | .suspended st => cachedPrefix nodes fixed count st
  | .terminal result => .terminal result

/-- No success or terminal hypothesis is required: both branches are exact. -/
private theorem cachedRunFuel_prefix (nodes : Nodes) (fixed : ℚ)
    (count remaining : ℕ) (st : DriverState) :
    cachedRunFuel nodes fixed (count + remaining) st =
      resumeCachedPrefix nodes fixed remaining (cachedPrefix nodes fixed count st) := by
  induction count generalizing st with
  | zero =>
      exact congrArg (fun fuel => cachedRunFuel nodes fixed fuel st) (Nat.zero_add remaining)
  | succ count ih =>
      rw [Nat.succ_add]
      change
        (if cachedKeepRunning fixed st then
          match cachedStep nodes st with
          | .error reason => Result.failed reason st
          | .ok next => cachedRunFuel nodes fixed (count + remaining) next
        else stopResult st) =
        resumeCachedPrefix nodes fixed remaining
          (if cachedKeepRunning fixed st then
            match cachedStep nodes st with
            | .error reason => CachedPrefixResult.terminal (Result.failed reason st)
            | .ok next => cachedPrefix nodes fixed count next
          else CachedPrefixResult.terminal (stopResult st))
      by_cases hg : cachedKeepRunning fixed st
      · simp only [if_pos hg]
        cases hstep : cachedStep nodes st with
        | error reason => rfl
        | ok next => exact ih next
      · simp only [if_neg hg, resumeCachedPrefix]

/-- A terminated prefix remains terminated when more prefix fuel is appended. -/
private theorem cachedPrefix_add (nodes : Nodes) (fixed : ℚ)
    (count more : ℕ) (st : DriverState) :
    cachedPrefix nodes fixed (count + more) st =
      continueCachedPrefix nodes fixed more (cachedPrefix nodes fixed count st) := by
  induction count generalizing st with
  | zero =>
      exact congrArg (fun fuel => cachedPrefix nodes fixed fuel st) (Nat.zero_add more)
  | succ count ih =>
      rw [Nat.succ_add]
      change
        (if cachedKeepRunning fixed st then
          match cachedStep nodes st with
          | .error reason => CachedPrefixResult.terminal (Result.failed reason st)
          | .ok next => cachedPrefix nodes fixed (count + more) next
        else CachedPrefixResult.terminal (stopResult st)) =
        continueCachedPrefix nodes fixed more
          (if cachedKeepRunning fixed st then
            match cachedStep nodes st with
            | .error reason => CachedPrefixResult.terminal (Result.failed reason st)
            | .ok next => cachedPrefix nodes fixed count next
          else CachedPrefixResult.terminal (stopResult st))
      by_cases hg : cachedKeepRunning fixed st
      · simp only [if_pos hg]
        cases hstep : cachedStep nodes st with
        | error reason => rfl
        | ok next => exact ih next
      · simp only [if_neg hg, continueCachedPrefix]

private theorem cachedRunFuel_of_suspended_prefix (nodes : Nodes) (fixed : ℚ)
    (count remaining : ℕ) (st next : DriverState)
    (hp : cachedPrefix nodes fixed count st = .suspended next) :
    cachedRunFuel nodes fixed (count + remaining) st =
      cachedRunFuel nodes fixed remaining next := by
  exact (cachedRunFuel_prefix nodes fixed count remaining st).trans
    (congrArg (resumeCachedPrefix nodes fixed remaining) hp)

private theorem cachedRunFuel_of_terminal_prefix (nodes : Nodes) (fixed : ℚ)
    (count remaining : ℕ) (st : DriverState) (result : Result)
    (hp : cachedPrefix nodes fixed count st = .terminal result) :
    cachedRunFuel nodes fixed (count + remaining) st = result := by
  exact (cachedRunFuel_prefix nodes fixed count remaining st).trans
    (congrArg (resumeCachedPrefix nodes fixed remaining) hp)

/-- The existing zero-fuel branch stops normally only once its guard is false. -/
private theorem cachedRunFuel_zero_of_budget (nodes : Nodes) (fixed : ℚ)
    (st : DriverState) (hs : st.splits = maxSplits) :
    cachedRunFuel nodes fixed 0 st = .stopped .budget st := by
  have hbudget : ¬ st.splits < maxSplits := by
    rw [hs]
    exact Nat.lt_irrefl _
  have hstop : ¬ cachedKeepRunning fixed st := fun h => hbudget h.1
  simp only [cachedRunFuel, if_neg hstop, stopResult, if_neg hbudget]

private theorem cachedRunFuel_of_budget_prefix (nodes : Nodes) (fixed : ℚ)
    (st next : DriverState)
    (hp : cachedPrefix nodes fixed maxSplits st = .suspended next)
    (hs : next.splits = maxSplits) :
    cachedRunFuel nodes fixed maxSplits st = .stopped .budget next := by
  exact (cachedRunFuel_of_suspended_prefix nodes fixed maxSplits 0 st next hp).trans
    (cachedRunFuel_zero_of_budget nodes fixed next hs)

/-- This retains the complete prefix premise AND every original endpoint field.
It supplies no closed prefix or final-state data. -/
private theorem historicalCheck_of_budget_prefix (nodes : Nodes) (fixed : ℚ)
    (st next : DriverState)
    (hp : cachedPrefix nodes fixed maxSplits st = .suspended next)
    (hs : next.splits = maxSplits)
    (hu : next.totalUpper = historicalUpper)
    (hq : Batteries.PairingHeap.size next.queue = 1852040)
    (ha : next.assertionsPassed = true) :
    historicalEndpointCheckFor (cachedRunFuel nodes fixed maxSplits st) = true := by
  rw [cachedRunFuel_of_budget_prefix nodes fixed st next hp hs]
  simp [historicalEndpointCheckFor, hs, hu, hq, ha]

end P24CachedRunPrefixCompositionDraft
