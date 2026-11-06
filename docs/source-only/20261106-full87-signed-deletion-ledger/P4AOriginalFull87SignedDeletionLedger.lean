import ImbalancedChen.P4AOriginalFull87WeightedRootTransport
import ImbalancedChen.P4AOriginalFull87ActualDeletionOnce
import ImbalancedChen.P4AOriginalFull87PhysicalFailedWeights
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4: compare the SAME physical g_N failed-select occurrence with its
single target-prime-deletion-factor adjustment. The comparison is signed:
the total error is bounded by an absolute occurrence sum, not by cap
monotonicity, sign cancellation, or a second sieve coefficient.

The rank-nine inherited-square failures (older.length = 8) are
INTENTIONALLY EXCLUDED. Every selected, rejected and suffix prime comes
from the original target-deleted physical first-exit recursion, and the
original owner/trim state list is retained with occurrence multiplicity.
The adjusted sum is a finite comparison ledger; it is NOT asserted equal
to a new independently normalized arithmetic density or to an external
ordinary sieve main term.

RealizedHistory is the already-existing manuscript-internal history
membership premise. Full supply of that premise on every owned state,
original saved87 archive checks and kernel elaboration remain open.
-/

namespace ImbalancedChen.P4AOriginalFull87SignedDeletionLedger
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87OwnedEighthSource
  (states_eq_owner_filter frontier_sign_mass)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts)
open P4AOriginalFull87PhysicalFailedWeights
  (failed_attempt_labels_independent_of_weights)
open P4AOriginalFull87ActualDeletionOnce
  (owned87_later_failed_target_deletion_once)
open P4AOriginalFull87TargetPrimeDeletion (targetDeletionFactor)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)

/-- Exactly the physical post-eight attempts used by the previous
root-to-eighth correction equality. The eighth incoming mass includes
the root-selected product once, and is NOT reweighted on the skip path. -/
def physicalFailedAt
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    List (FirstExitRejectedAttempt ℕ) :=
  firstExitRejectedAttempts
    (ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s useParent))
    halfProductDensity s.selectedPrefix s.positive
    (s.mass * (s.selectedPrefix.map halfProductDensity).prod) s.remaining

/-- The physical list above is literally the failed-list expression in the
already-existing root-transported correction at an actual owned unit state.
In particular s.mass=1; the eighth product must NOT be inserted twice. -/
theorem physicalFailedAt_eq_root_transported
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) (useParent : Bool) :
    physicalFailedAt n e q om N c s useParent =
      firstExitRejectedAttempts
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        halfProductDensity s.selectedPrefix s.positive
        (s.selectedPrefix.map halfProductDensity).prod s.remaining := by
  have hs' := hs
  rw [states_eq_owner_filter] at hs'
  have hfront : s ∈ P4AOriginalFull87OwnedEighthSource.frontier
      n e q om N cap w z := (List.mem_filter.mp hs').1
  have hmass := (frontier_sign_mass n e q om N cap w z s hfront).2
  simp [physicalFailedAt, hmass]

/-- The physical rejected event has a UNIT-weight event with exactly
the same occurrence key (history, rejected prime, suffix, sign). The
mass deliberately differs; no equality of these masses is claimed. -/
theorem physical_failed_has_unit_key
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ physicalFailedAt n e q om N c s useParent) :
    ∃ b : FirstExitRejectedAttempt ℕ,
      b ∈ firstExitRejectedAttempts
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        (fun _ : ℕ => (1 : ℝ)) s.selectedPrefix s.positive s.mass s.remaining ∧
      b.older = a.older ∧ b.rejected = a.rejected ∧
      b.smaller = a.smaller ∧ b.positive = a.positive := by
  let policy := ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s useParent)
  let label : FirstExitRejectedAttempt ℕ →
      (List ℕ × ℕ × List ℕ × Bool) :=
    fun x => (x.older, x.rejected, x.smaller, x.positive)
  have hlabels :=
    failed_attempt_labels_independent_of_weights
      policy halfProductDensity (fun _ : ℕ => (1 : ℝ))
      s.selectedPrefix s.remaining s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod) s.mass
  have hmem : label a ∈
      (firstExitRejectedAttempts policy halfProductDensity
        s.selectedPrefix s.positive
        (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
        s.remaining).map label := by
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  rw [hlabels] at hmem
  obtain ⟨b, hb, hkey⟩ := List.mem_map.mp hmem
  change (b.older, b.rejected, b.smaller, b.positive) =
    (a.older, a.rejected, a.smaller, a.positive) at hkey
  refine ⟨b, hb, ?_, ?_, ?_, ?_⟩
  · exact congrArg (fun t : List ℕ × ℕ × List ℕ × Bool => t.1) hkey
  · exact congrArg (fun t : List ℕ × ℕ × List ℕ × Bool => t.2.1) hkey
  · exact congrArg (fun t : List ℕ × ℕ × List ℕ × Bool => t.2.2.1) hkey
  · exact congrArg (fun t : List ℕ × ℕ × List ℕ × Bool => t.2.2.2) hkey

/-- The EXACT integer rank of a later odd failed event determines its
budget. No synthetic t-index or independently chosen mask enters it. -/
def laterDeletionBudget (a : FirstExitRejectedAttempt ℕ) : ℝ :=
  (((261 * 3 ^ ((a.older.length - 10) / 2 + 2) : ℕ) : ℝ)) /
    ((a.rejected : ℝ) - 1)

/-- The comparison changes a physical failed event only by ONE finite
factor, with no alteration of its signed value or suffix Euler product. -/
def adjustedFailedValue (N hi : ℕ) (a : FirstExitRejectedAttempt ℕ) : ℝ :=
  a.value halfProductDensity * targetDeletionFactor N a.rejected hi

/-- Signed finite arithmetic: the factor is bounded in [0,1], so the
error is at most the absolute original signed coefficient times the
one-factor loss. Neither sign of v is presumed. -/
theorem signed_one_factor_error (v D E : ℝ)
    (hD : D ≤ 1) (hLower : 1 - E ≤ D) :
    |v - v * D| ≤ |v| * E := by
  have hzero : 0 ≤ 1 - D := sub_nonneg.mpr hD
  have herror : 1 - D ≤ E := by linarith
  calc
    |v - v * D| = |v * (1 - D)| := by congr 1 <;> ring
    _ = |v| * |1 - D| := abs_mul v (1 - D)
    _ = |v| * (1 - D) := by rw [abs_of_nonneg hzero]
    _ ≤ |v| * E := mul_le_mul_of_nonneg_left herror (abs_nonneg v)

/-- Transfer the PREVIOUS integer power-gap deletion bound from the
unit key to the same genuine physical event, then pay the factor once.
This is restricted to rank >= 11 and uses the previously supplied
RealizedHistory premise, not a fabricated exit certificate. -/
theorem owned87_physical_later_event_signed_error
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hEven : 2 ∣ N)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (useParent : Bool) (hi : ℕ) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ physicalFailedAt n e q om N c s useParent)
    (hlater : 8 < a.older.length) :
    |a.value halfProductDensity - adjustedFailedValue N hi a| ≤
      |a.value halfProductDensity| * laterDeletionBudget a := by
  obtain ⟨b, hb, hOlder, hRejected, _hSmaller, _hPositive⟩ :=
    physical_failed_has_unit_key n e q om N c s useParent a ha
  have hblater : 8 < b.older.length := by
    rw [hOlder]
    exact hlater
  obtain ⟨m, hRank, _hDpos, hDupper, hDlower⟩ :=
    owned87_later_failed_target_deletion_once
      r n hn e q om N cap hN hEven w z c s hs hr
      useParent b hb hblater hi
  have hRankA : a.older.length = 10 + 2 * m := by
    simpa only [hOlder] using hRank
  have hM : (a.older.length - 10) / 2 = m := by omega
  have hUpperA : targetDeletionFactor N a.rejected hi ≤ 1 := by
    simpa only [hRejected] using hDupper
  have hLowerA :
      1 - laterDeletionBudget a ≤
        targetDeletionFactor N a.rejected hi := by
    dsimp [laterDeletionBudget]
    rw [hM]
    simpa only [hRejected] using hDlower
  exact signed_one_factor_error
    (a.value halfProductDensity) (targetDeletionFactor N a.rejected hi)
    (laterDeletionBudget a) hUpperA hLowerA

/-- A finite signed-sum bound proved by induction, retaining repeated
occurrences rather than converting the list into a Finset. -/
private theorem list_signed_sum_error {α : Type*}
    (xs : List α) (f g budget : α → ℝ) :
    (∀ x ∈ xs, |f x - g x| ≤ budget x) →
      |(xs.map f).sum - (xs.map g).sum| ≤ (xs.map budget).sum := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x xs ih =>
      intro h
      have hx : |f x - g x| ≤ budget x :=
        h x (by simp)
      have hxs : ∀ y ∈ xs, |f y - g y| ≤ budget y := by
        intro y hy
        exact h y (by simp [hy])
      have hrest := ih hxs
      simp only [List.map_cons, List.sum_cons]
      calc
        |f x + (xs.map f).sum - (g x + (xs.map g).sum)| =
            |(f x - g x) + ((xs.map f).sum - (xs.map g).sum)| := by
              congr 1 <;> ring
        _ ≤ |f x - g x| +
            |(xs.map f).sum - (xs.map g).sum| := abs_add_le _ _
        _ ≤ budget x + (xs.map budget).sum := add_le_add hx hrest

/-- Keep precisely the actual later-odd attempts; rank-nine inherited
square failures are left separate and receive NO deletion payment here. -/
def laterPhysicalFailedAt
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    List (FirstExitRejectedAttempt ℕ) :=
  (physicalFailedAt n e q om N c s useParent).filter
    (fun a => decide (8 < a.older.length))

def physicalLaterSigned
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) : ℝ :=
  ((laterPhysicalFailedAt n e q om N c s useParent).map
    (FirstExitRejectedAttempt.value halfProductDensity)).sum

def adjustedLaterSigned
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N hi : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) : ℝ :=
  ((laterPhysicalFailedAt n e q om N c s useParent).map
    (adjustedFailedValue N hi)).sum

def laterAbsoluteBudget
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) : ℝ :=
  ((laterPhysicalFailedAt n e q om N c s useParent).map
    (fun a => |a.value halfProductDensity| * laterDeletionBudget a)).sum

/-- Pointwise physical correction error at an ACTUAL eighth occurrence,
with the exact signs, incoming mass, and remaining suffix still present. -/
theorem owned87_physical_later_state_signed_error
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hEven : 2 ∣ N)
    (w z : ℝ) (c : Cell) (s : FirstExitDepthState ℕ)
    (hs : s ∈ states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (hr : RealizedHistory e q om (N : ℝ) s.selectedPrefix c)
    (useParent : Bool) (hi : ℕ) :
    |physicalLaterSigned n e q om N c s useParent -
      adjustedLaterSigned n e q om N hi c s useParent| ≤
      laterAbsoluteBudget n e q om N c s useParent := by
  unfold physicalLaterSigned adjustedLaterSigned laterAbsoluteBudget
  apply list_signed_sum_error
  intro a ha
  have hrecord : a ∈ physicalFailedAt n e q om N c s useParent :=
    (List.mem_filter.mp ha).1
  have hlater : 8 < a.older.length :=
    of_decide_eq_true (List.mem_filter.mp ha).2
  exact owned87_physical_later_event_signed_error
    r n hn e q om N cap hN hEven w z c s hs hr
    useParent hi a hrecord hlater

/-- Original full87 owner/trim state list, including all repeated
occurrences. This is only the later-odd part of each frozen continuation,
not the unproved total signed saving. -/
def ownedPhysicalLaterSigned
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (useParent : Bool) : ℝ :=
  ((states (width r) n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c).map
      (fun s => physicalLaterSigned n e q om N c s useParent)).sum

def ownedAdjustedLaterSigned
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap hi : ℕ) (w z : ℝ) (c : Cell) (useParent : Bool) : ℝ :=
  ((states (width r) n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c).map
      (fun s => adjustedLaterSigned n e q om N hi c s useParent)).sum

def ownedLaterAbsoluteBudget
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (useParent : Bool) : ℝ :=
  ((states (width r) n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c).map
      (fun s => laterAbsoluteBudget n e q om N c s useParent)).sum

/-- A genuine full87 signed, multiplicity-preserving finite comparison.
Each physical event is adjusted at most once. The explicit same-history
premise has NOT been supplied for every state and remains a yellow
manuscript-internal obligation. No sign, coefficient, or external
distribution mean is inferred from a separate sieve bound. -/
theorem owned87_later_physical_signed_deletion_ledger
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hEven : 2 ∣ N)
    (w z : ℝ) (c : Cell) (useParent : Bool) (hi : ℕ)
    (hHistory : ∀ s ∈ states (width r) n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c,
      RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    |ownedPhysicalLaterSigned r n e q om N cap w z c useParent -
      ownedAdjustedLaterSigned r n e q om N cap hi w z c useParent| ≤
      ownedLaterAbsoluteBudget r n e q om N cap w z c useParent := by
  unfold ownedPhysicalLaterSigned ownedAdjustedLaterSigned ownedLaterAbsoluteBudget
  apply list_signed_sum_error
  intro s hs
  exact owned87_physical_later_state_signed_error
    r n hn e q om N cap hN hEven w z c s hs
    (hHistory s hs) useParent hi

end
end ImbalancedChen.P4AOriginalFull87SignedDeletionLedger
