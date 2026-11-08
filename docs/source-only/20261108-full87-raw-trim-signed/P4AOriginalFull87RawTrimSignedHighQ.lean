import ImbalancedChen.P4AOriginalFull87RawOwnerPartition
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import ImbalancedChen.P4AOriginalFull87StrictActionTrim
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A signed FULL-PHYSICAL-q terminal test on the ORIGINAL complete-sixth
rank-eight frontier, partitioned by the ORIGINAL 87-cell owner and the
ORIGINAL strict trim predicate. The unowned and trimmed-out terms are kept
as genuine signed remainders, never declared zero. No numerical archive gain
is used as arithmetic source membership.

IMPORTANT: the complete-sixth raw producer and the filtered/licensed sixth
producer are DIFFERENT finite lists. This file proves an identity on the
raw producer only. It does NOT silently identify its trimmed list with
the filtered tree's states and does not claim an H_N error estimate.
-/

namespace ImbalancedChen.P4AOriginalFull87RawTrimSignedHighQ
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (signedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87ActualSourceMembership (sourceStates)
open P4AOriginalFull87RawOwnerPartition
open P4AOriginalFull87StrictActionTrim (trim)

/-- The ORIGINAL complete-sixth policy is used on each raw frontier
suffix. This is not the licensed sixth actualParent of the different
filtered tree. The sign and mass belong to this exact occurrence. -/
def rawSignedHighQ (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    s.selectedPrefix s.positive s.mass s.remaining

/-- The source-owned raw frontier occurrences retained by the ORIGINAL
strict eighth trim. No deduplication or replacement of sourceStates. -/
def rawOwnedTrimmed (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (sourceStates e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).filter
    (fun s => decide (point8 (N : ℝ) s.selectedPrefix ∈ trim c delta))

/-- The ORIGINAL owned raw occurrences outside the strict trim.
They are NOT an arithmetic null set and must be invoiced. -/
def rawOwnedTrimOmitted (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (sourceStates e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).filter
    (fun s => decide (¬ point8 (N : ℝ) s.selectedPrefix ∈ trim c delta))

/-- A LIST is partitioned without assuming Nodup, hence every repeated
signed occurrence is preserved. -/
private theorem list_filter_complement_sum {α : Type*}
    (xs : List α) (p : α → Prop) (f : α → ℝ) :
    (xs.map f).sum =
      ((xs.filter (fun x => decide (p x))).map f).sum +
      ((xs.filter (fun x => decide (¬ p x))).map f).sum := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x
      · simp [List.filter_cons, hx, ih]
        ring
      · simp [List.filter_cons, hx, ih]
        ring

/-- The ORIGINAL owner fibre is exactly the retained plus omitted
raw List, with the same arithmetic high-q value on both sides. -/
theorem raw_owned_trim_omitted_highQ
    (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) :
    ((sourceStates e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
       (rawSignedHighQ e q om N cap w L X F)).sum =
      ((rawOwnedTrimmed delta e q om N cap w z c).map
         (rawSignedHighQ e q om N cap w L X F)).sum +
      ((rawOwnedTrimOmitted delta e q om N cap w z c).map
         (rawSignedHighQ e q om N cap w L X F)).sum := by
  classical
  simpa only [rawOwnedTrimmed, rawOwnedTrimOmitted] using
    (list_filter_complement_sum
      (sourceStates e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)
      (fun s => point8 (N : ℝ) s.selectedPrefix ∈ trim c delta)
      (rawSignedHighQ e q om N cap w L X F))

/-- First EXACT owner/unowned, then EXACT strict-trim split, for the same
original complete-sixth rank-eight frontier and signed full-q test.
Neither missing term is set to zero or replaced by a geometric measure. -/
theorem actual_raw_highQ_unowned_trim_omitted
    (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
      (rawSignedHighQ e q om N cap w L X F)).sum =
      (((actualUnownedFrontier e q om N cap w z
        (fun _ : ℕ => (1 : ℝ))).map
          (rawSignedHighQ e q om N cap w L X F)).sum +
       ∑ c : Cell,
         ((rawOwnedTrimmed delta e q om N cap w z c).map
           (rawSignedHighQ e q om N cap w L X F)).sum) +
       ∑ c : Cell,
         ((rawOwnedTrimOmitted delta e q om N cap w z c).map
           (rawSignedHighQ e q om N cap w L X F)).sum := by
  have howner :=
    actual_raw_owned_unowned_sum e q om N cap w z
      (fun _ : ℕ => (1 : ℝ))
      (rawSignedHighQ e q om N cap w L X F)
  have htrim :
      (∑ c : Cell,
        ((sourceStates e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
          (rawSignedHighQ e q om N cap w L X F)).sum) =
      (∑ c : Cell,
        ((rawOwnedTrimmed delta e q om N cap w z c).map
          (rawSignedHighQ e q om N cap w L X F)).sum) +
      (∑ c : Cell,
        ((rawOwnedTrimOmitted delta e q om N cap w z c).map
          (rawSignedHighQ e q om N cap w L X F)).sum) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    exact raw_owned_trim_omitted_highQ delta e q om N cap w z L X F c
  rw [howner, htrim]
  ring

private theorem abs_map_sum_le_map_abs {α : Type*} (xs : List α)
    (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa only [List.map_cons, List.sum_cons] using
        (abs_add (f x) ((xs.map f).sum)).trans
          (add_le_add_left ih |f x|)

/-- An explicit NONNEGATIVE arithmetic invoice for the outside-trim
part: unowned raw occurrences PLUS genuinely owned-but-omitted raw
occurrences. No charge is applied to unrelated inherited branches. -/
def rawOutsideHighQInvoice
    (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((actualUnownedFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
    (fun s => |rawSignedHighQ e q om N cap w L X F s|)).sum +
  ∑ c : Cell,
    ((rawOwnedTrimOmitted delta e q om N cap w z c).map
      (fun s => |rawSignedHighQ e q om N cap w L X F s|)).sum

/-- Signed raw mass minus retained raw owner mass is controlled by the
ACTUAL two disjoint outside lists. This does NOT assert the invoice is
small relative to H_N and does NOT equate raw trim with licensed states. -/
theorem abs_raw_highQ_minus_trimmed_le_outside_invoice
    (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
       (rawSignedHighQ e q om N cap w L X F)).sum -
       (∑ c : Cell,
         ((rawOwnedTrimmed delta e q om N cap w z c).map
           (rawSignedHighQ e q om N cap w L X F)).sum)| ≤
       rawOutsideHighQInvoice delta e q om N cap w z L X F := by
  let v := rawSignedHighQ e q om N cap w L X F
  let U := actualUnownedFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))
  let E := fun c : Cell => rawOwnedTrimOmitted delta e q om N cap w z c
  have hs := actual_raw_highQ_unowned_trim_omitted
    delta e q om N cap w z L X F
  have hrewrite :
      ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map v).sum -
        (∑ c : Cell, ((rawOwnedTrimmed delta e q om N cap w z c).map v).sum) =
      (U.map v).sum + ∑ c : Cell, ((E c).map v).sum := by
    dsimp only [v, U, E]
    linarith
  rw [hrewrite]
  unfold rawOutsideHighQInvoice
  change |(U.map v).sum + ∑ c : Cell, ((E c).map v).sum| ≤
    (U.map (fun s => |v s|)).sum +
      ∑ c : Cell, ((E c).map (fun s => |v s|)).sum
  calc
    |(U.map v).sum + ∑ c : Cell, ((E c).map v).sum| ≤
        |(U.map v).sum| + |∑ c : Cell, ((E c).map v).sum| := abs_add _ _
    _ ≤ (U.map (fun s => |v s|)).sum +
        ∑ c : Cell, ((E c).map (fun s => |v s|)).sum := by
      apply add_le_add (abs_map_sum_le_map_abs U v)
      calc
        |∑ c : Cell, ((E c).map v).sum| ≤
          ∑ c : Cell, |((E c).map v).sum| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ c : Cell, ((E c).map (fun s => |v s|)).sum := by
          apply Finset.sum_le_sum
          intro c _
          exact abs_map_sum_le_map_abs (E c) v

end
end ImbalancedChen.P4AOriginalFull87RawTrimSignedHighQ
