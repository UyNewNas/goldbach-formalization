import ImbalancedChen.P4AOriginalFull87RawTrimSignedHighQ
import ImbalancedChen.P4AOriginalFull87LicensedSixthRealization
import ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An occurrence-preserving, exact producer-change ledger between the ORIGINAL
complete-sixth raw/trimmed 87-cell frontier and the ACTUAL licensed-sixth
filtered 87-cell frontier.  In particular these two lists are NOT identified.

A matched occurrence is an equality of the FULL first-exit state, including
selected prefix, incoming sign, mass, and remaining carrier.  The scan
consumes exactly one new occurrence on each match.  A matched occurrence
pays the difference of the two genuine signed full-modulus continuations;
a raw-only/new-only occurrence pays its own signed absolute contribution.
No monotonic signed-saving assertion, PP licence, or H_N bound is implied.
-/

namespace ImbalancedChen.P4AOriginalFull87ProducerChangeInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (signedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87RawTrimSignedHighQ
open P4AOriginalFull87LicensedSixthRealization (states)

/-- Remove exactly ONE occurrence, never all copies of an equal state. -/
private def eraseOne {α : Type*} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if y = x then ys else y :: eraseOne x ys

private theorem eraseOne_sum {α : Type*} [DecidableEq α]
    (x : α) (ys : List α) (g : α → ℝ) (hx : x ∈ ys) :
    (ys.map g).sum = g x + ((eraseOne x ys).map g).sum := by
  induction ys with
  | nil => cases hx
  | cons y ys ih =>
      by_cases h : y = x
      · subst y
        simp [eraseOne]
      · have htail : x ∈ ys := by simpa [h] using hx
        have he := ih htail
        rw [show eraseOne x (y :: ys) = y :: eraseOne x ys by
          simp [eraseOne, h]]
        simp only [List.map_cons, List.sum_cons]
        rw [he]
        ring

/-- The recursive ledger scans the actual raw list and consumes at most
one copy of an equal state from the actual licensed list. The first
coordinate is signed; the second is an explicit nonnegative invoice.
Pairing is on the WHOLE state, not merely the geometric label. -/
def producerLedger {α : Type*} [DecidableEq α] (f g : α → ℝ) :
    List α → List α → ℝ × ℝ
  | [], ys => (-(ys.map g).sum, (ys.map (fun y => |g y|)).sum)
  | x :: xs, ys =>
      if x ∈ ys then
        let tail := producerLedger f g xs (eraseOne x ys)
        (f x - g x + tail.1, |f x - g x| + tail.2)
      else
        let tail := producerLedger f g xs ys
        (f x + tail.1, |f x| + tail.2)

/-- Both actual List sums are accounted for exactly, even with repeated
occurrences and potentially different continuation values on a matched
state. No equality of producer frontiers is needed. -/
theorem producerLedger_signed {α : Type*} [DecidableEq α]
    (f g : α → ℝ) (xs ys : List α) :
    (producerLedger f g xs ys).1 = (xs.map f).sum - (ys.map g).sum := by
  induction xs generalizing ys with
  | nil => simp [producerLedger]
  | cons x xs ih =>
      by_cases hx : x ∈ ys
      · have he := eraseOne_sum x ys g hx
        simp only [producerLedger, if_pos hx, Prod.fst, List.map_cons,
          List.sum_cons]
        rw [ih (eraseOne x ys), he]
        ring
      · simp only [producerLedger, if_neg hx, Prod.fst, List.map_cons,
          List.sum_cons]
        rw [ih ys]
        ring

private theorem abs_list_sum_le_sum_abs {α : Type*}
    (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add (f x) ((xs.map f).sum)).trans
        (add_le_add_left ih |f x|)

/-- Matched copies pay |raw value - licensed value|; unmatched copies
pay their OWN absolute values. This is generally sharper than charging
all raw and all licensed occurrences separately. It does not claim any
numerical saving until the actual finite lists are evaluated. -/
theorem producerLedger_abs_le_cost {α : Type*} [DecidableEq α]
    (f g : α → ℝ) (xs ys : List α) :
    |(producerLedger f g xs ys).1| ≤ (producerLedger f g xs ys).2 := by
  induction xs generalizing ys with
  | nil =>
      simpa [producerLedger] using abs_list_sum_le_sum_abs ys g
  | cons x xs ih =>
      by_cases hx : x ∈ ys
      · simp only [producerLedger, if_pos hx, Prod.fst, Prod.snd]
        exact (abs_add (f x - g x)
          (producerLedger f g xs (eraseOne x ys)).1).trans
            (add_le_add_left (ih (eraseOne x ys)) |f x - g x|)
      · simp only [producerLedger, if_neg hx, Prod.fst, Prod.snd]
        exact (abs_add (f x) (producerLedger f g xs ys).1).trans
          (add_le_add_left (ih ys) |f x|)

/-- Genuine licensed-sixth/eighth physical full-q test at this exact new
state. Its sixth cap, selected eighth owner/cap, and entire beta terminal
are those of the NEW producer, not the raw complete-sixth producer. -/
def licensedSignedHighQ (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ))
    (attachedLeafTest N cap 1 w L (highQTest X F))
    s.selectedPrefix s.positive s.mass s.remaining

/-- No hypothetical pairing input: both lists and the two real
continuations are fully instantiated from their genuine producers.
The classical equality oracle compares FULL states and consumes copies. -/
noncomputable def actualCellLedger (delta : ℝ) (n : ℕ) (e : ℚ)
    (q : ℕ) (om : ℝ) (N cap : ℕ) (w z L : ℝ)
    (X : ℕ) (F : ℕ → ℝ) (c : Cell) : ℝ × ℝ := by
  classical
  exact producerLedger
    (rawSignedHighQ e q om N cap w L X F)
    (licensedSignedHighQ delta n e q om N cap w L X F)
    (rawOwnedTrimmed delta e q om N cap w z c)
    (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)

/-- The exact raw-trim to licensed/filtered producer-change difference.
An actual shared state is paired ONCE, with genuine source-specific tests;
all lost/introduced copies remain in the ledger rather than vanishing. -/
theorem actual_trim_to_licensed_signed_eq_ledger
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    (∑ c : Cell,
      ((rawOwnedTrimmed delta e q om N cap w z c).map
        (rawSignedHighQ e q om N cap w L X F)).sum) -
    (∑ c : Cell,
      ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
        (licensedSignedHighQ delta n e q om N cap w L X F)).sum) =
    ∑ c : Cell, (actualCellLedger delta n e q om N cap w z L X F c).1 := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simpa only [actualCellLedger] using
    (producerLedger_signed
      (rawSignedHighQ e q om N cap w L X F)
      (licensedSignedHighQ delta n e q om N cap w L X F)
      (rawOwnedTrimmed delta e q om N cap w z c)
      (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)).symm

/-- The separately auditable actual producer-change charge. It does not
include the raw unowned or strict-trim-omitted occurrences, which have
already been charged by rawOutsideHighQInvoice. -/
def licensedProducerInvoice (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ c : Cell, (actualCellLedger delta n e q om N cap w z L X F c).2

theorem abs_trim_to_licensed_le_producer_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |(∑ c : Cell,
      ((rawOwnedTrimmed delta e q om N cap w z c).map
        (rawSignedHighQ e q om N cap w L X F)).sum) -
     (∑ c : Cell,
      ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
        (licensedSignedHighQ delta n e q om N cap w L X F)).sum)| ≤
      licensedProducerInvoice delta n e q om N cap w z L X F := by
  classical
  rw [actual_trim_to_licensed_signed_eq_ledger]
  unfold licensedProducerInvoice
  calc
    |∑ c : Cell, (actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      ∑ c : Cell, |(actualCellLedger delta n e q om N cap w z L X F c).1| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell, (actualCellLedger delta n e q om N cap w z L X F c).2 := by
      apply Finset.sum_le_sum
      intro c _
      simpa only [actualCellLedger] using
        producerLedger_abs_le_cost
          (rawSignedHighQ e q om N cap w L X F)
          (licensedSignedHighQ delta n e q om N cap w L X F)
          (rawOwnedTrimmed delta e q om N cap w z c)
          (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)

/-- Once-only composition: ORIGINAL raw/unowned/strict-omitted cost PLUS
actual changed-producer cost. Neither physical frontier is equated with
the other, nor is any geometric null set made arithmetically free. -/
theorem abs_raw_to_actual_licensed_owned_le_separate_invoices
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
        (rawSignedHighQ e q om N cap w L X F)).sum -
      (∑ c : Cell,
        ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
          (licensedSignedHighQ delta n e q om N cap w L X F)).sum)| ≤
      rawOutsideHighQInvoice delta e q om N cap w z L X F +
        licensedProducerInvoice delta n e q om N cap w z L X F := by
  let R := ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
        (rawSignedHighQ e q om N cap w L X F)).sum
  let T := ∑ c : Cell,
        ((rawOwnedTrimmed delta e q om N cap w z c).map
          (rawSignedHighQ e q om N cap w L X F)).sum
  let V := ∑ c : Cell,
        ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
          (licensedSignedHighQ delta n e q om N cap w L X F)).sum
  have hraw : |R - T| ≤
      rawOutsideHighQInvoice delta e q om N cap w z L X F := by
    dsimp only [R, T]
    exact abs_raw_highQ_minus_trimmed_le_outside_invoice
      delta e q om N cap w z L X F
  have hchange : |T - V| ≤
      licensedProducerInvoice delta n e q om N cap w z L X F := by
    dsimp only [T, V]
    exact abs_trim_to_licensed_le_producer_invoice
      delta n e q om N cap w z L X F
  change |R - V| ≤
    rawOutsideHighQInvoice delta e q om N cap w z L X F +
      licensedProducerInvoice delta n e q om N cap w z L X F
  calc
    |R - V| = |(R - T) + (T - V)| := by ring
    _ ≤ |R - T| + |T - V| := abs_add _ _
    _ ≤ rawOutsideHighQInvoice delta e q om N cap w z L X F +
        licensedProducerInvoice delta n e q om N cap w z L X F :=
          add_le_add hraw hchange

end
end ImbalancedChen.P4AOriginalFull87ProducerChangeInvoice
