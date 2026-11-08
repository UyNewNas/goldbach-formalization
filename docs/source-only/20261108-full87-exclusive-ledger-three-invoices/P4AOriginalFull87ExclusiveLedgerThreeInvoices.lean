import ImbalancedChen.P4AOriginalFull87MatchedSuffixDisagreement
import ImbalancedChen.P4AOriginalFull87LicensedOutsideThreeInvoices
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The predecessor's real producerLedger matches identical FULL states one copy
at a time.  Here a separately inspectable invoice charges its matched
occurrences by the already PROVED-CANDIDATE actual first-disagreement physical
exclusive-leaf cost, while retaining raw-only/new-only costs unchanged.
The signed value is still the original producerLedger.1; we do not replace
it with a hypothetical signed sum and do not conflate RAW and LICENSED lists.

The three-book full-frontier inequality is then re-established with this
concrete invoice, the actual raw outside invoice and the actual licensed
outside invoice.  No invoice is proved small compared with H_N.
-/

namespace ImbalancedChen.P4AOriginalFull87ExclusiveLedgerThreeInvoices
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87RawTrimSignedHighQ
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ProducerChangeInvoice
open P4AOriginalFull87MatchedSuffixDisagreement
open P4AOriginalFull87LicensedOutsideThreeInvoices

/-- Consume one full-state copy; a second copy is not removed.  This
implementation is local because the original ledger's helper is private. -/
private def consumeOne {α : Type*} [DecidableEq α] (x : α) : List α → List α
  | [] => []
  | y :: ys => if y = x then ys else y :: consumeOne x ys

private theorem consumeOne_sum {α : Type*} [DecidableEq α]
    (x : α) (ys : List α) (g : α → ℝ) (hx : x ∈ ys) :
    (ys.map g).sum = g x + ((consumeOne x ys).map g).sum := by
  induction ys with
  | nil => cases hx
  | cons y ys ih =>
      by_cases h : y = x
      · subst y
        simp [consumeOne]
      · have ht : x ∈ ys := by simpa [h] using hx
        have he := ih ht
        rw [show consumeOne x (y :: ys) = y :: consumeOne x ys by
          simp [consumeOne, h]]
        simp only [List.map_cons, List.sum_cons]
        rw [he]
        ring

private theorem abs_list_sum_le_abs_sum {α : Type*}
    (xs : List α) (f : α → ℝ) :
    |(xs.map f).sum| ≤ (xs.map (fun x => |f x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans
        (add_le_add_left ih |f x|)

/-- This is a COST ONLY, not a second signed ledger. A matched state
pays its actual first-exclusive-leaf physical charge. Every unmatched
raw or licensed copy pays its own full physical signed absolute value.
There is no set conversion and no cancellation of duplicate occurrences. -/
def exclusiveMatchInvoice {α : Type*} [DecidableEq α]
    (f g matched : α → ℝ) : List α → List α → ℝ
  | [], ys => (ys.map (fun y => |g y|)).sum
  | x :: xs, ys =>
      if x ∈ ys then
        matched x + exclusiveMatchInvoice f g matched xs (consumeOne x ys)
      else
        |f x| + exclusiveMatchInvoice f g matched xs ys

/-- The only hypothesis is a LOCAL matched-state inequality.  It is
instantiated below from the actual physical signed first-disagreement
proof, not from a field asserting that the whole invoice is small. -/
private theorem abs_difference_le_exclusive_match_invoice
    {α : Type*} [DecidableEq α]
    (f g matched : α → ℝ)
    (hmatched : ∀ x, |f x - g x| ≤ matched x)
    (xs ys : List α) :
    |(xs.map f).sum - (ys.map g).sum| ≤
      exclusiveMatchInvoice f g matched xs ys := by
  induction xs generalizing ys with
  | nil =>
      simpa [exclusiveMatchInvoice, abs_neg] using
        abs_list_sum_le_abs_sum ys g
  | cons x xs ih =>
      by_cases hx : x ∈ ys
      · have he := consumeOne_sum x ys g hx
        have ht := ih (consumeOne x ys)
        simp only [exclusiveMatchInvoice, if_pos hx,
          List.map_cons, List.sum_cons]
        calc
          |f x + (xs.map f).sum - (ys.map g).sum| =
              |(f x - g x) +
                ((xs.map f).sum - ((consumeOne x ys).map g).sum)| := by
                rw [he]
                ring
          _ ≤ |f x - g x| +
              |(xs.map f).sum - ((consumeOne x ys).map g).sum| :=
                abs_add _ _
          _ ≤ matched x + exclusiveMatchInvoice f g matched xs
              (consumeOne x ys) := add_le_add (hmatched x) ht
      · have ht := ih ys
        simp only [exclusiveMatchInvoice, if_neg hx,
          List.map_cons, List.sum_cons]
        calc
          |f x + (xs.map f).sum - (ys.map g).sum| =
              |f x + ((xs.map f).sum - (ys.map g).sum)| := by ring
          _ ≤ |f x| + |(xs.map f).sum - (ys.map g).sum| :=
                abs_add _ _
          _ ≤ |f x| + exclusiveMatchInvoice f g matched xs ys :=
                add_le_add_left ht |f x|

/-- Only the original owner/strict trim RAW list and the actual licensed
source STATES list can generate the two sides.  The matched charge uses
the actual raw and licensed policies and their same-sign small beta. -/
noncomputable def actualCellExclusiveInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ := by
  classical
  exact exclusiveMatchInvoice
    (rawSignedHighQ e q om N cap w L X F)
    (licensedSignedHighQ delta n e q om N cap w L X F)
    (actualMatchedExclusiveCharge delta n e q om N cap w L X F)
    (rawOwnedTrimmed delta e q om N cap w z c)
    (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)

/-- The PRE-EXISTING signed producerLedger still gives the difference.
Only its matched ABSOLUTE invoice is replaced by the concrete leaf sum.
The bound is not assumed numerically sharper than the old absolute
matched-state difference. -/
theorem actual_cell_ledger_abs_le_exclusive_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) :
    |(actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      actualCellExclusiveInvoice delta n e q om N cap w z L X F c := by
  classical
  unfold actualCellLedger actualCellExclusiveInvoice
  rw [producerLedger_signed]
  exact abs_difference_le_exclusive_match_invoice
    (rawSignedHighQ e q om N cap w L X F)
    (licensedSignedHighQ delta n e q om N cap w L X F)
    (actualMatchedExclusiveCharge delta n e q om N cap w L X F)
    (fun s => abs_actual_matched_difference_le_exclusive_charge
      delta n e q om N cap w L X F s)
    (rawOwnedTrimmed delta e q om N cap w z c)
    (states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c)

/-- Keep all 87 original cells, with all source state multiplicities. -/
def actualProducerExclusiveInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ c : Cell,
    actualCellExclusiveInvoice delta n e q om N cap w z L X F c

theorem abs_actual_cell_ledger_sum_le_exclusive_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |∑ c : Cell,
      (actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      actualProducerExclusiveInvoice delta n e q om N cap w z L X F := by
  classical
  unfold actualProducerExclusiveInvoice
  calc
    |∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      ∑ c : Cell,
        |(actualCellLedger delta n e q om N cap w z L X F c).1| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell,
          actualCellExclusiveInvoice delta n e q om N cap w z L X F c := by
      apply Finset.sum_le_sum
      intro c _
      exact actual_cell_ledger_abs_le_exclusive_invoice
        delta n e q om N cap w z L X F c

/-- Fully physical RAW vs fully physical LICENSED finite difference,
now charged by three explicit independent sources:
  (1) raw unowned/trim-omitted,
  (2) matched first-exclusive leaves + raw/new unmatched copies,
  (3) licensed unowned/trim-omitted.
The signed conservation is the ORIGINAL prior theorem, not a new rho.
No H_N limit, cancellation improvement or positive gain is asserted. -/
theorem abs_raw_full_minus_licensed_full_le_exclusive_three_invoices
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
        (rawSignedHighQ e q om N cap w L X F)).sum -
      ((licensedFrontier delta n e q om N cap w z).map
        (licensedSignedHighQ delta n e q om N cap w L X F)).sum| ≤
      (rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerExclusiveInvoice delta n e q om N cap w z L X F) +
      licensedOutsideHighQInvoice delta n e q om N cap w z L X F := by
  let R := ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
    (rawSignedHighQ e q om N cap w L X F)).sum
  let T := ∑ c : Cell,
    ((rawOwnedTrimmed delta e q om N cap w z c).map
      (rawSignedHighQ e q om N cap w L X F)).sum
  let V := ∑ c : Cell,
    ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
      (licensedSignedHighQ delta n e q om N cap w L X F)).sum
  let B := ((licensedFrontier delta n e q om N cap w z).map
    (licensedSignedHighQ delta n e q om N cap w L X F)).sum
  have hr : |R - T| ≤
      rawOutsideHighQInvoice delta e q om N cap w z L X F := by
    dsimp only [R, T]
    exact abs_raw_highQ_minus_trimmed_le_outside_invoice
      delta e q om N cap w z L X F
  have hm : |T - V| ≤
      actualProducerExclusiveInvoice delta n e q om N cap w z L X F := by
    have hd : T - V = ∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1 := by
      dsimp only [T, V]
      exact actual_trim_to_licensed_signed_eq_ledger
        delta n e q om N cap w z L X F
    rw [hd]
    exact abs_actual_cell_ledger_sum_le_exclusive_invoice
      delta n e q om N cap w z L X F
  have hl : |V - B| ≤
      licensedOutsideHighQInvoice delta n e q om N cap w z L X F := by
    dsimp only [V, B]
    rw [abs_sub_comm]
    exact abs_licensed_full_minus_owned_le_outside_invoice
      delta n e q om N cap w z L X F
  change |R - B| ≤
    (rawOutsideHighQInvoice delta e q om N cap w z L X F +
      actualProducerExclusiveInvoice delta n e q om N cap w z L X F) +
    licensedOutsideHighQInvoice delta n e q om N cap w z L X F
  calc
    |R - B| = |((R - T) + (T - V)) + (V - B)| := by ring
    _ ≤ (|R - T| + |T - V|) + |V - B| := by
      calc
        |((R - T) + (T - V)) + (V - B)| ≤
            |(R - T) + (T - V)| + |V - B| := abs_add _ _
        _ ≤ (|R - T| + |T - V|) + |V - B| :=
          add_le_add_right (abs_add _ _) _
    _ ≤ (rawOutsideHighQInvoice delta e q om N cap w z L X F +
          actualProducerExclusiveInvoice delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F :=
          add_le_add (add_le_add hr hm) hl

end
end ImbalancedChen.P4AOriginalFull87ExclusiveLedgerThreeInvoices
