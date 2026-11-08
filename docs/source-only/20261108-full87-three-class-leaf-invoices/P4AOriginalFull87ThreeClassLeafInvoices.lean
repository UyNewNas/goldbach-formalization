import ImbalancedChen.P4AOriginalFull87UnmatchedPhysicalLeaves
import ImbalancedChen.P4AOriginalFull87LicensedOutsideThreeInvoices
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
The genuine raw and licensed producers have DIFFERENT complete-state lists.
The previous signed three-class leaf decomposition is now bounded by a
literal per-retained-leaf full-q absolute charge for each of its three
disjoint classes: matched FIRST-EXCLUSIVE, raw-only ORIGINAL, licensed-only
LICENSED.  These are costs, not a second signed saving definition.
The full frontiers add their two existing unowned/strict-omitted invoices
EXACTLY ONCE.  No claim of o(H_N) or saved87 replay is made.
-/

namespace ImbalancedChen.P4AOriginalFull87ThreeClassLeafInvoices
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87UnmatchedPhysicalLeaves
  (actualCellCopies actualCellSignedLeafBalance
   actual_cell_ledger_eq_signed_leaf_balance
   rawRetainedLeaves licensedRetainedLeaves
   raw_signed_highQ_eq_leaf_sum licensed_signed_highQ_eq_leaf_sum)
open P4AOriginalFull87MatchedSuffixDisagreement
  (actualMatchedExclusiveLeaves actualMatchedExclusiveCharge
   actual_matched_signed_difference_eq_exclusive
   abs_actual_matched_difference_le_exclusive_charge)
open P4AOriginalFull87ExclusiveLeafSignedCut (taggedHighQTerm exclusiveLeafCost)
open P4AOriginalFull87PhysicalHighQOwnedInvoice
  (leafHighQTerm leafHighQCharge abs_leaf_high_q_term_le_charge)
open P4AOriginalFull87RawTrimSignedHighQ
  (rawSignedHighQ rawOutsideHighQInvoice rawOwnedTrimmed
   abs_raw_highQ_minus_trimmed_le_outside_invoice)
open P4AOriginalFull87ProducerChangeInvoice
  (licensedSignedHighQ actualCellLedger actual_trim_to_licensed_signed_eq_ledger)
open P4AOriginalFull87LicensedOutsideThreeInvoices
  (licensedFrontier licensedOutsideHighQInvoice
   abs_licensed_full_minus_owned_le_outside_invoice)
open P4AOriginalFull87RawOwnerPartition (actualRawFrontier)
open P4AOriginalFull87LicensedSixthRealization (states)

/-- The only finite estimate used for a List: occurrence multiplicity is
not removed, and there is no independence or monotonicity assumption. -/
private theorem abs_list_map_le_charge {α : Type*} (xs : List α)
    (f charge : α → ℝ) (h : ∀ x, |f x| ≤ charge x) :
    |(xs.map f).sum| ≤ (xs.map charge).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (abs_add _ _).trans (add_le_add (h x) ih)

/-- Raw-only states still have their ORIGINAL retained source leaves,
including the sign-dependent small Rosser beta and strict full q. -/
theorem raw_only_abs_le_actual_leaf_charge
    (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) :
    |rawSignedHighQ e q om N cap w L X F s| ≤
      ((rawRetainedLeaves e q om N s).map
        (leafHighQCharge N cap w L X F)).sum := by
  rw [raw_signed_highQ_eq_leaf_sum]
  exact abs_list_map_le_charge
    (rawRetainedLeaves e q om N s)
    (leafHighQTerm N cap w L X F)
    (leafHighQCharge N cap w L X F)
    (fun leaf => abs_leaf_high_q_term_le_charge N cap w L X F leaf)

/-- Licensed-only states use only the LICENSED policy's own leaves. -/
theorem licensed_only_abs_le_actual_leaf_charge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) :
    |licensedSignedHighQ delta n e q om N cap w L X F s| ≤
      ((licensedRetainedLeaves delta n e q om N s).map
        (leafHighQCharge N cap w L X F)).sum := by
  rw [licensed_signed_highQ_eq_leaf_sum]
  exact abs_list_map_le_charge
    (licensedRetainedLeaves delta n e q om N s)
    (leafHighQTerm N cap w L X F)
    (leafHighQCharge N cap w L X F)
    (fun leaf => abs_leaf_high_q_term_le_charge N cap w L X F leaf)

/-- Matched copies are invoiced exclusively on first-divergence leaves,
never on both whole suffixes and never on an unrelated inherited mask. -/
def actualCellMatchedLeafBill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  (((actualCellCopies delta n e q om N cap w z c).1).map
    (actualMatchedExclusiveCharge delta n e q om N cap w L X F)).sum

/-- A raw-only full-state occurrence is paid using the actual raw
first-exit retained LEAVES, not the absolute sum of an unexpanded suffix. -/
def actualCellRawOnlyLeafBill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  (((actualCellCopies delta n e q om N cap w z c).2.1).map
    (fun s => ((rawRetainedLeaves e q om N s).map
      (leafHighQCharge N cap w L X F)).sum)).sum

/-- A licensed-only full-state occurrence is paid using a separately
enumerated LICENSED retained leaf list. -/
def actualCellLicensedOnlyLeafBill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  (((actualCellCopies delta n e q om N cap w z c).2.2).map
    (fun s => ((licensedRetainedLeaves delta n e q om N s).map
      (leafHighQCharge N cap w L X F)).sum)).sum

/-- The middle (producer-change) invoice, deliberately separate from
both producers' already-defined outside/strict-trim invoices. -/
def actualCellThreeClassLeafBill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  (actualCellMatchedLeafBill delta n e q om N cap w z L X F c +
   actualCellRawOnlyLeafBill delta n e q om N cap w z L X F c) +
   actualCellLicensedOnlyLeafBill delta n e q om N cap w z L X F c

/-- Actual existing signed three-class balance bounded by the three
DIFFERENT physical retained-leaf invoices. No occurrence is in two of
these three classes, and no signed-saving monotonicity is invoked. -/
theorem abs_actual_cell_signed_balance_le_three_class_leaf_bill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) :
    |actualCellSignedLeafBalance delta n e q om N cap w z L X F c| ≤
      actualCellThreeClassLeafBill delta n e q om N cap w z L X F c := by
  let copies := actualCellCopies delta n e q om N cap w z c
  let matched : FirstExitDepthState ℕ → ℝ := fun s =>
    ((actualMatchedExclusiveLeaves delta n e q om N s).map
      (taggedHighQTerm N cap w L X F)).sum
  let raw : FirstExitDepthState ℕ → ℝ := fun s =>
    ((rawRetainedLeaves e q om N s).map
      (leafHighQTerm N cap w L X F)).sum
  let licensed : FirstExitDepthState ℕ → ℝ := fun s =>
    ((licensedRetainedLeaves delta n e q om N s).map
      (leafHighQTerm N cap w L X F)).sum
  let matchCost : FirstExitDepthState ℕ → ℝ :=
    actualMatchedExclusiveCharge delta n e q om N cap w L X F
  let rawCost : FirstExitDepthState ℕ → ℝ := fun s =>
    ((rawRetainedLeaves e q om N s).map
      (leafHighQCharge N cap w L X F)).sum
  let licensedCost : FirstExitDepthState ℕ → ℝ := fun s =>
    ((licensedRetainedLeaves delta n e q om N s).map
      (leafHighQCharge N cap w L X F)).sum
  have hm (s : FirstExitDepthState ℕ) : |matched s| ≤ matchCost s := by
    dsimp only [matched, matchCost]
    have hs := abs_actual_matched_difference_le_exclusive_charge
      delta n e q om N cap w L X F s
    rw [actual_matched_signed_difference_eq_exclusive] at hs
    exact hs
  have hr (s : FirstExitDepthState ℕ) : |raw s| ≤ rawCost s := by
    dsimp only [raw, rawCost]
    exact abs_list_map_le_charge
      (rawRetainedLeaves e q om N s)
      (leafHighQTerm N cap w L X F)
      (leafHighQCharge N cap w L X F)
      (fun leaf => abs_leaf_high_q_term_le_charge N cap w L X F leaf)
  have hl (s : FirstExitDepthState ℕ) :
      |licensed s| ≤ licensedCost s := by
    dsimp only [licensed, licensedCost]
    exact abs_list_map_le_charge
      (licensedRetainedLeaves delta n e q om N s)
      (leafHighQTerm N cap w L X F)
      (leafHighQCharge N cap w L X F)
      (fun leaf => abs_leaf_high_q_term_le_charge N cap w L X F leaf)
  have hM := abs_list_map_le_charge copies.1 matched matchCost hm
  have hR := abs_list_map_le_charge copies.2.1 raw rawCost hr
  have hL := abs_list_map_le_charge copies.2.2 licensed licensedCost hl
  change |(copies.1.map matched).sum +
      (copies.2.1.map raw).sum - (copies.2.2.map licensed).sum| ≤
    ((copies.1.map matchCost).sum + (copies.2.1.map rawCost).sum) +
      (copies.2.2.map licensedCost).sum
  calc
    |(copies.1.map matched).sum +
        (copies.2.1.map raw).sum - (copies.2.2.map licensed).sum| ≤
      (|(copies.1.map matched).sum| + |(copies.2.1.map raw).sum|) +
        |(copies.2.2.map licensed).sum| := by
          calc
            |(copies.1.map matched).sum +
                (copies.2.1.map raw).sum -
                (copies.2.2.map licensed).sum| ≤
              |(copies.1.map matched).sum +
                (copies.2.1.map raw).sum| +
                |(copies.2.2.map licensed).sum| := by
                  simpa only [sub_eq_add_neg, abs_neg] using
                    (abs_add
                      ((copies.1.map matched).sum +
                        (copies.2.1.map raw).sum)
                      (-(copies.2.2.map licensed).sum))
            _ ≤ (|(copies.1.map matched).sum| +
                   |(copies.2.1.map raw).sum|) +
                  |(copies.2.2.map licensed).sum| :=
                    add_le_add_right (abs_add _ _) _
    _ ≤ ((copies.1.map matchCost).sum +
           (copies.2.1.map rawCost).sum) +
          (copies.2.2.map licensedCost).sum :=
            add_le_add (add_le_add hM hR) hL

theorem abs_actual_cell_ledger_le_three_class_leaf_bill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) :
    |(actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      actualCellThreeClassLeafBill delta n e q om N cap w z L X F c := by
  rw [actual_cell_ledger_eq_signed_leaf_balance]
  exact abs_actual_cell_signed_balance_le_three_class_leaf_bill
    delta n e q om N cap w z L X F c

/-- All original 87 Cells retained; no replacement by archive label sums. -/
def actualProducerThreeClassLeafBill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ c : Cell,
    actualCellThreeClassLeafBill delta n e q om N cap w z L X F c

theorem abs_owned87_ledger_le_three_class_leaf_bill
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |∑ c : Cell,
      (actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      actualProducerThreeClassLeafBill delta n e q om N cap w z L X F := by
  classical
  unfold actualProducerThreeClassLeafBill
  calc
    |∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1| ≤
      ∑ c : Cell,
        |(actualCellLedger delta n e q om N cap w z L X F c).1| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell,
        actualCellThreeClassLeafBill delta n e q om N cap w z L X F c := by
          apply Finset.sum_le_sum
          intro c _
          exact abs_actual_cell_ledger_le_three_class_leaf_bill
            delta n e q om N cap w z L X F c

/-- Two OUTSIDE books + one literal three-class physical producer bill.
The previous raw/full and licensed/full frontiers are NOT identified.
Every outside/strict-omitted occurrence is charged exactly once, with
the middle invoice covering only originally owned and strictly retained
producer states. No rho, H_N, PP, saved87 or numeric smallness asserted. -/
theorem abs_full_raw_minus_full_licensed_le_five_source_books
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
       (rawSignedHighQ e q om N cap w L X F)).sum -
      ((licensedFrontier delta n e q om N cap w z).map
       (licensedSignedHighQ delta n e q om N cap w L X F)).sum| ≤
      (rawOutsideHighQInvoice delta e q om N cap w z L X F +
        actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
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
      actualProducerThreeClassLeafBill delta n e q om N cap w z L X F := by
    have hd : T - V = ∑ c : Cell,
        (actualCellLedger delta n e q om N cap w z L X F c).1 := by
      dsimp only [T, V]
      exact actual_trim_to_licensed_signed_eq_ledger
        delta n e q om N cap w z L X F
    rw [hd]
    exact abs_owned87_ledger_le_three_class_leaf_bill
      delta n e q om N cap w z L X F
  have hl : |V - B| ≤
      licensedOutsideHighQInvoice delta n e q om N cap w z L X F := by
    dsimp only [V, B]
    rw [abs_sub_comm]
    exact abs_licensed_full_minus_owned_le_outside_invoice
      delta n e q om N cap w z L X F
  change |R - B| ≤
    (rawOutsideHighQInvoice delta e q om N cap w z L X F +
      actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
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
          actualProducerThreeClassLeafBill delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F :=
          add_le_add (add_le_add hr hm) hl

end
end ImbalancedChen.P4AOriginalFull87ThreeClassLeafInvoices
