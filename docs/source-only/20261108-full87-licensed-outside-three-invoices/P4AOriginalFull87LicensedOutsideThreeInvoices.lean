import ImbalancedChen.P4AOriginalFull87ProducerChangeInvoice
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The ACTUAL licensed-sixth/eighth rank-eight predecessor is a different
List from the complete-sixth raw predecessor.  This packet partitions
that new List by the ORIGINAL affine owner and ORIGINAL strict trim,
without deleting unowned or trimmed-out occurrences.

It then joins (i) raw outside, (ii) once-matched producer change, and
(iii) licensed outside in a single signed conservation identity and
three separately audited absolute invoices.  Every occurrence retains
its original state, sign, mass, remaining carrier, beta attachment,
and STRICT full physical modulus test.  No H_N payment is asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87LicensedOutsideThreeInvoices
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87RawOwnerPartition
open P4AOriginalFull87RawTrimSignedHighQ
open P4AOriginalFull87ProducerChangeInvoice

/-- The actual NEW rank-eight frontier: the licensed sixth producer
through its own eighth splice, with unit original-prime weights.
This is not the complete-sixth raw frontier. -/
def licensedFrontier (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) :
    List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 8
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    (fun _ : ℕ => (1 : ℝ)) [] true 1
    (roughPrimeUniverse N cap w z)

/-- At rank eight the eighth splice has not changed the actual new
predecessor List.  This does not identify it with the RAW sixth List. -/
theorem licensedFrontier_eq_new_sixth (delta : ℝ) (n : ℕ)
    (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (w z : ℝ) :
    licensedFrontier delta n e q om N cap w z =
      P4AOriginalFull87OwnedEighthSource.frontier n e q om N cap w z := by
  simpa only [licensedFrontier, P4AOriginalFull87OwnedEighthSource.frontier]
    using P4AOriginalFull87LicensedSixthPolicy.frontier_eq_new_sixth
      delta n e q om (N : ℝ) (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1

/-- New producer occurrences outside EVERY original Cell. -/
def licensedUnowned (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) :
    List (FirstExitDepthState ℕ) :=
  (licensedFrontier delta n e q om N cap w z).filter
    (fun s => decide (ownerAtPrefix (N : ℝ) s.selectedPrefix = none))

/-- New producer occurrences owned by one original Cell before trim. -/
def licensedOwned (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (licensedFrontier delta n e q om N cap w z).filter
    (fun s => decide (ownerAtPrefix (N : ℝ) s.selectedPrefix = some c))

/-- This is the LICENSED producer's genuine owned-but-omitted List,
not the same-named RAW complement and not a geometric null claim. -/
def licensedOwnedTrimOmitted (delta : ℝ) (n : ℕ) (e : ℚ)
    (q : ℕ) (om : ℝ) (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (licensedOwned delta n e q om N cap w z c).filter
    (fun s => decide
      (¬ point8 (N : ℝ) s.selectedPrefix ∈ trim c delta))

/-- A single List filter by two simultaneous predicates. -/
private theorem filter_filter_and {α : Type*}
    (xs : List α) (p q : α → Prop) :
    ((xs.filter (fun x => decide (p x))).filter
      (fun x => decide (q x))) =
      xs.filter (fun x => decide (p x ∧ q x)) := by
  classical
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      by_cases hp : p x <;> by_cases hq : q x <;>
        simp [List.filter_cons, hp, hq, ih]

/-- Split one occurrence List by a finite partial owner. The full
list sum is retained, including owner=none and repeated occurrences. -/
private theorem option_owner_sum {α κ : Type*} [Fintype κ]
    [DecidableEq κ] (owner : α → Option κ) (v : α → ℝ)
    (xs : List α) :
    (xs.map v).sum =
      ((xs.filter (fun x => decide (owner x = none))).map v).sum +
      ∑ c : κ,
        ((xs.filter (fun x => decide (owner x = some c))).map v).sum := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hn :
          (((x :: xs).filter (fun y => decide (owner y = none))).map v).sum =
            (if owner x = none then v x else 0) +
              ((xs.filter (fun y => decide (owner y = none))).map v).sum := by
        by_cases h : owner x = none <;> simp [List.filter_cons, h]
      have hc (c : κ) :
          (((x :: xs).filter (fun y => decide (owner y = some c))).map v).sum =
            (if owner x = some c then v x else 0) +
              ((xs.filter (fun y => decide (owner y = some c))).map v).sum := by
        by_cases h : owner x = some c <;> simp [List.filter_cons, h]
      have hs :
          (∑ c : κ,
            (((x :: xs).filter (fun y => decide (owner y = some c))).map v).sum) =
          (∑ c : κ, if owner x = some c then v x else 0) +
            (∑ c : κ,
              ((xs.filter (fun y => decide (owner y = some c))).map v).sum) := by
        simp_rw [hc]
        rw [Finset.sum_add_distrib]
      have hone :
          (if owner x = none then v x else 0) +
            (∑ c : κ, if owner x = some c then v x else 0) = v x := by
        cases ho : owner x with
        | none => simp [ho]
        | some c => simp [ho]
      calc
        ((x :: xs).map v).sum = v x + (xs.map v).sum := rfl
        _ = v x +
              (((xs.filter (fun y => decide (owner y = none))).map v).sum +
                ∑ c : κ,
                  ((xs.filter (fun y => decide (owner y = some c))).map v).sum) := by
              rw [ih]
        _ = (((x :: xs).filter (fun y => decide (owner y = none))).map v).sum +
              ∑ c : κ,
                (((x :: xs).filter (fun y => decide (owner y = some c))).map v).sum := by
              rw [hn, hs]
              linear_combination -hone

/-- Keep and omit are complementary ACTUAL predicates, even if a
state occurs several times with opposite signed continuation values. -/
private theorem filter_complement_sum {α : Type*}
    (xs : List α) (p : α → Prop) (v : α → ℝ) :
    (xs.map v).sum =
      ((xs.filter (fun x => decide (p x))).map v).sum +
        ((xs.filter (fun x => decide (¬ p x))).map v).sum := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : p x
      · simp [List.filter_cons, hx, ih]
        ring
      · simp [List.filter_cons, hx, ih]
        ring

/-- The existing licensed policy's physical 'states' list is EXACTLY
the original owner fibre subjected to original strict trim, without
reconstructing it from archive indices or forcing an old producer. -/
theorem actual_states_eq_licensed_owned_trim
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) (c : Cell) :
    states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c =
      (licensedOwned delta n e q om N cap w z c).filter
        (fun s => decide
          (point8 (N : ℝ) s.selectedPrefix ∈ trim c delta)) := by
  rw [filter_filter_and]
  rfl

/-- No assumed equivalence of producer Lists: one actual new owner
fibre is exactly its licensed states plus strict-trim omission. -/
theorem licensed_owned_kept_omitted_sum
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z : ℝ) (c : Cell)
    (v : FirstExitDepthState ℕ → ℝ) :
    ((licensedOwned delta n e q om N cap w z c).map v).sum =
      ((states delta n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c).map v).sum +
      ((licensedOwnedTrimOmitted delta n e q om N cap w z c).map v).sum := by
  classical
  have h := filter_complement_sum
    (licensedOwned delta n e q om N cap w z c)
    (fun s => point8 (N : ℝ) s.selectedPrefix ∈ trim c delta) v
  rw [← actual_states_eq_licensed_owned_trim] at h
  exact h

/-- The full NEW licensed frontier has three mutually exclusive
accounting families: unowned, licensed retained, licensed omitted.
The state List may contain duplicates, which are never deduplicated. -/
theorem licensed_frontier_three_way_sum
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (v : FirstExitDepthState ℕ → ℝ) :
    ((licensedFrontier delta n e q om N cap w z).map v).sum =
      ((licensedUnowned delta n e q om N cap w z).map v).sum +
      (∑ c : Cell,
        ((states delta n e q om N cap w z
          (fun _ : ℕ => (1 : ℝ)) c).map v).sum) +
      (∑ c : Cell,
        ((licensedOwnedTrimOmitted delta n e q om N cap w z c).map v).sum) := by
  have howner := option_owner_sum
    (fun s : FirstExitDepthState ℕ => ownerAtPrefix (N : ℝ) s.selectedPrefix)
    v (licensedFrontier delta n e q om N cap w z)
  have htrim :
      (∑ c : Cell,
        ((licensedOwned delta n e q om N cap w z c).map v).sum) =
      (∑ c : Cell,
        ((states delta n e q om N cap w z
          (fun _ : ℕ => (1 : ℝ)) c).map v).sum) +
      (∑ c : Cell,
        ((licensedOwnedTrimOmitted delta n e q om N cap w z c).map v).sum) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    exact licensed_owned_kept_omitted_sum delta n e q om N cap w z c v
  change ((licensedFrontier delta n e q om N cap w z).map v).sum =
      ((licensedUnowned delta n e q om N cap w z).map v).sum +
        (∑ c : Cell,
          ((licensedOwned delta n e q om N cap w z c).map v).sum) at howner
  rw [howner, htrim]
  ring

/-- Keep the REAL licensed signed ordinary continuation, with its own
sixth parent and eighth cap, the actual beta factors and full q.
No positive saving is inferred from this definition. -/
def licensedOutsideSigned
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((licensedUnowned delta n e q om N cap w z).map
    (licensedSignedHighQ delta n e q om N cap w L X F)).sum +
  ∑ c : Cell,
    ((licensedOwnedTrimOmitted delta n e q om N cap w z c).map
      (licensedSignedHighQ delta n e q om N cap w L X F)).sum

def licensedOutsideHighQInvoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((licensedUnowned delta n e q om N cap w z).map
    (fun s => |licensedSignedHighQ delta n e q om N cap w L X F s|)).sum +
  ∑ c : Cell,
    ((licensedOwnedTrimOmitted delta n e q om N cap w z c).map
      (fun s => |licensedSignedHighQ delta n e q om N cap w L X F s|)).sum

theorem licensed_full_signed_eq_owned_plus_outside
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    ((licensedFrontier delta n e q om N cap w z).map
      (licensedSignedHighQ delta n e q om N cap w L X F)).sum =
      (∑ c : Cell,
        ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
          (licensedSignedHighQ delta n e q om N cap w L X F)).sum) +
        licensedOutsideSigned delta n e q om N cap w z L X F := by
  have h := licensed_frontier_three_way_sum delta n e q om N cap w z
    (licensedSignedHighQ delta n e q om N cap w L X F)
  unfold licensedOutsideSigned
  linarith

private theorem abs_list_sum_le_abs_map {α : Type*}
    (xs : List α) (v : α → ℝ) :
    |(xs.map v).sum| ≤ (xs.map (fun x => |v x|)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simpa only [List.map_cons, List.sum_cons] using
        (abs_add (v x) ((xs.map v).sum)).trans
          (add_le_add_left ih |v x|)

/-- LICENSED outside is separately charged; no raw outside entry
is silently reused and no missing term is discarded as null geometry. -/
theorem abs_licensed_full_minus_owned_le_outside_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |((licensedFrontier delta n e q om N cap w z).map
       (licensedSignedHighQ delta n e q om N cap w L X F)).sum -
      (∑ c : Cell,
        ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
          (licensedSignedHighQ delta n e q om N cap w L X F)).sum)| ≤
      licensedOutsideHighQInvoice delta n e q om N cap w z L X F := by
  let v := licensedSignedHighQ delta n e q om N cap w L X F
  let U := licensedUnowned delta n e q om N cap w z
  let E := fun c : Cell => licensedOwnedTrimOmitted delta n e q om N cap w z c
  have hs := licensed_frontier_three_way_sum delta n e q om N cap w z v
  have hrewrite :
      ((licensedFrontier delta n e q om N cap w z).map v).sum -
        (∑ c : Cell,
          ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map v).sum) =
      (U.map v).sum + ∑ c : Cell, ((E c).map v).sum := by
    dsimp only [U, E]
    linarith
  rw [hrewrite]
  unfold licensedOutsideHighQInvoice
  change |(U.map v).sum + ∑ c : Cell, ((E c).map v).sum| ≤
    (U.map (fun s => |v s|)).sum +
      ∑ c : Cell, ((E c).map (fun s => |v s|)).sum
  calc
    |(U.map v).sum + ∑ c : Cell, ((E c).map v).sum| ≤
        |(U.map v).sum| + |∑ c : Cell, ((E c).map v).sum| := abs_add _ _
    _ ≤ (U.map (fun s => |v s|)).sum +
        ∑ c : Cell, ((E c).map (fun s => |v s|)).sum := by
      apply add_le_add (abs_list_sum_le_abs_map U v)
      calc
        |∑ c : Cell, ((E c).map v).sum| ≤
          ∑ c : Cell, |((E c).map v).sum| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ c : Cell, ((E c).map (fun s => |v s|)).sum := by
          apply Finset.sum_le_sum
          intro c _
          exact abs_list_sum_le_abs_map (E c) v

/-- The old signed outside mass uses exactly the ORIGINAL producer's
unowned and trimmed-out occurrence lists, once each. -/
def rawOutsideSigned
    (delta : ℝ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((actualUnownedFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
    (rawSignedHighQ e q om N cap w L X F)).sum +
  ∑ c : Cell,
    ((rawOwnedTrimOmitted delta e q om N cap w z c).map
      (rawSignedHighQ e q om N cap w L X F)).sum

/-- FULL raw minus FULL licensed conservation. The matched part is the
genuine per-original-Cell producer ledger; outside terms keep BOTH
different producers. It is never a statement of positive saving. -/
theorem raw_minus_full_licensed_signed_eq_three_books
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
      (rawSignedHighQ e q om N cap w L X F)).sum -
    ((licensedFrontier delta n e q om N cap w z).map
      (licensedSignedHighQ delta n e q om N cap w L X F)).sum =
    rawOutsideSigned delta e q om N cap w z L X F +
    (∑ c : Cell, (actualCellLedger delta n e q om N cap w z L X F c).1) -
    licensedOutsideSigned delta n e q om N cap w z L X F := by
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
  let D := ∑ c : Cell,
    (actualCellLedger delta n e q om N cap w z L X F c).1
  let U := rawOutsideSigned delta e q om N cap w z L X F
  let W := licensedOutsideSigned delta n e q om N cap w z L X F
  have hr : R = U + T := by
    dsimp only [R, U, T]
    have h := actual_raw_highQ_unowned_trim_omitted
      delta e q om N cap w z L X F
    linarith
  have hl : B = V + W := by
    dsimp only [B, V, W]
    exact licensed_full_signed_eq_owned_plus_outside
      delta n e q om N cap w z L X F
  have hd : T - V = D := by
    dsimp only [T, V, D]
    exact actual_trim_to_licensed_signed_eq_ledger
      delta n e q om N cap w z L X F
  change R - B = U + D - W
  linarith

/-- The three charges are disjoint:
  1. original raw unowned/strict-omitted;
  2. actual matched/unmatched owner producer change;
  3. NEW licensed unowned/strict-omitted.
No individual occurrence is paid twice by these classifications.
No asymptotic H_N bound is inferred from this finite inequality. -/
theorem abs_raw_to_full_licensed_le_three_invoices
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
       (rawSignedHighQ e q om N cap w L X F)).sum -
      ((licensedFrontier delta n e q om N cap w z).map
       (licensedSignedHighQ delta n e q om N cap w L X F)).sum| ≤
      (rawOutsideHighQInvoice delta e q om N cap w z L X F +
        licensedProducerInvoice delta n e q om N cap w z L X F) +
      licensedOutsideHighQInvoice delta n e q om N cap w z L X F := by
  let R := ((actualRawFrontier e q om N cap w z (fun _ : ℕ => (1 : ℝ))).map
    (rawSignedHighQ e q om N cap w L X F)).sum
  let V := ∑ c : Cell,
    ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
      (licensedSignedHighQ delta n e q om N cap w L X F)).sum
  let B := ((licensedFrontier delta n e q om N cap w z).map
    (licensedSignedHighQ delta n e q om N cap w L X F)).sum
  have hprior : |R - V| ≤
      rawOutsideHighQInvoice delta e q om N cap w z L X F +
        licensedProducerInvoice delta n e q om N cap w z L X F := by
    dsimp only [R, V]
    exact abs_raw_to_actual_licensed_owned_le_separate_invoices
      delta n e q om N cap w z L X F
  have hnew : |V - B| ≤
      licensedOutsideHighQInvoice delta n e q om N cap w z L X F := by
    dsimp only [V, B]
    rw [abs_sub_comm]
    exact abs_licensed_full_minus_owned_le_outside_invoice
      delta n e q om N cap w z L X F
  change |R - B| ≤
    (rawOutsideHighQInvoice delta e q om N cap w z L X F +
      licensedProducerInvoice delta n e q om N cap w z L X F) +
    licensedOutsideHighQInvoice delta n e q om N cap w z L X F
  calc
    |R - B| = |(R - V) + (V - B)| := by ring
    _ ≤ |R - V| + |V - B| := abs_add _ _
    _ ≤ (rawOutsideHighQInvoice delta e q om N cap w z L X F +
          licensedProducerInvoice delta n e q om N cap w z L X F) +
        licensedOutsideHighQInvoice delta n e q om N cap w z L X F :=
          add_le_add hprior hnew

end
end ImbalancedChen.P4AOriginalFull87LicensedOutsideThreeInvoices
