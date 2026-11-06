import ImbalancedChen.P4AOriginalFull87ArithmeticTerminalBridge
import ImbalancedChen.P4AOriginalFull87SignedDeletionLedger
import ImbalancedChen.P4AOriginalFull87FailedAttempts
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4, continuation of the genuine full-q arithmetic/terminal bridge:
split BOTH physical first-exit corrections at the SAME actual eighth
state into true rank-nine rejected attempts and later odd rejected
attempts, preserving each signed occurrence and its unprocessed suffix.

A rank-nine attempt is defined using the complement of the later rank
filter. The proof below uses the genuine first-exit history to show
that every such occurrence has older.length = 8; this is NOT an
assumption smuggled into a synthetic event type.

Finally, connect this exact split to the original arithmetic source:
the original terminal mismatch stays an explicit UNPAID invoice and
the later target-prime deletion comparison is charged ONCE for each
of the two real policies. The rank-nine inherited-square part is
NOT estimated here. No external number theory is proved or assumed.
-/

namespace ImbalancedChen.P4AOriginalFull87CorrectionRankTerminal
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt correction_eq_failed_attempt_sum
    owned87_failed_attempt_actual_source)
open P4AOriginalFull87SignedDeletionLedger
  (physicalFailedAt physical_failed_has_unit_key
    physicalLaterSigned ownedPhysicalLaterSigned
    ownedAdjustedLaterSigned ownedLaterAbsoluteBudget
    owned87_later_physical_signed_deletion_ledger)
open P4AOriginalFull87ArithmeticTerminalBridge
  (correctionGapAt ownedCorrectionGap
    ownedTerminalMismatchGap ownedTerminalMismatchCost
    ownedSource_sub_correction_abs_le_terminalCost
    physical_saving_eq_correction_plus_terminalMismatch)
open P4AOriginalFull87OwnedEighthSource (ownedSource)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87LicensedSixthPolicy

/-- The complementary part of the LITERAL rejected-attempt list.
Its rank-nine interpretation is proved below for genuine owned states. -/
def rankNinePhysicalFailedAt
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    List (FirstExitRejectedAttempt ℕ) :=
  (physicalFailedAt n e q om N c s useParent).filter
    (fun a => decide (a.older.length ≤ 8))

def rankNineSigned
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) : ℝ :=
  ((rankNinePhysicalFailedAt n e q om N c s useParent).map
    (FirstExitRejectedAttempt.value halfProductDensity)).sum

/-- Every actual physical failure has all eight historical primes in
its older word. The proof transfers ONLY the occurrence key to the
already-proved unit-weight valid selection, never its physical mass. -/
theorem physical_failed_older_length_ge_eight
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ physicalFailedAt n e q om N c s useParent) :
    8 ≤ a.older.length := by
  obtain ⟨b, hb, hOlder, _, _, _⟩ :=
    physical_failed_has_unit_key n e q om N c s useParent a ha
  obtain ⟨before, chosen, _, _, _, _, _, _, hRank, _, _⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent b hb
  rw [hOlder] at hRank
  omega

/-- Thus the complementary branch is EXACTLY rank nine at any genuine
owned original87 state, not an arbitrary "early" error catchall. -/
theorem rankNinePhysicalFailedAt_actual_rank
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ rankNinePhysicalFailedAt n e q om N c s useParent) :
    a.older.length = 8 := by
  have hmem := ha
  unfold rankNinePhysicalFailedAt at hmem
  obtain ⟨hphysical, hdec⟩ := List.mem_filter.mp hmem
  have hle : a.older.length ≤ 8 := of_decide_eq_true hdec
  have hge := physical_failed_older_length_ge_eight
    delta n e q om N cap w z c s hs useParent a hphysical
  omega

/-- List partition identity: no Finset and no occurrence deduplication.
The two exact tests are logical complements even for a general list. -/
private theorem sum_split_at_eight {α : Type*}
    (xs : List α) (depth : α → ℕ) (v : α → ℝ) :
    (xs.map v).sum =
      ((xs.filter (fun x => decide (depth x ≤ 8))).map v).sum +
      ((xs.filter (fun x => decide (8 < depth x))).map v).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : depth x ≤ 8
      · have hy : ¬ 8 < depth x := by omega
        simp [hx, hy, ih, add_assoc, add_left_comm, add_comm]
      · have hy : 8 < depth x := by omega
        simp [hx, hy, ih, add_assoc, add_left_comm, add_comm]

/-- A single genuine frozen correction splits into EXACT physical
rank-nine and later signed attempt sums. All suffix Euler products,
incoming root weights, signs and repetitions are unchanged. -/
theorem physical_correction_eq_rankNine_add_later
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    firstExitCorrection
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      halfProductDensity s.selectedPrefix s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
      s.remaining =
        rankNineSigned n e q om N c s useParent +
        physicalLaterSigned n e q om N c s useParent := by
  rw [correction_eq_failed_attempt_sum]
  change
    ((physicalFailedAt n e q om N c s useParent).map
      (FirstExitRejectedAttempt.value halfProductDensity)).sum =
      rankNineSigned n e q om N c s useParent +
        physicalLaterSigned n e q om N c s useParent
  exact sum_split_at_eight
    (physicalFailedAt n e q om N c s useParent)
    (fun a : FirstExitRejectedAttempt ℕ => a.older.length)
    (FirstExitRejectedAttempt.value halfProductDensity)

/-- Both actual policies are evaluated at the SAME eighth occurrence.
No cap monotonicity is used to subtract the two signed corrections. -/
theorem correctionGapAt_eq_rankNine_gap_add_later_gap
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) :
    correctionGapAt n e q om N c s =
      (rankNineSigned n e q om N c s true -
        rankNineSigned n e q om N c s false) +
      (physicalLaterSigned n e q om N c s true -
        physicalLaterSigned n e q om N c s false) := by
  change
    firstExitCorrection
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s true))
        halfProductDensity s.selectedPrefix s.positive
        (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
        s.remaining -
      firstExitCorrection
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s false))
        halfProductDensity s.selectedPrefix s.positive
        (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
        s.remaining = _
  rw [physical_correction_eq_rankNine_add_later
        n e q om N c s true,
      physical_correction_eq_rankNine_add_later
        n e q om N c s false]
  ring

/-- Genuine owner/trim list of rank-nine signed contributions, with all
repeated eighth states kept as occurrences. -/
def ownedRankNineSigned
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (useParent : Bool) : ℝ :=
  ((states (width r) n e q om N cap w z
    (fun _ : ℕ => (1 : ℝ)) c).map
      (fun s => rankNineSigned n e q om N c s useParent)).sum

/-- A linearity lemma retaining LIST multiplicity and all four signed
orientations: old rank-nine, new rank-nine, old later, new later. -/
private theorem list_four_gap {α : Type*} (xs : List α)
    (f a b c d : α → ℝ) :
    (∀ x ∈ xs, f x = (a x - b x) + (c x - d x)) →
      (xs.map f).sum =
        ((xs.map a).sum - (xs.map b).sum) +
        ((xs.map c).sum - (xs.map d).sum) := by
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro h
      have hx := h x (by simp)
      have htail := ih (by
        intro y hy
        exact h y (by simp [hy]))
      simp only [List.map_cons, List.sum_cons]
      rw [hx, htail]
      ring

/-- The full87 physical correction GAP is precisely the old-minus-new
rank-nine attempt sum PLUS the old-minus-new later-odd attempt sum.
The same physical owner/trim list is used in all four sums. -/
theorem ownedCorrectionGap_eq_rankNine_gap_add_later_gap
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    ownedCorrectionGap (width r) n e q om N cap w z c =
      (ownedRankNineSigned r n e q om N cap w z c true -
        ownedRankNineSigned r n e q om N cap w z c false) +
      (ownedPhysicalLaterSigned r n e q om N cap w z c true -
        ownedPhysicalLaterSigned r n e q om N cap w z c false) := by
  unfold ownedCorrectionGap ownedRankNineSigned ownedPhysicalLaterSigned
  apply list_four_gap
  intro s hs
  exact correctionGapAt_eq_rankNine_gap_add_later_gap n e q om N c s

/-- ORIGINAL full-q arithmetic old-minus-new (not a surrogate density):
exact sum of rank-nine, later physical correction, and the UNPAID
sign-dependent terminal mismatch, over all 87 actual owner cells. -/
theorem full87_arithmetic_eq_rankNine_later_and_terminal
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G -
      physical (policy (width r) n e q om (N : ℝ)) N cap w z L G =
      (∑ c : Cell,
        (ownedRankNineSigned r n e q om N cap w z c true -
          ownedRankNineSigned r n e q om N cap w z c false)) +
      (∑ c : Cell,
        (ownedPhysicalLaterSigned r n e q om N cap w z c true -
          ownedPhysicalLaterSigned r n e q om N cap w z c false)) +
      (∑ c : Cell,
        ownedTerminalMismatchGap (width r) n e q om N cap w z L G c) := by
  rw [physical_saving_eq_correction_plus_terminalMismatch]
  have hcells :
      (∑ c : Cell, ownedCorrectionGap (width r) n e q om N cap w z c) =
        ∑ c : Cell,
          ((ownedRankNineSigned r n e q om N cap w z c true -
              ownedRankNineSigned r n e q om N cap w z c false) +
           (ownedPhysicalLaterSigned r n e q om N cap w z c true -
              ownedPhysicalLaterSigned r n e q om N cap w z c false)) := by
    apply Finset.sum_congr rfl
    intro c hc
    exact ownedCorrectionGap_eq_rankNine_gap_add_later_gap
      r n e q om N cap w z c
  rw [hcells, Finset.sum_add_distrib]

/-- One-shot comparison against the EXISTING adjusted-later ledger.
Rank nine and the original full-q terminal mismatch remain separately
visible. Both old and new sides are paid once (not twice), each with
its own signed absolute budget and the SAME actual RealizedHistory
premise at its eighth owner state. This is a finite inequality only. -/
theorem owned_arithmetic_vs_rankNine_adjusted_later
    (r n : ℕ) (hn : 4 * width n < width r)
    (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hN : 1 < (N : ℝ)) (hEven : 2 ∣ N)
    (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) (hi : ℕ)
    (hHistory : ∀ s ∈ states (width r) n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c,
      RealizedHistory e q om (N : ℝ) s.selectedPrefix c) :
    |ownedSource (width r) n e q om N cap w z L G c -
      ((ownedRankNineSigned r n e q om N cap w z c true -
          ownedRankNineSigned r n e q om N cap w z c false) +
       (ownedAdjustedLaterSigned r n e q om N cap hi w z c true -
          ownedAdjustedLaterSigned r n e q om N cap hi w z c false))| ≤
      ownedTerminalMismatchCost (width r) n e q om N cap w z L G c +
        (ownedLaterAbsoluteBudget r n e q om N cap w z c true +
          ownedLaterAbsoluteBudget r n e q om N cap w z c false) := by
  let S := ownedSource (width r) n e q om N cap w z L G c
  let C := ownedCorrectionGap (width r) n e q om N cap w z c
  let X := ownedRankNineSigned r n e q om N cap w z c true -
    ownedRankNineSigned r n e q om N cap w z c false
  let A := ownedPhysicalLaterSigned r n e q om N cap w z c true
  let B := ownedPhysicalLaterSigned r n e q om N cap w z c false
  let AA := ownedAdjustedLaterSigned r n e q om N cap hi w z c true
  let BB := ownedAdjustedLaterSigned r n e q om N cap hi w z c false
  let T := ownedTerminalMismatchCost (width r) n e q om N cap w z L G c
  let E1 := ownedLaterAbsoluteBudget r n e q om N cap w z c true
  let E2 := ownedLaterAbsoluteBudget r n e q om N cap w z c false
  have hsplit : C = X + (A - B) :=
    ownedCorrectionGap_eq_rankNine_gap_add_later_gap
      r n e q om N cap w z c
  have ht : |S - C| ≤ T :=
    ownedSource_sub_correction_abs_le_terminalCost
      (width r) n e q om N cap w z L G c
  have hOld : |A - AA| ≤ E1 :=
    owned87_later_physical_signed_deletion_ledger
      r n hn e q om N cap hN hEven w z c true hi hHistory
  have hNew : |B - BB| ≤ E2 :=
    owned87_later_physical_signed_deletion_ledger
      r n hn e q om N cap hN hEven w z c false hi hHistory
  change |S - (X + (AA - BB))| ≤ T + (E1 + E2)
  calc
    |S - (X + (AA - BB))| =
        |(S - C) + ((A - AA) - (B - BB))| := by
          rw [hsplit]
          congr 1
          ring
    _ ≤ |S - C| + |(A - AA) - (B - BB)| := abs_add_le _ _
    _ ≤ T + (|A - AA| + |B - BB|) :=
      add_le_add ht (abs_sub_le _ _)
    _ ≤ T + (E1 + E2) :=
      add_le_add_left (add_le_add hOld hNew) T

end
end ImbalancedChen.P4AOriginalFull87CorrectionRankTerminal
