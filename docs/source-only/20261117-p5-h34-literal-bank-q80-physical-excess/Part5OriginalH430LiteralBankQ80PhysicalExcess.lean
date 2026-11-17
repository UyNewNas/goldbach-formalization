import ImbalancedChen.Part5OriginalH430DirectPhysicalBankPayment
import ImbalancedChen.Part5OriginalH430RequestedCandidateLevel

/-!
P5.6 / h34: the actual winning 106-bank physical excess is linked to the
ORIGINAL INTEGER candidate / 2^80. The chosen scalar or specified-cell
resolver, same root Q, old array, positive path marks and repeated Fin
occurrences are unchanged. The exact Q80 identification precedes a
ONE-SIDED comparison to base + fixed + feedback under genuine parent
theta positivity. The latter positive excess is not paid by this packet.

No signed cancellation, nonwinning 106-bank alternative, arbitrary owner,
new external input, CLOSED-CELL base, or U3/U4 count-source assertion.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LiteralBankQ80PhysicalExcess
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430DirectPhysicalBankPayment

/-- The ORIGINAL selected integer candidate, on the preceding table,
with its literal Q80 divisor, not the larger real candidate. -/
def literalChosenBankQ80 (g : Fin 430) (a : Original106Action) : ℝ :=
  (P2Selected430LiteralActionData.candidate (iterate g.val)
    (P2Selected430LiteralActionData.rows (slotOfAction a)) : ℝ) /
      (2^80 : ℝ)

/-- The true selected scalar/cell request reads the exact old integer
candidate; its own resolver supplies the selected cell. -/
theorem selected_bank_true_read_eq_literal_q80
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (hl : l ∈ selectedLevel N n root tau p g a) :
    iteratedRequest (g.val+1) (levelOccurrence l).current =
      literalChosenBankQ80 g a := by
  obtain ⟨i, hs⟩ := (Finset.mem_filter.mp hl).2
  simpa only [literalChosenBankQ80, choiceValue] using (selected_value hs)

/-- Only an upper bound by the old real base/fixed/feedback candidate,
NOT an equality suppressing the Q80 integer floor. -/
theorem selected_literal_q80_le_real_candidate
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (hl : l ∈ selectedLevel N n root tau p g a) :
    literalChosenBankQ80 g a ≤
      baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a := by
  obtain ⟨i, hs⟩ := (Finset.mem_filter.mp hl).2
  calc
    literalChosenBankQ80 g a =
        iteratedRequest (g.val+1) (levelOccurrence l).current :=
      (selected_bank_true_read_eq_literal_q80 N n root tau p g a l hl).symm
    _ ≤ _ := by
      simpa only [action_slot] using (selected_bank_candidate_upper hs)

/-- Physical one-sided excess with the actual ORIGINAL integer Q80 read.
Positive part is taken BEFORE marking and summing over distinct positions. -/
def bankLiteralQ80IdealExcess (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        max 0
          (thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
                literalChosenBankQ80 g a -
            thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
                idealCellProfile (precedingH g) (precedingh g) a)

/-- Exact, occurrence-preserving identification of the previously open
true-read physical excess with its immutable integer Q80 numerator. -/
theorem true_read_ideal_excess_eq_literal_q80
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) :
    bankReadIdealPositiveExcess N n root tau p g =
      bankLiteralQ80IdealExcess N n root tau p g := by
  unfold bankReadIdealPositiveExcess bankLiteralQ80IdealExcess
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro l hl
  rw [selected_bank_true_read_eq_literal_q80 N n root tau p g a l hl]

/-- The winning real candidate's still-unpaid positive surplus over the
same physical ideal and under the same genuine parent theta. -/
def bankRealCandidateIdealExcess (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        max 0
          (thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
                (baseValue a + fixedValue (iterate g.val true) a +
                  feedbackValue (iterate g.val) a) -
            thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) *
                idealCellProfile (precedingH g) (precedingh g) a)

/-- Safe pointwise Q80-to-real one-sided comparison at every original
winning Fin occurrence. Theta positivity is derived from the admitted
source-root window; it is NOT a new hypothesis on arbitrary parents. -/
theorem literal_q80_excess_le_real_candidate_excess
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (hN : 4 ≤ N)
    (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankLiteralQ80IdealExcess N n root tau p g ≤
      bankRealCandidateIdealExcess N n root tau p g := by
  unfold bankLiteralQ80IdealExcess bankRealCandidateIdealExcess
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l hl
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hread := selected_literal_q80_le_real_candidate
    N n root tau p g a l hl
  have hscale := mul_le_mul_of_nonneg_left hread htheta
  have hpos :
      max 0
        (thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
            literalChosenBankQ80 g a -
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) *
              idealCellProfile (precedingH g) (precedingh g) a) ≤
      max 0
        (thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
            (baseValue a + fixedValue (iterate g.val true) a +
              feedbackValue (iterate g.val) a) -
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) *
              idealCellProfile (precedingH g) (precedingh g) a) := by
    apply max_le
    · exact le_max_left _ _
    · exact (sub_le_sub_right hscale _).trans (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left hpos (mark_pos _).le

/-- Exact substitution in the true frozen 430-root physical payment.
The original Q80 bank gap, Buchstab physical gap and seed are still OPEN. -/
theorem frozen_root_le_seed_buchstab_literal_q80_applied
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ) :
    weightedRequest N (rootQ N n root tau p) 430
      (rootRequest N n root tau p) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankLiteralQ80IdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g) := by
  simpa only [true_read_ideal_excess_eq_literal_q80] using
    (frozen_root_le_seed_buchstab_ideal_excess_applied N n root tau p)

/-- The existing one-threshold epsilon*Theta bank error payment continues
to hold after the exact Q80 replacement, with no double charge. -/
theorem uniform_frozen_root_le_seed_buchstab_literal_q80
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) ≤
        (∑ l : LevelIndex N n root tau p 0,
          levelMark l *
            max 0 (weightedRequest N (rootQ N n root tau p) 0
              (levelOccurrence l).current)) +
        ∑ g : Fin 430,
          (buchstabPhysicalSource N n root tau p g +
            bankLiteralQ80IdealExcess N n root tau p g +
              epsilon * bankPhysicalTheta N n root tau p g) := by
  simpa only [true_read_ideal_excess_eq_literal_q80] using
    (uniform_frozen_root_le_partly_paid_physical_source he)

end
end ImbalancedChen.Part5OriginalH430LiteralBankQ80PhysicalExcess
