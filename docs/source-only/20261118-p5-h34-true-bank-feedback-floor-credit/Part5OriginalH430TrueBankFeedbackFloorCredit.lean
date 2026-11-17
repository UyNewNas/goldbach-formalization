import ImbalancedChen.Part5OriginalH430LiteralBankQ80PhysicalExcess
import ImbalancedChen.Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-!
P5.6 / h34: retain the ORIGINAL per-product integer feedback floor as
an exact CAPPED CREDIT in the positive physical bank read gap.

The actual selected candidate is at most the original real candidate.
The latter is its pre-feedback-floor candidate minus the old, nonnegative
per-product Euclidean remainder, not an independent cost to be added.
For each selected Fin occurrence this packet proves the exact clipped
credit identity BEFORE summing, then injects it into the true 430-root
physical bound. It does NOT establish a numerical upper bound for the
remaining pre-floor positive excess, Buchstab, seed, count owner or h34.

No new axiom, extra closed-cell hypothesis, scalar/cell exchange, or
repeated-history quotient. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430TrueBankFeedbackFloorCredit
noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430DirectPhysicalBankPayment
open Part5OriginalH430LiteralBankQ80PhysicalExcess

/-- Physical *pre-feedback-floor* excess of the literal original base,
fixed read and unrounded feedback over the same-Q original ideal. -/
def preFloorAtom (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) : ℝ :=
  occurrenceTheta N n root tau p g l *
      (baseValue a + fixedValue (iterate g.val true) a +
        idealFeedbackValue (iterate g.val) a) -
    occurrenceTheta N n root tau p g l *
      idealCellProfile (precedingH g) (precedingh g) a

/-- Only the actual sum of Euclidean remainders, with its original
row divisor and Q80 decoder, is eligible for floor credit. -/
def floorAtom (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) : ℝ :=
  occurrenceTheta N n root tau p g l *
    feedbackRoundingLoss (iterate g.val) a

/-- The real selected-bank candidate gap, on the very same actual
specified-cell/scalar occurrence, is exactly pre-floor gap minus the
original per-product floor loss. There is NO final-candidate-Q80-floor
equality assumed here: that candidate is only bounded above by this one. -/
theorem real_candidate_gap_eq_prefloor_sub_feedback_floor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) :
    occurrenceTheta N n root tau p g l *
        (baseValue a + fixedValue (iterate g.val true) a +
          feedbackValue (iterate g.val) a) -
      occurrenceTheta N n root tau p g l *
        idealCellProfile (precedingH g) (precedingh g) a =
      preFloorAtom N n root tau p g a l -
        floorAtom N n root tau p g a l := by
  dsimp [preFloorAtom, floorAtom]
  rw [ideal_feedback_exact]
  ring

/-- An exact clipped credit, valid even when the pre-floor gap is
negative or its nonnegative remainder exceeds the gap. -/
private theorem positive_sub_credit (x y : ℝ) (hy : 0 ≤ y) :
    max 0 (x - y) + min (max 0 x) y = max 0 x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right hx]
    rcases le_total y x with hyx | hxy
    · rw [min_eq_right hyx, max_eq_right (sub_nonneg.mpr hyx)]
      ring
    · rw [min_eq_left hxy, max_eq_left (sub_nonpos.mpr hxy)]
      ring
  · rw [max_eq_left hx, min_eq_left hy]
    have hxy : x - y ≤ 0 := by linarith only [hx, hy]
    rw [max_eq_left hxy]
    ring

/-- The genuinely unpaid pre-floor positive gap, retaining one summand
for every selected ORIGINAL 106-bank Fin history occurrence. -/
def bankPreFloorIdealExcess (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l * max 0 (preFloorAtom N n root tau p g a l)

/-- Floor credit is CAPPED by the pre-floor positive gap, pointwise.
It is not the full signed floor loss when the gap is already zero. -/
def bankFeedbackFloorCredit (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l * min (max 0 (preFloorAtom N n root tau p g a l))
        (floorAtom N n root tau p g a l)

/-- Exact clipped floor, once per true selected Fin occurrence. -/
theorem real_candidate_atom_plus_floor_credit_eq_prefloor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (htheta : 0 ≤ occurrenceTheta N n root tau p g l) :
    max 0
        (occurrenceTheta N n root tau p g l *
            (baseValue a + fixedValue (iterate g.val true) a +
              feedbackValue (iterate g.val) a) -
          occurrenceTheta N n root tau p g l *
            idealCellProfile (precedingH g) (precedingh g) a) +
      min (max 0 (preFloorAtom N n root tau p g a l))
        (floorAtom N n root tau p g a l) =
      max 0 (preFloorAtom N n root tau p g a l) := by
  have hf : 0 ≤ floorAtom N n root tau p g a l := by
    exact mul_nonneg htheta (feedbackRoundingLoss_nonneg (iterate g.val) a)
  rw [real_candidate_gap_eq_prefloor_sub_feedback_floor]
  exact positive_sub_credit _ _ hf

/-- The original selected-bank real gap PLUS its clipped Euclidean
floor credit equals the full pre-floor positive gap. This is an
identity of positive parts at REAL selected positions, not the signed
bank ledger and not a bound on the original count-source. -/
theorem bank_real_excess_plus_floor_credit_eq_prefloor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (hN : 4 ≤ N)
    (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankRealCandidateIdealExcess N n root tau p g +
      bankFeedbackFloorCredit N n root tau p g =
      bankPreFloorIdealExcess N n root tau p g := by
  unfold bankRealCandidateIdealExcess bankFeedbackFloorCredit
    bankPreFloorIdealExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ occurrenceTheta N n root tau p g l := by
    exact thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  simpa only [occurrenceTheta, mul_add] using
    congrArg (fun z : ℝ => levelMark l * z)
      (real_candidate_atom_plus_floor_credit_eq_prefloor
        N n root tau p g a l htheta)

/-- Pointwise-selected Q80 physical excess inherits the full capped
floor credit without assuming an exact final candidate floor formula. -/
theorem bank_literal_excess_plus_floor_credit_le_prefloor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (hN : 4 ≤ N)
    (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankLiteralQ80IdealExcess N n root tau p g +
      bankFeedbackFloorCredit N n root tau p g ≤
      bankPreFloorIdealExcess N n root tau p g := by
  have hc := literal_q80_excess_le_real_candidate_excess
    N n root tau p g hN ht ht' hn hp hband
  have he := bank_real_excess_plus_floor_credit_eq_prefloor
    N n root tau p g hN ht ht' hn hp hband
  linarith only [hc, he]

/-- The clipped credit is genuinely nonnegative; it cannot be used as
negative mass and it never exceeds the pre-floor positive gap. -/
theorem bank_feedback_floor_credit_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (hN : 4 ≤ N)
    (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ bankFeedbackFloorCredit N n root tau p g := by
  unfold bankFeedbackFloorCredit
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ occurrenceTheta N n root tau p g l := by
    exact thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hf : 0 ≤ floorAtom N n root tau p g a l := by
    exact mul_nonneg htheta (feedbackRoundingLoss_nonneg (iterate g.val) a)
  have hmin : 0 ≤ min (max 0 (preFloorAtom N n root tau p g a l))
      (floorAtom N n root tau p g a l) :=
    le_min (le_max_left _ _) hf
  exact mul_nonneg (mark_pos _).le hmin

/-- Genuine frozen 430-root payment with the floor credit retained on
the LEFT: it is never billed as an additional absolute Q80 error. The
unpaid pre-floor gap, Buchstab positive source, zero seed and applied
bank error are visible. This DOES NOT close the count induction. -/
theorem frozen_root_le_prefloor_with_actual_feedback_credit
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430, bankFeedbackFloorCredit N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPreFloorIdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_seed_buchstab_literal_q80_applied
    N n root tau p
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankLiteralQ80IdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g)) +
        (∑ g : Fin 430, bankFeedbackFloorCredit N n root tau p g) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPreFloorIdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro g _
    have hc := bank_literal_excess_plus_floor_credit_le_prefloor
      N n root tau p g hN ht ht' hn hp hband
    linarith only [hc]
  linarith only [hroot, hlevels]

end
end ImbalancedChen.Part5OriginalH430TrueBankFeedbackFloorCredit
