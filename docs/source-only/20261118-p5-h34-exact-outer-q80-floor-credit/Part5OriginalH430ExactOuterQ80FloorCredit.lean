import ImbalancedChen.Part5OriginalH430SelectedPositiveAnchorPayment

/-!
P5.6 / h34: restore the OUTER original 106-bank integer quotient remainder.

The earlier per-product Q80 feedback ledger is exact, but the final original
candidate also divides the combined fixed-point and feedback numerator by
the W1/W2 outer divisor (1 or 5). Its remainder was previously discarded
through a one-sided candidate upper bound. This packet restores that final
literal integer payment, valid even for signed preceding table arrays.

The additional nonnegative remainder is charged only at genuinely selected
Fin occurrences with the original same-Q parent Theta and history mark.
The sum of the two floor losses is clipped by the actual pre-floor positive
surplus, so neither floor can be over-credited. The frozen 430-root bound
retains this COMPLETE eligible floor credit on its left side.

No numerical lower bound on the eligible credit is claimed. The CLOSED-CELL
premise, dynamic/Buchstab/seed payments, original count ownership, PP and
common refinement remain manuscript-internal and OPEN.
SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ExactOuterQ80FloorCredit

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualFeedbackQuotientRemainders
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430LiteralBankQ80PhysicalExcess
open Part5OriginalH430TrueBankFeedbackFloorCredit
open Part5OriginalH430ClosedCellPositivePrefloor
open Part5OriginalH430ClosedCellIdealSplit
open Part5OriginalH430SelectedPositiveAnchorPayment

/-- Original fixed-point integer point numerator, prior to the ONLY
outer action divisor. It preserves repeated point occurrences. -/
def originalPointNumerator (old : Table) (a : Original106Action) : ℤ :=
  ((P2Selected430LiteralActionData.rows (slotOfAction a)).points.map
    (fun p => read old true p.1 * p.2)).sum

/-- Remainder of the original final W1/W2 candidate division.
This is distinct from the earlier PER-PRODUCT q80 feedback remainders. -/
def originalOuterRemainder (old : Table) (a : Original106Action) : ℤ :=
  (originalPointNumerator old a + feedbackNumerator old a) %
    ((P2Selected430LiteralActionData.rows (slotOfAction a)).divisor : ℤ)

/-- Exact real loss of the final outer integer quotient, AFTER
the original W1=1 / W2=5 divisor and the unchanged Q80 decoder. -/
def outerRoundingLoss (old : Table) (a : Original106Action) : ℝ :=
  (originalOuterRemainder old a : ℝ) /
    ((P2Selected430LiteralActionData.rows (slotOfAction a)).divisor : ℝ) /
      (2^80 : ℝ)

theorem outerRoundingLoss_nonneg (old : Table) (a : Original106Action) :
    0 ≤ outerRoundingLoss old a := by
  have hd : (0 : ℤ) <
      ((P2Selected430LiteralActionData.rows
        (slotOfAction a)).divisor : ℤ) := by
    exact_mod_cast literal_divisor_pos a
  have hr : (0 : ℤ) ≤ originalOuterRemainder old a := by
    unfold originalOuterRemainder
    exact Int.emod_nonneg _ hd.ne'
  have hr' : (0 : ℝ) ≤ (originalOuterRemainder old a : ℝ) := by
    exact_mod_cast hr
  have hd' : (0 : ℝ) ≤
      ((P2Selected430LiteralActionData.rows
        (slotOfAction a)).divisor : ℝ) := by
    exact_mod_cast hd.le
  unfold outerRoundingLoss
  exact div_nonneg (div_nonneg hr' hd') (by positivity)

/-- Exact final integer-division identity. Unlike the previous
candidate_fixedRead_upper, equality retains the actual outer remainder.
No assumption on the sign of any original Q80 table entry. -/
theorem literal_candidate_plus_outer_floor_eq_real
    (old : Table) (a : Original106Action) :
    ((P2Selected430LiteralActionData.candidate old
      (P2Selected430LiteralActionData.rows (slotOfAction a)) : ℤ) : ℝ) /
        (2^80 : ℝ) +
      outerRoundingLoss old a =
        baseValue a + fixedValue (old true) a + feedbackValue old a := by
  let r := P2Selected430LiteralActionData.rows (slotOfAction a)
  let P : ℤ := originalPointNumerator old a
  let B : ℤ := feedbackNumerator old a
  let d : ℤ := (r.divisor : ℤ)
  let q : ℝ := (2^80 : ℝ)
  have hdpos : (0 : ℤ) < d := by
    dsimp [d, r]
    exact_mod_cast literal_divisor_pos a
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hcand :
      P2Selected430LiteralActionData.candidate old r =
        r.base + (P + B) / d := by
    dsimp [r, P, B, d, originalPointNumerator, feedbackNumerator,
      P2Selected430LiteralActionData.candidate]
    congr 1
    congr 1
    ring
  have hdiv : P + B = d * ((P + B) / d) + (P + B) % d := by
    calc
      P + B = (P + B) % d + d * ((P + B) / d) :=
        (Int.emod_add_ediv (P + B) d).symm
      _ = _ := by ring
  have hreal : (P : ℝ) + (B : ℝ) =
      (d : ℝ) * (((P + B) / d : ℤ) : ℝ) +
        (((P + B) % d : ℤ) : ℝ) := by
    exact_mod_cast hdiv
  have hbase : baseValue a = (r.base : ℝ) / q := by
    dsimp [baseValue, r, q]
  have hfixed : fixedValue (old true) a = (P : ℝ) / (d : ℝ) / q := by
    calc
      fixedValue (old true) a = rawFixedValue old a :=
        (rawFixedValue_eq old a).symm
      _ = (P : ℝ) / (d : ℝ) / q := by
        dsimp [rawFixedValue, P, d, q, r, originalPointNumerator]
  have hfeedback : feedbackValue old a = (B : ℝ) / (d : ℝ) / q := by
    dsimp [feedbackValue, B, d, q, r]
  have hloss : outerRoundingLoss old a =
      (((P + B) % d : ℤ) : ℝ) / (d : ℝ) / q := by
    dsimp [outerRoundingLoss, originalOuterRemainder, P, B, d, q, r,
      originalPointNumerator]
  change
    (((P2Selected430LiteralActionData.candidate old r : ℤ) : ℝ) / q +
      outerRoundingLoss old a =
        baseValue a + fixedValue (old true) a + feedbackValue old a)
  rw [hcand, hbase, hfixed, hfeedback, hloss]
  push_cast
  field_simp [hd, hq]
  nlinarith only [hreal]

/-- Exact outer-floor payment on the TRUE same-Q selected occurrence. -/
def outerFloorAtom (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) : ℝ :=
  occurrenceTheta N n root tau p g l *
    outerRoundingLoss (iterate g.val) a

/-- Literal selected integer-Q80 gap equals the full pre-floor gap
minus BOTH the original per-product feedback and final outer losses. -/
theorem prefloor_eq_literal_plus_both_floors
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g) :
    preFloorAtom N n root tau p g a l =
      (occurrenceTheta N n root tau p g l *
          literalChosenBankQ80 g a -
        occurrenceTheta N n root tau p g l *
          idealCellProfile (precedingH g) (precedingh g) a) +
      (floorAtom N n root tau p g a l +
        outerFloorAtom N n root tau p g a l) := by
  have ho := literal_candidate_plus_outer_floor_eq_real
    (iterate g.val) a
  have hi := ideal_feedback_exact (iterate g.val) a
  have hc :
      literalChosenBankQ80 g a +
        feedbackRoundingLoss (iterate g.val) a +
        outerRoundingLoss (iterate g.val) a =
      baseValue a + fixedValue (iterate g.val true) a +
        idealFeedbackValue (iterate g.val) a := by
    dsimp [literalChosenBankQ80]
    linarith only [ho, hi]
  unfold preFloorAtom floorAtom outerFloorAtom
  linear_combination (occurrenceTheta N n root tau p g l) * hc

/-- The two literal integer losses may be credited only up to the
positive pre-floor surplus at that SAME Fin occurrence. -/
def bankCompleteFloorCredit (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l *
        min (max 0 (preFloorAtom N n root tau p g a l))
          (floorAtom N n root tau p g a l +
            outerFloorAtom N n root tau p g a l)

private theorem positive_sub_two_floor_credit
    (x y : ℝ) (hy : 0 ≤ y) :
    max 0 (x-y) + min (max 0 x) y = max 0 x := by
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right hx]
    rcases le_total y x with hyx | hxy
    · rw [min_eq_right hyx, max_eq_right (sub_nonneg.mpr hyx)]
      ring
    · rw [min_eq_left hxy, max_eq_left (sub_nonpos.mpr hxy)]
      ring
  · rw [max_eq_left hx, min_eq_left hy]
    have hxy : x-y ≤ 0 := by linarith only [hx,hy]
    rw [max_eq_left hxy]
    ring

/-- The exact real-vs-integer identity on every ORIGINAL selected bank
occurrence, preserving the original predecessor Theta and integer floor. -/
theorem literal_atom_plus_complete_credit_eq_prefloor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (a : Original106Action)
    (l : Index N n root tau p g)
    (htheta : 0 ≤ occurrenceTheta N n root tau p g l) :
    max 0
      (occurrenceTheta N n root tau p g l *
          literalChosenBankQ80 g a -
        occurrenceTheta N n root tau p g l *
          idealCellProfile (precedingH g) (precedingh g) a) +
      min (max 0 (preFloorAtom N n root tau p g a l))
        (floorAtom N n root tau p g a l +
          outerFloorAtom N n root tau p g a l) =
        max 0 (preFloorAtom N n root tau p g a l) := by
  have hf : 0 ≤ floorAtom N n root tau p g a l :=
    mul_nonneg htheta (feedbackRoundingLoss_nonneg (iterate g.val) a)
  have ho : 0 ≤ outerFloorAtom N n root tau p g a l :=
    mul_nonneg htheta (outerRoundingLoss_nonneg (iterate g.val) a)
  have heq := prefloor_eq_literal_plus_both_floors
    N n root tau p g a l
  have hgap :
      occurrenceTheta N n root tau p g l *
          literalChosenBankQ80 g a -
        occurrenceTheta N n root tau p g l *
          idealCellProfile (precedingH g) (precedingh g) a =
      preFloorAtom N n root tau p g a l -
        (floorAtom N n root tau p g a l +
          outerFloorAtom N n root tau p g a l) := by
    linarith only [heq]
  rw [hgap]
  exact positive_sub_two_floor_credit _ _ (add_nonneg hf ho)

/-- Old bankLiteralQ80IdealExcess now has an EXACT clipped credit,
not merely the old one-sided bound that omitted the final quotient. -/
theorem bank_literal_plus_complete_credit_eq_prefloor
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankLiteralQ80IdealExcess N n root tau p g +
      bankCompleteFloorCredit N n root tau p g =
        bankPreFloorIdealExcess N n root tau p g := by
  unfold bankLiteralQ80IdealExcess bankCompleteFloorCredit
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
  have hpoint := literal_atom_plus_complete_credit_eq_prefloor
    N n root tau p g a l htheta
  simpa only [occurrenceTheta, mul_add] using
    congrArg (fun z : ℝ => levelMark l * z) hpoint

/-- The complete eligible integer-floor credit is nonnegative and
cannot exceed the genuine pre-floor positive excess. -/
theorem bank_complete_credit_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ bankCompleteFloorCredit N n root tau p g := by
  have hreal := bank_literal_plus_complete_credit_eq_prefloor
    N n root tau p g hN ht ht' hn hp hband
  unfold bankCompleteFloorCredit
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have ht0 : 0 ≤ occurrenceTheta N n root tau p g l :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hf := mul_nonneg ht0
    (feedbackRoundingLoss_nonneg (iterate g.val) a)
  have ho := mul_nonneg ht0
    (outerRoundingLoss_nonneg (iterate g.val) a)
  exact mul_nonneg (mark_pos _).le
    (le_min (le_max_left _ _) (add_nonneg hf ho))

/-- A frozen-root inequality with BOTH actual integer floors in their
correct direction, retaining the UNPAID Buchstab, seed, bank ideal and
applied-error sources. No CLOSED-CELL premise is used in this stage. -/
theorem frozen_root_le_prefloor_with_complete_credit
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430, bankCompleteFloorCredit N n root tau p g) ≤
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
        (∑ g : Fin 430, bankCompleteFloorCredit N n root tau p g) =
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          bankPreFloorIdealExcess N n root tau p g +
            bankPhysicalAppliedAbs N n root tau p g) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    have hc := bank_literal_plus_complete_credit_eq_prefloor
      N n root tau p g hN ht ht' hn hp hband
    linarith only [hc]
  linarith only [hroot, hlevels]

end
end ImbalancedChen.Part5OriginalH430ExactOuterQ80FloorCredit
