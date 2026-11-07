import ImbalancedChen.Part5OriginalH430ActualFeedbackQuotientRemainders

/-!
P5.6 / h34 — original selected 106-bank GLOBAL occurrence ledger.

The previous source proved exact signed integer feedback division PER bank.
This source carries that identity across the actual selected LevelIndex
positions, with their original positive history marks and parent Theta.
It then exposes the ORIGINAL base, 4:1 fixed W2 read, ideal feedback,
strict-prime selected child and Q80 floor as five distinct terms.

In particular the real-ideal feedback correction is SUBTRACTED from the
actual bank gap, not paid a second time as a positive analytic error.
The lemma is still conditional on the genuine preceding closed-cell
estimate and is not an original U3/U4 selected-count equality, a seed
application or a complete CLOSED-CELL induction.

All names, c/K, root 7/2, row 12, true alpha, same Q and 430+11 remain
unchanged. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430SelectedBankGlobalFloorBaseLedger
noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430PhysicalRoots Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430ActualFeedbackQuotientRemainders

/-- Parent Theta at a genuine occurrence of the original request history. -/
def occurrenceTheta (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (l : Index N n root tau p g) : ℝ :=
  thetaAtom N (rootQ N n root tau p)
    (parentProduct (levelOccurrence l).current.old)

/-- Original positive path mark times its own SAME-Q parent Theta. -/
def occurrenceScale (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (l : Index N n root tau p g) : ℝ :=
  levelMark l * occurrenceTheta N n root tau p g l

theorem occurrenceScale_nonneg (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (l : Index N n root tau p g)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ occurrenceScale N n root tau p g l := by
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  exact mul_nonneg (mark_pos _).le htheta

/-- One selected bank per real LevelIndex, without quotienting by
catalog labels, integer products, root primes or source fibres. -/
def selectedBankActualGap (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      bankFixedReferenceGap N n root tau p g F a l

def selectedBankIdealGap (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      bankIdealFeedbackGap N n root tau p g F a l

/-- Signed integer division produces a nonnegative loss, summed ONCE
per selected bank occurrence with the original action's own divisor. -/
def selectedBankRoundingLoss (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        feedbackRoundingLoss (iterate g.val) a

/-- Exact GLOBAL floor identity: no 106-to-1 normalization, and no
multiplicity erasure when two historical paths share a catalog label. -/
theorem selected_bank_floor_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) :
    selectedBankIdealGap N n root tau p g F =
      selectedBankActualGap N n root tau p g F +
        selectedBankRoundingLoss N n root tau p g := by
  classical
  unfold selectedBankIdealGap selectedBankActualGap selectedBankRoundingLoss
  calc
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        bankIdealFeedbackGap N n root tau p g F a l) =
      ∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          (bankFixedReferenceGap N n root tau p g F a l +
            occurrenceScale N n root tau p g l *
              feedbackRoundingLoss (iterate g.val) a) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro l _
        simpa only [occurrenceScale, occurrenceTheta, mul_assoc] using
          bank_ideal_feedback_exact N n root tau p g F a l
    _ = _ := by simp only [Finset.sum_add_distrib]

theorem selected_bank_rounding_nonneg (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    0 ≤ selectedBankRoundingLoss N n root tau p g := by
  unfold selectedBankRoundingLoss
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro l _
  exact mul_nonneg
    (occurrenceScale_nonneg N n root tau p g l
      hN ht ht' hn hp hband)
    (feedbackRoundingLoss_nonneg (iterate g.val) a)

/-- The original per-product payment envelope, with ORIGINAL row divisor
and the actual number of repeated weighted integer products. -/
def selectedBankRoundingEnvelope (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        (((literalFeedbackProducts (iterate g.val) a).length : ℝ) /
          ((P2Selected430LiteralActionData.rows
            (slotOfAction a)).divisor : ℝ) / (2^80 : ℝ))

theorem selected_bank_rounding_le_envelope (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    selectedBankRoundingLoss N n root tau p g ≤
      selectedBankRoundingEnvelope N n root tau p g := by
  unfold selectedBankRoundingLoss selectedBankRoundingEnvelope
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l _
  exact mul_le_mul_of_nonneg_left
    (feedbackRoundingLoss_le_length (iterate g.val) a)
    (occurrenceScale_nonneg N n root tau p g l
      hN ht ht' hn hp hband)

/-- Original base and prior-cell fixed reference are kept separate from
the rationalized feedback. Neither term is declared paid by this file. -/
def selectedBankBaseMass (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l * baseValue a

def selectedBankFixedMass (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l * fixedReference F a

def selectedBankIdealFeedbackMass (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      occurrenceScale N n root tau p g l *
        idealFeedbackValue (iterate g.val) a

def selectedBankPrimeChildMass (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action,
    ∑ l ∈ selectedLevel N n root tau p g a,
      levelMark l * childTerm N n root tau p g l

/-- Exact selected-action decomposition into literal base, old-cell
fixed term, ideal feedback and actual strict-prime child subtractions. -/
theorem selected_bank_ideal_components (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ) :
    selectedBankIdealGap N n root tau p g F =
      selectedBankBaseMass N n root tau p g +
      selectedBankFixedMass N n root tau p g F +
      selectedBankIdealFeedbackMass N n root tau p g -
      selectedBankPrimeChildMass N n root tau p g := by
  classical
  unfold selectedBankIdealGap
  calc
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        bankIdealFeedbackGap N n root tau p g F a l) =
      ∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          (occurrenceScale N n root tau p g l * baseValue a +
           occurrenceScale N n root tau p g l * fixedReference F a +
           occurrenceScale N n root tau p g l *
             idealFeedbackValue (iterate g.val) a -
           levelMark l * childTerm N n root tau p g l) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro l _
        unfold bankIdealFeedbackGap occurrenceScale occurrenceTheta
        ring
    _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          selectedBankBaseMass, selectedBankFixedMass,
          selectedBankIdealFeedbackMass, selectedBankPrimeChildMass]
        ring

/-- One-generation arithmetic SOURCE upper, still conditional on the
actual preceding closed-cell inequality, retaining every literal base,
the original fixed 4:1 read, real feedback, strict-prime children and
SUBTRACTED integer floor loss. It asserts no U3/U4 source bijection. -/
theorem actual_one_generation_base_feedback_floor_upper (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g +
        selectedBankRoundingLoss N n root tau p g +
        selectedBankPrimeChildMass N n root tau p g ≤
      buchstabLevelError N n root tau p g +
        selectedBankBaseMass N n root tau p g +
        selectedBankFixedMass N n root tau p g F +
        selectedBankIdealFeedbackMass N n root tau p g := by
  have hstep := actual_one_generation_fixed_upper N n root tau p g F
    hN ht ht' hn hp hband hcells
  have hfloor : selectedBankIdealGap N n root tau p g F =
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          bankFixedReferenceGap N n root tau p g F a l) +
        selectedBankRoundingLoss N n root tau p g := by
    simpa only [selectedBankActualGap] using
      selected_bank_floor_exact N n root tau p g F
  have hparts := selected_bank_ideal_components N n root tau p g F
  linarith only [hstep, hfloor, hparts]

/-- Forgetting the NONNEGATIVE floor credit gives a weaker clean source
upper. The exact stronger version above remains the one to reuse when
integral/Theta payments are made, avoiding a second Q80 charge. -/
theorem actual_one_generation_base_feedback_upper (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g +
        selectedBankPrimeChildMass N n root tau p g ≤
      buchstabLevelError N n root tau p g +
        selectedBankBaseMass N n root tau p g +
        selectedBankFixedMass N n root tau p g F +
        selectedBankIdealFeedbackMass N n root tau p g := by
  have hstep := actual_one_generation_base_feedback_floor_upper
    N n root tau p g F hN ht ht' hn hp hband hcells
  have hround := selected_bank_rounding_nonneg N n root tau p g
    hN ht ht' hn hp hband
  linarith only [hstep, hround]

end
end ImbalancedChen.Part5OriginalH430SelectedBankGlobalFloorBaseLedger
