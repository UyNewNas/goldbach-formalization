import ImbalancedChen.Part5OriginalH430ClosedCellIdealSplit

/-!
P5.6 / h34. Quantitative payment interface for the exact fixed-read
slack in the TRUE original 106-bank selected request history.

The preceding packet exposed two positive debts, including the NONNEGATIVE
W1/W2 fixed-reference slack. Here the latter is bounded by a single real
anchor discrepancy bound for each generation, sampled only at the ORIGINAL
10 W1 fixed anchors and 36 pairs of W2 fixed anchors. The W2 mix is exactly
4:1 divided by 5; each real winning Fin occurrence is paid once with its
original path mark and same-Q Theta. No scalar-owner substitution occurs.

No approximation-size claim is made: the finite anchor discrepancy bound
is an explicit, still-unproved manuscript-internal obligation to be paid
from the original closed-cell induction. No PNT/BV input, h34 assumption,
new axiom or h34 count-source identity is introduced.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FixedAnchorSlackPayment

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger
open Part5OriginalH430TrueBankFeedbackFloorCredit
open Part5OriginalH430ClosedCellIdealSplit

/-- Only the original 10 W1 fixed anchors and original 36 W2 pairs
are required, at the TRUE previous-generation table. -/
def FixedAnchorUpper (g : Fin 430) (F : ℝ → ℝ) (delta : ℝ) : Prop :=
  (∀ j : Fin 10,
    F (W1Anchor j) - floorValue (precedingH g) (w1Cell j) ≤ delta) ∧
  (∀ j : Fin 36,
    F (originalW2At j).s0 - floorValue (precedingH g) (w2Cell j true) ≤ delta ∧
    F (originalW2At j).phi1 - floorValue (precedingH g) (w2Cell j false) ≤ delta)

/-- The original W1 fixed read has weight 1, and each W2 fixed read
has weights 4/5 and 1/5. Hence there is NO factor 2, 5 or 106 here. -/
theorem fixedReadSlack_le_anchor_delta
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ)
    (delta : ℝ) (hanchor : FixedAnchorUpper g F delta) :
    fixedReadSlack g a F ≤ delta := by
  rcases a with ⟨i,j⟩ | j
  · simpa only [fixedReadSlack, fixedReference, fixedValue] using hanchor.1 j
  · have h0 := (hanchor.2 j).1
    have h1 := (hanchor.2 j).2
    change (4 * F (originalW2At j).s0 + F (originalW2At j).phi1)/5 -
      (4 * floorValue (precedingH g) (w2Cell j true) +
        floorValue (precedingH g) (w2Cell j false))/5 ≤ delta
    linarith only [h0, h1]

/-- The fixed debt is bounded actionwise by exactly the same one-sided
anchor allowance, with no coefficient-mass loss. -/
theorem fixedReadSlack_interval
    (g : Fin 430) (a : Original106Action) (F : ℝ → ℝ)
    (delta : ℝ)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s)
    (hanchor : FixedAnchorUpper g F delta) :
    0 ≤ fixedReadSlack g a F ∧ fixedReadSlack g a F ≤ delta :=
  ⟨fixedReadSlack_nonneg g a F hcells,
   fixedReadSlack_le_anchor_delta g a F delta hanchor⟩

/-- Actual total selected-bank Theta: the original winning action
and Fin history occurrence, never a scalar bankFamily owner. -/
def bankSelectedTheta (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, levelTheta N n root tau p g a

/-- A quantitative bound for the entire original W1/W2 fixed-reference
slack in the real selected bank history. No CLOSED-CELL result is assumed
for this upper direction; it only needs the finite anchor upper defects.
The request geometry ensures genuine occurrenceScale >= 0. -/
theorem bank_fixed_slack_le_anchor_delta_theta
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ) (delta : ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hanchor : FixedAnchorUpper g F delta) :
    bankFixedSlackMass N n root tau p g F ≤
      delta * bankSelectedTheta N n root tau p g := by
  unfold bankFixedSlackMass bankSelectedTheta levelTheta
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hscale := occurrenceScale_nonneg N n root tau p g l
    hN ht ht' hn hp hband
  have hpoint := mul_le_mul_of_nonneg_left
    (fixedReadSlack_le_anchor_delta g a F delta hanchor) hscale
  calc
    levelMark l * (occurrenceTheta N n root tau p g l *
        fixedReadSlack g a F) =
      occurrenceScale N n root tau p g l * fixedReadSlack g a F := by
        simp only [occurrenceScale, mul_assoc]
    _ ≤ occurrenceScale N n root tau p g l * delta := hpoint
    _ = delta * (levelMark l *
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old)) := by
        dsimp [occurrenceScale, occurrenceTheta]
        ring

/-- One budget per actual preceding generation. The root bound retains
both the zero-generation seed and the Buchstab physical source, the
applied-error term, and positive capped feedback-floor credit on LEFT.
This replaces only the exact fixed slack by delta_g times actual bank
Theta; it does NOT pay delta_g or assert it tends to zero. -/
theorem frozen_root_le_anchor_delta_budget
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ) (delta : Fin 430 → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s)
    (hanchor : ∀ g : Fin 430, FixedAnchorUpper g F (delta g)) :
    weightedRequest N (rootQ N n root tau p) 430
        (rootRequest N n root tau p) +
      (∑ g : Fin 430, bankFeedbackFloorCredit N n root tau p g) ≤
      (∑ l : LevelIndex N n root tau p 0,
        levelMark l *
          max 0 (weightedRequest N (rootQ N n root tau p) 0
            (levelOccurrence l).current)) +
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            delta g * bankSelectedTheta N n root tau p g) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  have hroot := frozen_root_le_ideal_balance_plus_fixed_slack
    N n root tau p F hN ht ht' hn hp hband hclosed
  have hlevels :
      (∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            bankFixedSlackMass N n root tau p g F) +
          bankPhysicalAppliedAbs N n root tau p g)) ≤
      ∑ g : Fin 430,
        (buchstabPhysicalSource N n root tau p g +
          (bankBaseIdealPositive N n root tau p g +
            delta g * bankSelectedTheta N n root tau p g) +
          bankPhysicalAppliedAbs N n root tau p g) := by
    apply Finset.sum_le_sum
    intro g _
    have hd := bank_fixed_slack_le_anchor_delta_theta
      N n root tau p g F (delta g) hN ht ht' hn hp hband (hanchor g)
    linarith only [hd]
  exact hroot.trans (add_le_add_left hlevels _)

end
end ImbalancedChen.Part5OriginalH430FixedAnchorSlackPayment
