import ImbalancedChen.Part5OriginalH430FixedAnchorSlackPayment

/-!
P5.6 / h34: remove the additional, freely supplied FixedAnchorUpper
hypothesis from the true 430-root fixed-slack consumer.

The old packet correctly identified 82 original anchor APPEARANCES but
left an arbitrary delta(g) and its FixedAnchorUpper proof as independent
manuscript-internal inputs. This module constructs the LEAST NONNEGATIVE
uniform delta directly from the ORIGINAL preceding Q80 table and the
ORIGINAL ten W1 and 36+36 W2 anchor reads, by three finite nonempty suprema.

The resulting true-bank and frozen 430-root statements no longer require
a caller to assert FixedAnchorUpper. They retain all selected Fin occurrences,
same-Q physical theta, actual history marks, and original 4:1 W2 weights.

This does NOT prove the finite defect small, nor CLOSE the predecessor
CLOSED-CELL induction or root counting theorem. No table is recomputed or
replaced, and no new axiom/external analytic result is introduced.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ExplicitAnchorDefect

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
open Part5OriginalH430FixedAnchorSlackPayment

/-- Exact maximum of the original ten W1 endpoint deficits at the
genuine preceding-generation integer Q80 table. -/
def w1AnchorDefect (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin 10)).sup'
    ⟨0, Finset.mem_univ _⟩
    (fun j => F (W1Anchor j) -
      floorValue (precedingH g) (w1Cell j))

/-- Exact maximum of the FIRST original W2 fixed-endpoint deficits.
The same original 36 pair slots are retained. -/
def w2FirstAnchorDefect (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin 36)).sup'
    ⟨0, Finset.mem_univ _⟩
    (fun j => F (originalW2At j).s0 -
      floorValue (precedingH g) (w2Cell j true))

/-- Exact maximum of the SECOND original W2 fixed-endpoint deficits. -/
def w2SecondAnchorDefect (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin 36)).sup'
    ⟨0, Finset.mem_univ _⟩
    (fun j => F (originalW2At j).phi1 -
      floorValue (precedingH g) (w2Cell j false))

/-- The minimal NONNEGATIVE common upper allowance for all the 82
original fixed-anchor appearances at the actual preceding Q80 table.
This is a concrete finite expression, not a supplied error constant.
In particular, it is not asserted to be small or to decay in g. -/
def actualAnchorDefect (g : Fin 430) (F : ℝ → ℝ) : ℝ :=
  max 0 (max (w1AnchorDefect g F)
    (max (w2FirstAnchorDefect g F)
      (w2SecondAnchorDefect g F)))

theorem actualAnchorDefect_nonneg (g : Fin 430) (F : ℝ → ℝ) :
    0 ≤ actualAnchorDefect g F := by
  unfold actualAnchorDefect
  exact le_max_left _ _

private theorem w1_defect_le_sup (g : Fin 430) (F : ℝ → ℝ)
    (j : Fin 10) :
    F (W1Anchor j) - floorValue (precedingH g) (w1Cell j) ≤
      w1AnchorDefect g F := by
  unfold w1AnchorDefect
  exact Finset.le_sup'
    (fun k : Fin 10 =>
      F (W1Anchor k) - floorValue (precedingH g) (w1Cell k))
    (Finset.mem_univ j)

private theorem w2_first_defect_le_sup (g : Fin 430) (F : ℝ → ℝ)
    (j : Fin 36) :
    F (originalW2At j).s0 -
      floorValue (precedingH g) (w2Cell j true) ≤
      w2FirstAnchorDefect g F := by
  unfold w2FirstAnchorDefect
  exact Finset.le_sup'
    (fun k : Fin 36 =>
      F (originalW2At k).s0 -
        floorValue (precedingH g) (w2Cell k true))
    (Finset.mem_univ j)

private theorem w2_second_defect_le_sup (g : Fin 430) (F : ℝ → ℝ)
    (j : Fin 36) :
    F (originalW2At j).phi1 -
      floorValue (precedingH g) (w2Cell j false) ≤
      w2SecondAnchorDefect g F := by
  unfold w2SecondAnchorDefect
  exact Finset.le_sup'
    (fun k : Fin 36 =>
      F (originalW2At k).phi1 -
        floorValue (precedingH g) (w2Cell k false))
    (Finset.mem_univ j)

/-- Discharge the old packet's FixedAnchorUpper condition from the
original data itself, with no separate certificate supplied by the caller. -/
theorem actualAnchorDefect_supplies_upper
    (g : Fin 430) (F : ℝ → ℝ) :
    FixedAnchorUpper g F (actualAnchorDefect g F) := by
  have hw1 : w1AnchorDefect g F ≤ actualAnchorDefect g F := by
    unfold actualAnchorDefect
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hw2a : w2FirstAnchorDefect g F ≤ actualAnchorDefect g F := by
    unfold actualAnchorDefect
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hw2b : w2SecondAnchorDefect g F ≤ actualAnchorDefect g F := by
    unfold actualAnchorDefect
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  constructor
  · intro j
    exact (w1_defect_le_sup g F j).trans hw1
  · intro j
    exact ⟨(w2_first_defect_le_sup g F j).trans hw2a,
      (w2_second_defect_le_sup g F j).trans hw2b⟩

/-- Optimality: any nonnegative delta meeting all of the same ORIGINAL
anchor inequalities must dominate the explicit finite defect.
This prevents a fictitious smaller fixed-anchor payment. -/
theorem actualAnchorDefect_le_any_nonnegative_upper
    (g : Fin 430) (F : ℝ → ℝ) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hanchor : FixedAnchorUpper g F delta) :
    actualAnchorDefect g F ≤ delta := by
  have hw1 : w1AnchorDefect g F ≤ delta := by
    unfold w1AnchorDefect
    apply Finset.sup'_le
    intro j _
    exact hanchor.1 j
  have hw2a : w2FirstAnchorDefect g F ≤ delta := by
    unfold w2FirstAnchorDefect
    apply Finset.sup'_le
    intro j _
    exact (hanchor.2 j).1
  have hw2b : w2SecondAnchorDefect g F ≤ delta := by
    unfold w2SecondAnchorDefect
    apply Finset.sup'_le
    intro j _
    exact (hanchor.2 j).2
  unfold actualAnchorDefect
  exact max_le hdelta (max_le hw1 (max_le hw2a hw2b))

/-- Direct true selected-bank fixed-slack payment using the *actual*
finite predecessor Q80 anchor defect, with no extra anchor hypothesis.
This still depends on the prior manuscript-local selected history
geometry, exactly as the old supplier does. -/
theorem bank_fixed_slack_le_actual_anchor_defect
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    bankFixedSlackMass N n root tau p g F ≤
      actualAnchorDefect g F *
        bankSelectedTheta N n root tau p g := by
  exact bank_fixed_slack_le_anchor_delta_theta
    N n root tau p g F (actualAnchorDefect g F)
    hN ht ht' hn hp hband
    (actualAnchorDefect_supplies_upper g F)

/-- Frozen original 430-root consumer with no assumed FixedAnchorUpper.
Every generation's fixed payment is now the EXACT finite maximum of
actual predecessor-table anchor deficits, multiplied by existing
selected-bank Theta. This is not a numerical h34 closure: one must
still bound the computed defects and discharge the full CLOSED-CELL
count induction, dynamic/Buchstab/seed and original owner obligations. -/
theorem frozen_root_le_actual_anchor_defect_budget
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hclosed : ∀ g : Fin 430, ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
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
            actualAnchorDefect g F *
              bankSelectedTheta N n root tau p g) +
          bankPhysicalAppliedAbs N n root tau p g) := by
  exact frozen_root_le_anchor_delta_budget
    N n root tau p F (fun g => actualAnchorDefect g F)
    hN ht ht' hn hp hband hclosed
    (fun g => actualAnchorDefect_supplies_upper g F)

end
end ImbalancedChen.Part5OriginalH430ExplicitAnchorDefect
