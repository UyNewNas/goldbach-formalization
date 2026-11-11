import ImbalancedChen.Part5OriginalH430ActualThetaAbsolutePayment

/-!
P5.6 / h34 — cancel the EXACT retained Theta read before charging
the genuine bank/Buchstab source debt.

The previous absolute-payment packet charged |Theta-1| at every resolved
request, including retention. That payment is needlessly coarse for the
original read-minus-child CLOSED-CELL inequality: on a retained winner
the physical Theta-weighted new-table read IS its original child edge.
Here the retained correction cancels against the retained unweighted
request, and only Buchstab/106-bank winners retain a Theta correction.

This is a genuine reduction of the unpaid source budget, NOT a new
upper bound for original U3/U4 arithmetic counts. No hypothesis asserts
that remaining Theta payment or source gaps are small.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRetainedThetaCancellation

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedFeedbackOperator
open Part5OriginalH430ActualRetainedSelectedSameQEnvelope
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430ActualNextTableThetaFloorBridge
open Part5OriginalH430ActualThetaAbsolutePayment
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-- The signed physical Theta-1 correction at RETAINED winners only.
No quotient by equal products or replacement of the specified old cell. -/
def actualRetainedThetaCorrection (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ retainedLevel N n root tau p g,
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)

/-- The exact remaining signed correction: Buchstab and the ORIGINAL
bank winners, not all alternative bank slots. -/
def actualNonretainedThetaCorrection (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)

/-- Explicit NONNEGATIVE unpaid correction at selected NONretention
positions. Unlike the former all-action budget, no retention term occurs. -/
def actualNonretainedThetaPayment (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g ∪
      bankLevel N n root tau p g,
    |levelMark l| *
      |thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1| *
      |requestValue (iterate (g.val + 1))
          (levelOccurrence l).current|

theorem actual_nonretained_theta_payment_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ actualNonretainedThetaPayment N n root tau p g := by
  unfold actualNonretainedThetaPayment
  apply Finset.sum_nonneg
  intro l _
  positivity

/-- Exact disjoint action partition of the physical Theta correction.
The bank half still uses all and only the actual 106 winning slots. -/
theorem actual_theta_correction_retained_nonretained
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualThetaReadCorrection N n root tau p g =
      actualRetainedThetaCorrection N n root tau p g +
        actualNonretainedThetaCorrection N n root tau p g := by
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)
  have hPartition := actual_theta_correction_all_actions N n root tau p g
  have hBank := bank_level_sum_eq_original_106 N n root tau p g F
  change actualThetaReadCorrection N n root tau p g =
      (∑ l ∈ retainedLevel N n root tau p g, F l) +
        (∑ l ∈ buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g, F l)
  calc
    actualThetaReadCorrection N n root tau p g =
        (∑ l ∈ retainedLevel N n root tau p g, F l) +
        (∑ l ∈ buchstabLevel N n root tau p g, F l) +
        (∑ a : Original106Action,
          ∑ l ∈ selectedLevel N n root tau p g a, F l) := by
            simpa only [F] using hPartition
    _ = _ := by
      rw [← hBank, Finset.sum_union
        (buchstab_bank_disjoint N n root tau p g)]
      ring

/-- Retained new-table read plus its ENTIRE signed Theta correction
is exactly the original physical retained child value. The equality
uses the actual retained winner, original mark and genuine root Q. -/
theorem actual_retained_theta_cancels_to_child
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualRetainedRead N n root tau p g +
      actualRetainedThetaCorrection N n root tau p g =
        retainedLevelValue N n root tau p g := by
  rw [actual_retention_child_exact N n root tau p g]
  unfold actualRetainedRead actualRetainedThetaCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- There is no sign assumption on Theta-1 or the Q80 request. Every
remaining selected occurrence is paid once by its own absolute value. -/
theorem actual_nonretained_theta_correction_lower
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    -actualNonretainedThetaPayment N n root tau p g ≤
      actualNonretainedThetaCorrection N n root tau p g := by
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)
  have h :
      (∑ l ∈ buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g, -(F l)) ≤
      (∑ l ∈ buchstabLevel N n root tau p g ∪
          bankLevel N n root tau p g,
        |levelMark l| *
          |thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1| *
          |requestValue (iterate (g.val + 1))
              (levelOccurrence l).current|) := by
    apply Finset.sum_le_sum
    intro l _
    calc
      -(F l) ≤ |F l| := neg_le_abs _
      _ = |levelMark l| *
          |thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1| *
          |requestValue (iterate (g.val + 1))
              (levelOccurrence l).current| := by
            dsimp [F]
            rw [abs_mul, abs_mul]
  have hBound :
      -actualNonretainedThetaCorrection N n root tau p g ≤
        actualNonretainedThetaPayment N n root tau p g := by
    simpa only [actualNonretainedThetaCorrection,
      actualNonretainedThetaPayment, Finset.sum_neg_distrib] using h
  linarith only [hBound]

/-- The old ALL-ACTION absolute payment decomposes into a nonnegative
retained excess and this smaller selected-only payment. Thus removing
retention is never an artificial new positive budget. -/
theorem actual_nonretained_payment_le_all_action_payment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualNonretainedThetaPayment N n root tau p g ≤
      actualThetaAbsolutePayment N n root tau p g := by
  let G : Index N n root tau p g → ℝ := fun l =>
    |levelMark l| *
      |thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1| *
      |requestValue (iterate (g.val + 1))
          (levelOccurrence l).current|
  have hPartition := actual_theta_absolute_payment_all_actions
    N n root tau p g
  have hBank := bank_level_sum_eq_original_106 N n root tau p g G
  have hEq :
      actualThetaAbsolutePayment N n root tau p g =
        (∑ l ∈ retainedLevel N n root tau p g, G l) +
        actualNonretainedThetaPayment N n root tau p g := by
    calc
      actualThetaAbsolutePayment N n root tau p g =
          (∑ l ∈ retainedLevel N n root tau p g, G l) +
          (∑ l ∈ buchstabLevel N n root tau p g, G l) +
          (∑ a : Original106Action,
            ∑ l ∈ selectedLevel N n root tau p g a, G l) := by
              simpa only [G] using hPartition
      _ = _ := by
        unfold actualNonretainedThetaPayment
        rw [← hBank, Finset.sum_union
          (buchstab_bank_disjoint N n root tau p g)]
        ring
  have hRet : 0 ≤
      ∑ l ∈ retainedLevel N n root tau p g, G l := by
    apply Finset.sum_nonneg
    intro l _
    dsimp [G]
    positivity
  linarith only [hEq, hRet]

/-- Actual original floor/base source debt with retained Theta cancelled
EXACTLY against the retained physical child. Only bank/Buchstab Theta
deviations are charged, once per original generated Fin position.

The original previous-cell CLOSED-CELL hypothesis is preserved; the
remaining selected payment, count-owner and source gaps are still OPEN. -/
theorem actual_source_debt_without_retained_theta_payment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    actualBankSourceGap N n root tau p g +
        actualBuchstabSourceGap N n root tau p g ≤
      buchstabLevelError N n root tau p g +
        selectedBankBaseMass N n root tau p g +
        selectedBankFixedMass N n root tau p g F +
        selectedBankIdealFeedbackMass N n root tau p g +
        levelChildMass N n root tau p g -
        selectedBankRoundingLoss N n root tau p g -
        selectedBankPrimeChildMass N n root tau p g -
        retainedLevelValue N n root tau p g -
        actualSelectedOldRead N n root tau p g +
        actualNonretainedThetaPayment N n root tau p g := by
  have hSource := actual_source_debt_theta_floor_upper
    N n root tau p g F hN ht ht' hn hp hband hcells
  have hPartition := actual_theta_correction_retained_nonretained
    N n root tau p g
  have hRet := actual_retained_theta_cancels_to_child
    N n root tau p g
  have hPay := actual_nonretained_theta_correction_lower
    N n root tau p g
  unfold actualRetainedSelectedPhysicalRead at hSource
  linarith only [hSource, hPartition, hRet, hPay]

end
end ImbalancedChen.Part5OriginalH430ActualRetainedThetaCancellation
