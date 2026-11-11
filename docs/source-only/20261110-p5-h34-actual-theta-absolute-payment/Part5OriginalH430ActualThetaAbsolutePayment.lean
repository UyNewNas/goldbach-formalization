import ImbalancedChen.Part5OriginalH430ActualNextTableThetaFloorBridge

/-!
P5.6 / h34 — explicit ABSOLUTE physical Theta-normalization debt.

The actual new-table / original Theta-weighted consumer identity contains
the signed occurrence sum mark*(Theta-1)*requestValue. It cannot be
silently discarded or given a favorable sign. This packet introduces
its literal, noncancelling absolute payment, preserving every actual
Fin position, original physical parent Q, previous/next table index,
scalar-versus-specified-cell selection, and all repeated occurrences.

The true signed correction is bounded by this *explicit* finite sum,
and the existing conditional base/floor/source-gap inequality is
transferred with precisely ONE additional unpaid positive mass.
This is a quantified reduction, NOT a bound on this mass by Theta,
and NOT a U3/U4 CLOSED-CELL arithmetic count induction.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualThetaAbsolutePayment

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430ActualNextTableThetaFloorBridge
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-- No sign, cancellation, normalized-Q shortcut, or uniformity assumption:
this is the nonnegative sum of the LITERAL Theta-1 correction at
the real history positions, including multiplicities. -/
def actualThetaAbsolutePayment (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    |levelMark l| *
      |thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1| *
      |requestValue (iterate (g.val + 1))
          (levelOccurrence l).current|

theorem actual_theta_absolute_payment_nonneg
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    0 ≤ actualThetaAbsolutePayment N n root tau p g := by
  unfold actualThetaAbsolutePayment
  apply Finset.sum_nonneg
  intro l _
  positivity

/-- Triangle inequality at the *entire original Fin-list*, not at
a quotient by physical products or catalog names. In particular, the
actual signed normalization correction may be either sign. -/
theorem actual_theta_correction_abs_le_payment
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    |actualThetaReadCorrection N n root tau p g| ≤
      actualThetaAbsolutePayment N n root tau p g := by
  let T : Index N n root tau p g → ℝ := fun l =>
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)
  have hUpper :
      (∑ l : Index N n root tau p g, T l) ≤
        ∑ l : Index N n root tau p g, |T l| := by
    apply Finset.sum_le_sum
    intro l _
    exact le_abs_self (T l)
  have hLower :
      -(∑ l : Index N n root tau p g, T l) ≤
        ∑ l : Index N n root tau p g, |T l| := by
    calc
      -(∑ l : Index N n root tau p g, T l) =
          ∑ l : Index N n root tau p g, -(T l) := by
            simp only [Finset.sum_neg_distrib]
      _ ≤ ∑ l : Index N n root tau p g, |T l| := by
        apply Finset.sum_le_sum
        intro l _
        exact neg_le_abs (T l)
  have hAbs :
      |∑ l : Index N n root tau p g, T l| ≤
        ∑ l : Index N n root tau p g, |T l| :=
    abs_le.mpr ⟨hLower, hUpper⟩
  calc
    |actualThetaReadCorrection N n root tau p g| =
        |∑ l : Index N n root tau p g, T l| := rfl
    _ ≤ ∑ l : Index N n root tau p g, |T l| := hAbs
    _ = actualThetaAbsolutePayment N n root tau p g := by
      unfold actualThetaAbsolutePayment
      apply Finset.sum_congr rfl
      intro l _
      dsimp [T]
      rw [abs_mul, abs_mul]
      ring

/-- BOTH directions are licensed, without assuming that physical
Theta is above or below one. In particular this pays the negative
correction in the original one-sided source debt ledger. -/
theorem actual_theta_correction_signed_interval
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    -actualThetaAbsolutePayment N n root tau p g ≤
        actualThetaReadCorrection N n root tau p g ∧
      actualThetaReadCorrection N n root tau p g ≤
        actualThetaAbsolutePayment N n root tau p g :=
  abs_le.mp (actual_theta_correction_abs_le_payment N n root tau p g)

/-- Decompose the NONCANCELLING payment among the actual resolved
retention, Buchstab and 106 bank winners. Non-resolved positions
have zero request value. No physical-product quotient or new
choice of action occurs in this sum. -/
theorem actual_theta_absolute_payment_all_actions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualThetaAbsolutePayment N n root tau p g =
      (∑ l ∈ retainedLevel N n root tau p g,
        |levelMark l| *
          |thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1| *
          |requestValue (iterate (g.val + 1))
              (levelOccurrence l).current|) +
      (∑ l ∈ buchstabLevel N n root tau p g,
        |levelMark l| *
          |thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1| *
          |requestValue (iterate (g.val + 1))
              (levelOccurrence l).current|) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          |levelMark l| *
            |thetaAtom N (rootQ N n root tau p)
                (parentProduct (levelOccurrence l).current.old) - 1| *
            |requestValue (iterate (g.val + 1))
                (levelOccurrence l).current|) := by
  let F : Index N n root tau p g → ℝ := fun l =>
    |levelMark l| *
      |thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1| *
      |requestValue (iterate (g.val + 1))
          (levelOccurrence l).current|
  have hFull :
      (∑ l : Index N n root tau p g, F l) =
        ∑ l ∈ resolvedLevel N n root tau p g, F l := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l ∈ resolvedLevel N n root tau p g
    · simp [hl]
    · have hz := unresolved_level_value_zero N n root tau p g l hl
      simp [F, hl, hz]
  change (∑ l : Index N n root tau p g, F l) =
    (∑ l ∈ retainedLevel N n root tau p g, F l) +
      (∑ l ∈ buchstabLevel N n root tau p g, F l) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a, F l)
  rw [hFull]
  exact resolved_level_sum_all_actions N n root tau p g F

/-- A genuine, always NONNEGATIVE correction budget in the original
conditional floor/base ledger. Previously the right side contained
-thetaCorrection with unknown sign. It is now bounded by a precisely
specified positive mass that still needs original U3/U4 count control.
The preceding closed-cell hypothesis is NOT discharged here. -/
theorem actual_source_debt_theta_absolute_payment_upper
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
        actualRetainedSelectedPhysicalRead N n root tau p g +
        actualThetaAbsolutePayment N n root tau p g := by
  have hSource := actual_source_debt_theta_floor_upper
    N n root tau p g F hN ht ht' hn hp hband hcells
  have hTheta :=
    (actual_theta_correction_signed_interval N n root tau p g).1
  linarith only [hSource, hTheta]

end
end ImbalancedChen.Part5OriginalH430ActualThetaAbsolutePayment
