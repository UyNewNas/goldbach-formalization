import ImbalancedChen.Part5OriginalH430ActualNextTableSignedSourceResidual
import ImbalancedChen.Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-!
P5.6 / h34 — literal new-table request, physical Theta scaling and the
ORIGINAL 106-bank integer-floor/base ledger, at the SAME real generation.

The preceding next-table packet uses levelMark * requestValue. The original
arithmetic read/edge defect uses levelMark * thetaAtom * requestValue.
Those are not interchangeable. The correction below is the exact
signed, positionwise (thetaAtom - 1) factor, at the real root-specific Q.

The original floor/base conditional upper step is transferred to the
literal next-table with that correction RETAINED, and then to the
two genuine unpaid bank/Buchstab new-table source gaps. No sign is
assigned to the Theta correction or source gaps. The old-cell
closed-cell premise remains an actual unproved predecessor induction
obligation, not a granted U3/U4 count theorem.

SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualNextTableThetaFloorBridge

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestAllActionPartition
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430ActualNextTableSignedSourceResidual
open Part5OriginalH430SelectedBankGlobalFloorBaseLedger

/-- The EXACT signed change from the literal unscaled g+1 request
read to the manuscript's physical Theta-weighted edge read. All
original generated Fin positions are retained; in particular, this
is not a free scalar error or an assumed positive payment. -/
def actualThetaReadCorrection (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l : Index N n root tau p g,
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)

/-- The two actual generation-g+1 reads are related by the
full signed physical Theta correction, not by an unjustified
identification of their normalizations. -/
theorem actual_weighted_new_table_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    levelReadMass N n root tau p g =
      actualNewTableRead N n root tau p g +
        actualThetaReadCorrection N n root tau p g := by
  unfold levelReadMass readTerm actualNewTableRead
    actualThetaReadCorrection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- The physical normalization correction is charged at the ACTUAL
retention, Buchstab and 106-bank winning positions. Unresolved
requests have zero literal g+1 value, even with signed Theta-1.
This preserves the specified-cell/scalar distinction and
the multiplicities of equal physical products. -/
theorem actual_theta_correction_all_actions
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualThetaReadCorrection N n root tau p g =
      (∑ l ∈ retainedLevel N n root tau p g,
        levelMark l *
          ((thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1) *
            requestValue (iterate (g.val + 1))
              (levelOccurrence l).current)) +
      (∑ l ∈ buchstabLevel N n root tau p g,
        levelMark l *
          ((thetaAtom N (rootQ N n root tau p)
              (parentProduct (levelOccurrence l).current.old) - 1) *
            requestValue (iterate (g.val + 1))
              (levelOccurrence l).current)) +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          levelMark l *
            ((thetaAtom N (rootQ N n root tau p)
                (parentProduct (levelOccurrence l).current.old) - 1) *
              requestValue (iterate (g.val + 1))
                (levelOccurrence l).current)) := by
  let F : Index N n root tau p g → ℝ := fun l =>
    levelMark l *
      ((thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) - 1) *
        requestValue (iterate (g.val + 1))
          (levelOccurrence l).current)
  have hfull :
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
  rw [hfull]
  exact resolved_level_sum_all_actions N n root tau p g F

/-- The original genuine physical one-generation inequality after
paying the EXACT integer feedback floors. This is a bridge for the
literal unweighted g+1 request, not a new count-source permission:
the signed Theta correction stays on the LEFT, as do the true
floor credit and original selected strict-prime children.
Only the fixed prior-cell premise is assumed, explicitly. -/
theorem actual_new_table_theta_floor_upper
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    actualNewTableRead N n root tau p g +
        actualThetaReadCorrection N n root tau p g -
        levelChildMass N n root tau p g +
        selectedBankRoundingLoss N n root tau p g +
        selectedBankPrimeChildMass N n root tau p g ≤
      buchstabLevelError N n root tau p g +
        selectedBankBaseMass N n root tau p g +
        selectedBankFixedMass N n root tau p g F +
        selectedBankIdealFeedbackMass N n root tau p g := by
  have h := actual_one_generation_base_feedback_floor_upper
    N n root tau p g F hN ht ht' hn hp hband hcells
  rw [actual_weighted_new_table_exact N n root tau p g] at h
  exact h

/-- The real bank AND Buchstab next-table source gaps now have one
explicit signed upper ledger in terms of the original physical
Theta correction, true child masses, actual base/fixed/ideal
feedback and the SUBTRACTED nonnegative Q80 floor payment.

This is not a numerical small-gap result: all right-side masses
still require legitimate base/seed/CLOSED-CELL arithmetic control.
Crucially neither unscaled request read nor the signed Theta-1
term is incorrectly relabelled as original selected q-count. -/
theorem actual_source_debt_theta_floor_upper
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
        actualThetaReadCorrection N n root tau p g -
        actualRetainedSelectedPhysicalRead N n root tau p g := by
  have h := actual_new_table_theta_floor_upper N n root tau p g F
    hN ht ht' hn hp hband hcells
  rw [actual_new_table_eq_retained_physical_plus_source_gaps] at h
  linarith only [h]

end
end ImbalancedChen.Part5OriginalH430ActualNextTableThetaFloorBridge
