import ImbalancedChen.Part5OriginalH430ActualRequestNonbankQuantitative
import ImbalancedChen.Part5OriginalH430RequestedLevelBankSupply

/-!
P5.6 / h34 -- one PRE-N threshold for the actual winning Buchstab
and all 106 selected-bank action families, at the SAME generated
request history and the SAME root-dependent physical Q.

This combines two existing, independently quantified manuscript-local
suppliers. It does NOT add 5 and 12 to a single winner, replace a
specified-cell read by the scalar closed-min owner, turn an unchosen
bank alternative into an occurrence, or assert that generated requests
already own the complete original U3/U4 arithmetic selected source.

The selected total absolute/applied error is bounded against the SUM
of the actual distinct action-specific Theta masses, and the genuine
row-mass envelope remains 5*BuchstabTheta + 12*bankTheta.
Retention stays the exact previously supplied selected-cell read;
it is not given a fictitious row error.

SOURCE ONLY / UNCOMPILED / UNEVALUATED. FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430UnifiedWinningActionBudget

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestNonbankQuantitative

/-- The actual resolver's one-generation Buchstab and all 106 bank
suppliers can use ONE threshold before N, root, precision, prime,
generation and selected action are fixed.

Every total uses generated Fin LIST positions, so repeated physical
products are not quotiented. The bank applied error has already
absorbed the W1/W2 fixed-cell comparison in its original supplier.

This is a quantitative one-step error/row budget, NOT the missing
CLOSED-CELL count induction or the original U3/U4 owner theorem. -/
theorem uniform_actual_winning_action_budget
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
        ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
          physicalPrime N p ∈ rootBand root →
          ∀ g : Fin 430,
            ((∑ l : Index N n root tau p g,
                levelMark l * requestValue (iterate (g.val + 1))
                  (levelOccurrence l).current) ≤
              actualRetainedRead N n root tau p g +
              actualBuchstabRead N n root tau p g +
              (∑ a : Original106Action,
                markedBankCandidate N n root tau p g a)) ∧
            actualBuchstabError N n root tau p g ≤
              epsilon * actualBuchstabTheta N n root tau p g ∧
            (∀ b : RowAtom,
              0 ≤ actualBuchstabRow N n root tau p g b) ∧
            (∑ b : RowAtom, actualBuchstabRow N n root tau p g b) ≤
              5 * actualBuchstabTheta N n root tau p g ∧
            (actualBuchstabTheta N n root tau p g = 0 →
              actualBuchstabError N n root tau p g = 0 ∧
              ∀ b : RowAtom, actualBuchstabRow N n root tau p g b = 0) ∧
            (∀ a : Original106Action,
              levelError N n root tau p g a ≤
                epsilon * levelTheta N n root tau p g a ∧
              levelAppliedError N n root tau p g a ≤
                epsilon * levelTheta N n root tau p g a ∧
              (∀ b : RowAtom, 0 ≤ levelRow N n root tau p g a b) ∧
              (∑ b : RowAtom, levelRow N n root tau p g a b) ≤
                12 * levelTheta N n root tau p g a ∧
              (levelTheta N n root tau p g a = 0 →
                levelError N n root tau p g a = 0 ∧
                ∀ b : RowAtom, levelRow N n root tau p g a b = 0)) ∧
            (actualBuchstabError N n root tau p g +
              (∑ a : Original106Action,
                levelAppliedError N n root tau p g a) ≤
              epsilon * (actualBuchstabTheta N n root tau p g +
                (∑ a : Original106Action,
                  levelTheta N n root tau p g a))) ∧
            ((∑ b : RowAtom, actualBuchstabRow N n root tau p g b) +
              (∑ a : Original106Action,
                ∑ b : RowAtom, levelRow N n root tau p g a b) ≤
              5 * actualBuchstabTheta N n root tau p g +
                12 * (∑ a : Original106Action,
                  levelTheta N n root tau p g a)) := by
  obtain ⟨Tnon, hTnon, hNon⟩ :=
    uniform_actual_nonbank_quantitative he
  obtain ⟨Tbank, hTbank, hBank⟩ :=
    uniform_level_bank_supply he
  refine ⟨max Tnon Tbank,
    le_trans hTnon (Nat.le_max_left Tnon Tbank), ?_⟩
  intro N hN n root tau htau0 htau12 hprecision p hp hband g
  have hNnon : Tnon ≤ N :=
    le_trans (Nat.le_max_left Tnon Tbank) hN
  have hNbank : Tbank ≤ N :=
    le_trans (Nat.le_max_right Tnon Tbank) hN
  obtain ⟨hRead, hBError, hBRow, hBMass, hBZero⟩ :=
    hNon N hNnon n root tau htau0 htau12 hprecision p hp hband g
  have hBankAt :=
    hBank N hNbank n root tau htau0 htau12 hprecision p hp hband g
  have hAppliedSum :
      (∑ a : Original106Action,
          levelAppliedError N n root tau p g a) ≤
        epsilon * (∑ a : Original106Action,
          levelTheta N n root tau p g a) := by
    calc
      _ ≤ ∑ a : Original106Action,
          epsilon * levelTheta N n root tau p g a := by
            apply Finset.sum_le_sum
            intro a _
            exact (hBankAt a).2.1
      _ = _ := by rw [Finset.mul_sum]
  have hBankMassSum :
      (∑ a : Original106Action,
          ∑ b : RowAtom, levelRow N n root tau p g a b) ≤
        12 * (∑ a : Original106Action,
          levelTheta N n root tau p g a) := by
    calc
      _ ≤ ∑ a : Original106Action,
          12 * levelTheta N n root tau p g a := by
            apply Finset.sum_le_sum
            intro a _
            exact (hBankAt a).2.2.2.1
      _ = _ := by rw [Finset.mul_sum]
  refine ⟨hRead, hBError, hBRow, hBMass, hBZero,
    hBankAt, ?_, ?_⟩
  · calc
      actualBuchstabError N n root tau p g +
          (∑ a : Original106Action,
            levelAppliedError N n root tau p g a) ≤
        epsilon * actualBuchstabTheta N n root tau p g +
          epsilon * (∑ a : Original106Action,
            levelTheta N n root tau p g a) :=
              add_le_add hBError hAppliedSum
      _ = _ := by ring
  · exact add_le_add hBMass hBankMassSum

end
end ImbalancedChen.Part5OriginalH430UnifiedWinningActionBudget
