import ImbalancedChen.Part5OriginalH430UnifiedWinningActionBudget
import ImbalancedChen.Part5OriginalH430ActualFixedClosedCell

/-!
P5.6 / h34: causal prefixes of actual generated 430-level request positions.
The SAME pre-N threshold controls the winning-action absolute/applied error,
Buchstab and bank row mass, and the actual fixed-read CLOSED-CELL step.

The predecessor CLOSED-CELL bound is required ONLY at the generations
belonging to this prefix, and is NOT proved or assumed for all 430 levels.
The theorem preserves original fixed-cell versus scalar reads and distinct
Fin history occurrences. No original arithmetic q/tag count closure,
non-edge rejection payment, base/seed induction or new external input.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430PrefixClosedCellWinningBudget
noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430UnifiedWinningActionBudget

/-- The literal, non-wrapping 430-generation prefix. The Fin index is a
generation, not a physical catalog label, source q, or selected action. -/
def generationPrefix (m : ℕ) : Finset (Fin 430) :=
  Finset.univ.filter (fun g => g.val < m)

theorem generationPrefix_zero :
    generationPrefix 0 = ∅ := by
  ext g
  simp [generationPrefix]

theorem generationPrefix_full :
    generationPrefix 430 = Finset.univ := by
  ext g
  simp [generationPrefix, g.isLt]

theorem generationPrefix_mono {m k : ℕ} (hmk : m ≤ k) :
    generationPrefix m ⊆ generationPrefix k := by
  intro g hg
  have hgm : g.val < m := (Finset.mem_filter.mp hg).2
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ g, lt_of_lt_of_le hgm hmk⟩

/-- At EVERY causal prefix, the actual chosen Buchstab and bank errors
are bounded on the same finite generated-level list positions by one
epsilon selected before N. The additional signed request-minus-child
bound uses ONLY the predecessor CLOSED-CELL fact for generations in that
prefix, so it is an induction-step consumer, NOT the induction base or
the full arithmetic count theorem.

The original 5-Theta Buchstab and 12-Theta bank mass budgets remain
separate. Only winning bank actions are included; the specified-cell
read is never exchanged for a scalar owner. -/
theorem uniform_actual_prefix_closed_cell_winning_budget
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
        ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
          physicalPrime N p ∈ rootBand root →
          ∀ m : ℕ, m ≤ 430 →
          ∀ F : ℝ → ℝ,
            (∀ g : Fin 430, g ∈ generationPrefix m →
              ∀ (i : Fin 200) (s : ℝ), s ∈ queryCell i →
                floorValue (iterate g.val true) i ≤ F s) →
            ( (∑ g ∈ generationPrefix m,
                (levelReadMass N n root tau p g -
                 levelChildMass N n root tau p g)) ≤
              ∑ g ∈ generationPrefix m,
                (epsilon * actualBuchstabTheta N n root tau p g +
                 (∑ a : Original106Action,
                   ∑ l ∈ selectedLevel N n root tau p g a,
                     bankFixedReferenceGap N n root tau p g F a l)) ) ∧
            ( (∑ g ∈ generationPrefix m,
                (actualBuchstabError N n root tau p g +
                 (∑ a : Original106Action,
                   levelAppliedError N n root tau p g a))) ≤
              epsilon * (∑ g ∈ generationPrefix m,
                (actualBuchstabTheta N n root tau p g +
                 (∑ a : Original106Action,
                   levelTheta N n root tau p g a))) ) ∧
            ( (∑ g ∈ generationPrefix m,
                ((∑ b : RowAtom,
                   actualBuchstabRow N n root tau p g b) +
                 (∑ a : Original106Action,
                   ∑ b : RowAtom,
                     levelRow N n root tau p g a b))) ≤
              ∑ g ∈ generationPrefix m,
                (5 * actualBuchstabTheta N n root tau p g +
                 12 * (∑ a : Original106Action,
                   levelTheta N n root tau p g a)) ) := by
  obtain ⟨Tf, hTf, hFixed⟩ :=
    uniform_actual_one_generation_fixed_upper he
  obtain ⟨Ta, hTa, hAction⟩ :=
    uniform_actual_winning_action_budget he
  refine ⟨max Tf Ta, le_trans hTf (Nat.le_max_left Tf Ta), ?_⟩
  intro N hN n root tau htau0 htau12 hprecision p hp hband
    m _ F hclosed
  have hNf : Tf ≤ N :=
    le_trans (Nat.le_max_left Tf Ta) hN
  have hNa : Ta ≤ N :=
    le_trans (Nat.le_max_right Tf Ta) hN
  have hAt (g : Fin 430) :
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
    obtain ⟨_, _, _, _, _, _, hErr, hRows⟩ :=
      hAction N hNa n root tau htau0 htau12 hprecision
        p hp hband g
    exact ⟨hErr, hRows⟩
  constructor
  · apply Finset.sum_le_sum
    intro g hg
    exact hFixed N hNf n root tau htau0 htau12 hprecision
      p hp hband g F (hclosed g hg)
  constructor
  · calc
      (∑ g ∈ generationPrefix m,
        (actualBuchstabError N n root tau p g +
         (∑ a : Original106Action,
           levelAppliedError N n root tau p g a))) ≤
        ∑ g ∈ generationPrefix m,
          epsilon * (actualBuchstabTheta N n root tau p g +
            (∑ a : Original106Action,
              levelTheta N n root tau p g a)) := by
                apply Finset.sum_le_sum
                intro g _
                exact (hAt g).1
      _ = epsilon * (∑ g ∈ generationPrefix m,
            (actualBuchstabTheta N n root tau p g +
             (∑ a : Original106Action,
               levelTheta N n root tau p g a))) := by
            rw [Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro g _
    exact (hAt g).2

end
end ImbalancedChen.Part5OriginalH430PrefixClosedCellWinningBudget
