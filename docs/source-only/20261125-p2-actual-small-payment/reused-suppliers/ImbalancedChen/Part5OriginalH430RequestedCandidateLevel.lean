import ImbalancedChen.Part5OriginalH430RequestedAllFeedbackBudget

/-!
The remaining bank-side scalar step of the manuscript-local CLOSED-CELL
induction, on the ACTUAL generated winner level. SOURCE ONLY / UNCOMPILED.

This lifts the pre-existing roundDecision candidate upper bound to every
list-position occurrence. It does not assume that a generated request is
an original U3/U4 prime-count parent, or that the unnormalized request
value is the original arithmetic count. Those source/count obligations
remain OPEN.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedCandidateLevel

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalH430PhysicalRoots Part5OriginalH430BankSlotTargets
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply

/-- The chosen bank's updated-table READ at its actual level occurrence.
No scalar-owner replacement for specified-cell requests occurs. -/
def markedBankRead (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a,
    levelMark l * requestValue (iterate (g.val+1)) (levelOccurrence l).current

/-- Its literal base + fixed + feedback candidate computed from the
PREVIOUS array, at the same selected action and the same path weight. -/
def markedBankCandidate (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a,
    levelMark l *
      (baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a)

/-- No new count licence: each actual selected read satisfies the
original finite roundDecision bound, with its original positive mark. -/
theorem markedBankRead_le_candidate (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (a : Original106Action) :
    markedBankRead N n root tau p g a ≤
      markedBankCandidate N n root tau p g a := by
  unfold markedBankRead markedBankCandidate
  apply Finset.sum_le_sum
  intro l hl
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  have hc : requestValue (iterate (g.val+1)) (levelOccurrence l).current ≤
      baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a := by
    simpa only [action_slot] using selected_bank_candidate_upper hi
  exact mul_le_mul_of_nonneg_left hc (mark_pos _).le

/-- Summation keeps all distinct occurrences and pays only the chosen
bank. The Buchstab and retained choices are disjoint and excluded. -/
theorem all_markedBankRead_le_candidate (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    (∑ a : Original106Action, markedBankRead N n root tau p g a) ≤
      (∑ a : Original106Action, markedBankCandidate N n root tau p g a) :=
  Finset.sum_le_sum (fun a _ => markedBankRead_le_candidate N n root tau p g a)

end
end ImbalancedChen.Part5OriginalH430RequestedCandidateLevel
