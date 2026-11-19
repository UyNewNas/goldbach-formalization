import ImbalancedChen.P2CausalBankOccurrenceBinding

/-!
SOURCE ONLY. A generated mark's literal next history is identified with
its W1/W2 child occurrence. This is a finite tuple-fibre identity, not
an analytic licence, an all-roots admission, or an H247 comparison.
The inherited physical Q, ceiling, original child predicates and incoming
label are unchanged. No quotient by equal products is performed.
-/
namespace ImbalancedChen.P2CausalSuccessorOccurrence

noncomputable section
open Finset
open P2CausalPrimeHistorySource P2CausalMarkedThetaSupply
open P2CausalBankOccurrenceBinding
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildMarks
open P2EnhancedLowerPhysicalTransition
open Part5OriginalH430NativeQueryPaths
open scoped Classical BigOperators

def singleSuccessor (m : Mark) (rule : SingleRule) : Mark where
  rootRank := m.rootRank
  rank := m.rank + 1
  box := m.box
  history := .single m.history rule
  ceiling := m.ceiling
  coefficient := m.coefficient

def pairSuccessor (m : Mark) (bank : Fin 36) (piece : Fin 4) : Mark where
  rootRank := m.rootRank
  rank := m.rank + 2
  box := m.box
  history := .pair m.history bank piece
  ceiling := m.ceiling
  coefficient := m.coefficient

/-- One actual successor, with its edge scalar exactly once. -/
theorem single_successor_test (m : Mark) (N : ℕ) (nu : ℝ)
    (rule : SingleRule) (G : ℕ → ℝ) :
    parentTest (singleSuccessor m rule) N nu G =
      singleEdgeScalar rule * singleTest m N nu rule G := by
  unfold parentTest singleTest
  simp only [singleSuccessor, Mark.source, Mark.weight, History.scalar]
  rw [single_family_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro old _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- One actual pair successor: each of the four occurrences carries /5. -/
theorem pair_successor_test (m : Mark) (N : ℕ) (nu : ℝ)
    (bank : Fin 36) (piece : Fin 4) (G : ℕ → ℝ) :
    parentTest (pairSuccessor m bank piece) N nu G =
      pairTest m N nu bank piece G / 5 := by
  unfold parentTest pairTest
  simp only [pairSuccessor, Mark.source, Mark.weight, History.scalar]
  rw [pair_family_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro old _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem w1_single_successor (m : Mark) (N : ℕ) (nu : ℝ)
    (i : Fin 7) (j : Fin 10) (G : ℕ → ℝ) :
    parentTest (singleSuccessor m (.w1 i j)) N nu G =
      singleTest m N nu (.w1 i j) G / 2 := by
  rw [single_successor_test]
  simp only [singleEdgeScalar]
  ring

theorem w2_single_successor (m : Mark) (N : ℕ) (nu : ℝ)
    (bank : Fin 36) (piece : Fin 3) (G : ℕ → ℝ) :
    parentTest (singleSuccessor m (.w2 bank piece)) N nu G =
      singleTest m N nu (.w2 bank piece) G / 5 := by
  rw [single_successor_test]
  simp only [singleEdgeScalar]
  ring

/-- W1's unchanged parent and its one generated singleton occurrence. -/
theorem w1_components_are_successors (m : Mark) (N : ℕ) (nu : ℝ)
    (i : Fin 7) (j : Fin 10) (G : StepShape → ℕ → ℝ) :
    componentSum (.inl (i,j)) (componentTest m N nu G) =
      parentTest m N nu (G (.w1Fixed i j)) +
      parentTest (singleSuccessor m (.w1 i j)) N nu (G (.w1Singleton i j)) := by
  rw [W1_actual_occurrences, w1_single_successor]

/-- W2 has separate 4:1 parent entries, three labelled singletons, and
four labelled pairs. No two occurrences are merged by equal products. -/
theorem w2_components_are_successors (m : Mark) (N : ℕ) (nu : ℝ)
    (bank : Fin 36) (G : StepShape → ℕ → ℝ) :
    componentSum (.inr bank) (componentTest m N nu G) =
      (4 * parentTest m N nu (G (.w2Fixed bank true)) +
        parentTest m N nu (G (.w2Fixed bank false))) / 5 +
      (∑ piece : Fin 3, parentTest (singleSuccessor m (.w2 bank piece)) N nu
        (G (.w2Singleton bank piece))) +
      (∑ piece : Fin 4, parentTest (pairSuccessor m bank piece) N nu
        (G (.w2Pair bank piece))) := by
  rw [W2_actual_occurrences]
  simp_rw [w2_single_successor, pair_successor_test]
  simp only [← Finset.sum_div]
  ring

end
end ImbalancedChen.P2CausalSuccessorOccurrence
