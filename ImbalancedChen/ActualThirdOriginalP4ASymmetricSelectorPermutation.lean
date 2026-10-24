import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
import ImbalancedChen.ActualThirdOriginalP4ASymmetricBranchPermutation

/-! SOURCEONLY / UNCOMPILED / OPEN30.
Direct adapter to the ordinary selector's actual integer branch/root tests and
rational plane_range score. The source enumeration order is not permuted. -/
namespace ImbalancedChen.OriginalThirdP4ASymmetricSelectorPermutationSourceOnly

noncomputable section
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4ASymmetricBranchPermutationSourceOnly

def swapIntegerXY (v : Fin 3 → ℤ) : Fin 3 → ℤ := ![v 1, v 0, v 2]

def swapCandidate : Candidate → Candidate
  | .base => .base
  | .tent s k => .tent (swapSum s) k

theorem swapIntegerXY_involutive (v : Fin 3 → ℤ) :
    swapIntegerXY (swapIntegerXY v) = v := by
  funext i
  fin_cases i <;> simp [swapIntegerXY]

theorem swapCandidate_involutive (p : Candidate) :
    swapCandidate (swapCandidate p) = p := by
  cases p with
  | base => rfl
  | tent s k => simp only [swapCandidate, swapSum_involutive]

theorem rawSum_swap (s : TentSum) (v : Fin 3 → ℤ) :
    rawSum (swapSum s) (swapIntegerXY v) = rawSum s v := by
  cases s <;> simp [rawSum, swapSum, swapIntegerXY,
    literalTentX, literalTentY, literalTentZ, add_comm]

theorem deltaNumerator_swap (D : ℤ) (s : TentSum) (v : Fin 3 → ℤ) :
    deltaNumerator D (swapSum s) (swapIntegerXY v) = deltaNumerator D s v := by
  simp only [deltaNumerator, rawSum_swap]

theorem branchTest_swap_iff (lo hi : Fin 3 → ℤ) (D : ℤ)
    (s : TentSum) (k : TentSide) :
    branchTest (swapIntegerXY lo) (swapIntegerXY hi) D (swapSum s) k ↔
      branchTest lo hi D s k := by
  cases k <;> simp only [branchTest, deltaNumerator_swap]

theorem rootTest_swap_iff (lo hi : Fin 3 → ℤ) (D T : ℤ) (p : Candidate) :
    rootTest (swapIntegerXY lo) (swapIntegerXY hi) D T (swapCandidate p) ↔
      rootTest lo hi D T p := by
  cases p with
  | base => simp [rootTest, swapCandidate, swapIntegerXY]
  | tent s k => cases k <;> simp only [swapCandidate, rootTest, rawSum_swap]

theorem rangeLow_swap (lo hi : Fin 3 → ℤ) (D : ℤ) (p : Candidate) :
    rangeLow (swapIntegerXY lo) (swapIntegerXY hi) D (swapCandidate p) =
      rangeLow lo hi D p := by
  cases p with
  | base => simp [rangeLow, swapCandidate, swapIntegerXY]
  | tent s k => cases k <;> simp only [swapCandidate, rangeLow, rawSum_swap]

theorem rangeHigh_swap (lo hi : Fin 3 → ℤ) (D : ℤ) (p : Candidate) :
    rangeHigh (swapIntegerXY lo) (swapIntegerXY hi) D (swapCandidate p) =
      rangeHigh lo hi D p := by
  cases p with
  | base => simp [rangeHigh, swapCandidate, swapIntegerXY]
  | tent s k => cases k <;> simp only [swapCandidate, rangeHigh, rawSum_swap]

theorem sourceScore_swap (lo hi : Fin 3 → ℤ) (D : ℤ) (p : Candidate) :
    sourceScore (swapIntegerXY lo) (swapIntegerXY hi) D (swapCandidate p) =
      sourceScore lo hi D p := by
  simp only [sourceScore, rangeLow_swap, rangeHigh_swap]

theorem symmetric_integer_endpoint (a c : ℤ) :
    swapIntegerXY (![a, a, c] : Fin 3 → ℤ) = ![a, a, c] := by
  funext i
  fin_cases i <;> simp [swapIntegerXY]

/-- This is the actual rational score used by originalMinorant, with no
physical/rational score identification or numerical bound as a premise. -/
theorem symmetric_literal_score_swap (x0 x1 z0 z1 D : ℤ) (p : Candidate) :
    sourceScore ![x0, x0, z0] ![x1, x1, z1] D (swapCandidate p) =
      sourceScore ![x0, x0, z0] ![x1, x1, z1] D p := by
  simpa only [symmetric_integer_endpoint] using
    sourceScore_swap (![x0, x0, z0] : Fin 3 → ℤ) ![x1, x1, z1] D p

theorem symmetric_literal_paired_ties (x0 x1 z0 z1 D : ℤ) (k : TentSide) :
    sourceScore ![x0, x0, z0] ![x1, x1, z1] D (.tent .x k) =
        sourceScore ![x0, x0, z0] ![x1, x1, z1] D (.tent .y k) ∧
    sourceScore ![x0, x0, z0] ![x1, x1, z1] D (.tent .xz k) =
        sourceScore ![x0, x0, z0] ![x1, x1, z1] D (.tent .yz k) := by
  constructor
  · exact (symmetric_literal_score_swap x0 x1 z0 z1 D (.tent .x k)).symm
  · exact (symmetric_literal_score_swap x0 x1 z0 z1 D (.tent .xz k)).symm

/-- Root-filtered tent membership is preserved. This uses the selector's
proved membership characterization, rather than a new list enumeration. -/
theorem symmetric_literal_tent_mem_swap_iff (x0 x1 z0 z1 D T : ℤ)
    (s : TentSum) (k : TentSide) :
    Candidate.tent (swapSum s) k ∈
        sourceCandidates ![x0, x0, z0] ![x1, x1, z1] D T ↔
      Candidate.tent s k ∈
        sourceCandidates ![x0, x0, z0] ![x1, x1, z1] D T := by
  have hb := branchTest_swap_iff (![x0, x0, z0] : Fin 3 → ℤ)
    ![x1, x1, z1] D s k
  have hr := rootTest_swap_iff (![x0, x0, z0] : Fin 3 → ℤ)
    ![x1, x1, z1] D T (.tent s k)
  simp only [symmetric_integer_endpoint, swapCandidate] at hb hr
  rw [tent_mem_candidates_iff, tent_mem_candidates_iff, hb, hr]

end
end ImbalancedChen.OriginalThirdP4ASymmetricSelectorPermutationSourceOnly
