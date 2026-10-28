import ImbalancedChen.P1HistoricalFifthCommonSourceContribution
import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The partition now acts on the independent ORIGINAL finite Rosser residual,
not on an invented rho/profile identification. Both strict own-cube gates,
the actual cap, complete fifth history and its actual fourth ancestor stay
inside literalTupleDifference. No next candidate is filtered by admission.
Carrier-to-physical-rho telescoping is a separate independently owned step.
-/
namespace ImbalancedChen.P1HistoricalFifthCommonLiteralContribution
noncomputable section
open Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1OriginalFifthRawBoxSelectorEquivalence
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthCommonPolicyInputs
open P1HistoricalFifthCommonSourceContribution
open P1CorrectedFifthCausalTupleDictionary

/-- The original row formula, with its REAL common fourth parent. It is a
local source level, not a new similarly named global policy. -/
def rowLevel5 (i : ArchiveIndex) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega : ℝ) (N : ℕ)
    (pre : List ℕ) : ℝ :=
  (N : ℝ) ^ max (P5OriginalCommonRefinedConstructor.exponent4
    (sourceData rows4 licensed4 e q chi omega) (N : ℝ) (rosserAncestor 4 pre))
    (rawCandidate (e : ℝ) (archiveRow i) (primeHistoryLogCoordinates (N : ℝ) 5 pre))

def indexedLiteralTupleDifference (i : ArchiveIndex) (rows4 : Finset ProducerRow)
    (licensed4 : ProducerRow → Prop) (e : ℚ) (q : ℕ) (chi omega : ℝ)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  if actualPrimeTupleLog N p ∈ sourceCellDomain i e q chi omega then
    literalTupleDifference
      (P5OriginalCommonRefinedConstructor.level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (rowLevel5 i rows4 licensed4 e q chi omega N) N cap p
  else 0

theorem actual_literal_on_source
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) (i : ArchiveIndex)
    (hi : actualPrimeTupleLog N p ∈ sourceCellDomain i e q chi omega) :
    literalTupleDifference
      (P5OriginalCommonRefinedConstructor.level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (P5OriginalCommonRefinedConstructor.level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      N cap p = indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p := by
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have ht : primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) ∈
      sourceCellDomain i e q chi omega := by simpa only [tupleHistory_log] using hi
  have hcap := common_exponent5_eq_unique_source rows4 licensed4 e q chi omega
    (N : ℝ) (tupleHistory p) hlen i ht
  have hlevel : P5OriginalCommonRefinedConstructor.level5
      (sourceData rows4 licensed4 e q chi omega) (N : ℝ) (tupleHistory p) =
        rowLevel5 i rows4 licensed4 e q chi omega N (tupleHistory p) := by
    exact congrArg (fun a : ℝ => (N : ℝ) ^ a) hcap
  simp only [indexedLiteralTupleDifference, if_pos hi, literalTupleDifference,
    actualOwnCubeGatedMinusDensity, hlevel]

theorem actual_literal_zero_off_sources
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ i : ArchiveIndex, actualPrimeTupleLog N p ∉ sourceCellDomain i e q chi omega) :
    literalTupleDifference
      (P5OriginalCommonRefinedConstructor.level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (P5OriginalCommonRefinedConstructor.level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      N cap p = 0 := by
  have hlen : (tupleHistory p).length = 5 := by simp [tupleHistory]
  have ht : ∀ i : ArchiveIndex, primeHistoryLogCoordinates (N : ℝ) 5 (tupleHistory p) ∉
      sourceCellDomain i e q chi omega := by simpa only [tupleHistory_log] using hout
  have hcap := common_exponent5_eq_seed_off_sources rows4 licensed4 e q chi omega
    (N : ℝ) (tupleHistory p) hlen ht
  have hlevel : P5OriginalCommonRefinedConstructor.level5
      (sourceData rows4 licensed4 e q chi omega) (N : ℝ) (tupleHistory p) =
        P5OriginalCommonRefinedConstructor.level4 (sourceData rows4 licensed4 e q chi omega)
          (N : ℝ) (rosserAncestor 4 (tupleHistory p)) :=
    congrArg (fun a : ℝ => (N : ℝ) ^ a) hcap
  simp only [literalTupleDifference, actualOwnCubeGatedMinusDensity, hlevel,
    sub_self, zero_mul, zero_div]

/-- Complete finite residual source partition on the original ten-field
typed indices. It is exact for every cap and every tuple, without primes,
admission or any finite-Rosser monotonicity assumption. -/
theorem actual_literal_eq_source_sum
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (p : Fin 5 → ℕ) :
    literalTupleDifference
      (P5OriginalCommonRefinedConstructor.level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      (P5OriginalCommonRefinedConstructor.level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
      N cap p = ∑ i : ArchiveIndex, indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p := by
  by_cases hex : ∃ i : ArchiveIndex, actualPrimeTupleLog N p ∈ sourceCellDomain i e q chi omega
  · obtain ⟨i, hi⟩ := hex
    rw [actual_literal_on_source rows4 licensed4 e q chi omega N cap p i hi]
    symm
    apply Finset.sum_eq_single i
    · intro k _hk hki
      have hnot : actualPrimeTupleLog N p ∉ sourceCellDomain k e q chi omega := by
        intro hk
        exact hki (sourceCellDomain_unique k i e q chi omega _ hk hi)
      simp only [indexedLiteralTupleDifference, if_neg hnot]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  · have hout : ∀ i : ArchiveIndex, actualPrimeTupleLog N p ∉ sourceCellDomain i e q chi omega := by
      intro i hi
      exact hex ⟨i, hi⟩
    rw [actual_literal_zero_off_sources rows4 licensed4 e q chi omega N cap p hout]
    symm
    apply Finset.sum_eq_zero
    intro i _hi
    simp only [indexedLiteralTupleDifference, if_neg (hout i)]

/-- Every actual next candidate under one FIXED supplied parent is kept.
The SAME parent, N, cap, rough universe and reciprocal-prime factors occur
on both sides. Which parent realizes a full-rho telescope is not assumed. -/
theorem actual_frontier_tuple_sum_eq_indexed_sources
    (rows4 : Finset ProducerRow) (licensed4 : ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) (N cap : ℕ) (z : ℝ)
    (parent : Bool → List ℕ → Bool) :
    (∑ p ∈ firstExitFrontierTuples 4 parent (roughPrimeUniverse N cap 0 z),
      (∏ k, 1 / ((p k : ℝ) - 1)) * literalTupleDifference
        (P5OriginalCommonRefinedConstructor.level4 (sourceData rows4 licensed4 e q chi omega) (N : ℝ))
        (P5OriginalCommonRefinedConstructor.level5 (sourceData rows4 licensed4 e q chi omega) (N : ℝ)) N cap p) =
      ∑ i : ArchiveIndex, ∑ p ∈ firstExitFrontierTuples 4 parent (roughPrimeUniverse N cap 0 z),
        (∏ k, 1 / ((p k : ℝ) - 1)) * indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p := by
  calc
    _ = ∑ p ∈ firstExitFrontierTuples 4 parent (roughPrimeUniverse N cap 0 z),
        ∑ i : ArchiveIndex, (∏ k, 1 / ((p k : ℝ) - 1)) *
          indexedLiteralTupleDifference i rows4 licensed4 e q chi omega N cap p := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [actual_literal_eq_source_sum rows4 licensed4 e q chi omega N cap p, Finset.mul_sum]
    _ = _ := Finset.sum_comm

end
end ImbalancedChen.P1HistoricalFifthCommonLiteralContribution
