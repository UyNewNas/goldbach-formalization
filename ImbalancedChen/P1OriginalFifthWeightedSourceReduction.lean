import ImbalancedChen.P1OriginalCoarseFifthCellLimit
import ImbalancedChen.P1OriginalSmallCutoffActualLowerTail
import ImbalancedChen.P1OriginalFifthAllFacesAnalyticTail

/-!
SOURCE_ONLY / UNCOMPILED.

The literal original T3 fifth small remainder is rewritten into the actual
same-cutoff lower-density difference, with its real normalization visible.
The pinned Suzuki source estimate then reduces arithmetic control to a
positive weighted Euler/source-envelope sum.  No bound for that remaining
prime-tuple sum is postulated or inferred from the continuous integral.
-/

namespace ImbalancedChen.P1OriginalFifthWeightedSourceReduction

noncomputable section

open Filter Topology
open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation

abbrev sourceCarrier (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (N cap : ℕ) : Finset (Fin 5 → ℕ) :=
  firstExitFrontierTuples 4
    (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
    (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))

/-- The normalized dictionary and the actual small-cutoff source use the
same reversed fifth history. -/
theorem normalized_difference_eq_actual_source
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    P1OriginalCoarseFifthResidual.coarseTupleOwnCubeDifference
      e chi m omega J4 cap4 J5 cap5 N cap p =
      P1OriginalSmallCutoffActualLowerTail.originalDifference
        e chi m omega J4 cap4 J5 cap5 N cap p *
        Real.log (N : ℝ) / singularSeries N := by
  have hlen : (P1OriginalCoarseFifthResidual.tupleHistory p).length = 5 := by
    simp [P1OriginalCoarseFifthResidual.tupleHistory]
  have h := P1OriginalCoarseFifthResidual.coarseTupleOwnCubeDifference_history
    e chi m omega J4 cap4 J5 cap5 N cap
    (P1OriginalCoarseFifthResidual.tupleHistory p) hlen
  rw [P1OriginalCoarseFifthResidual.primeHistoryTuple_tupleHistory] at h
  simpa only [P1OriginalSmallCutoffActualLowerTail.originalDifference,
    P1OriginalSmallCutoffActualLowerTail.history5,
    P1OriginalCoarseFifthResidual.tupleHistory] using h

/-- Literal original small remainder on the same complete rank-four carrier.
The two strict own-cube indicators have only been rewritten through proved
residual identities; neither has become a carrier filter. -/
theorem smallRemainder_eq_weighted_actual_source
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) :
    P1OriginalFifthLimit.smallRemainder e chi m omega a J4 cap4 J5 cap5 N cap =
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
            (fun p => ∃ i, actualPrimeTupleLog N p i < a),
          (∏ i, 1 / ((p i : ℝ) - 1)) *
            (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
              P1OriginalSmallCutoffActualLowerTail.originalDifference
                e chi m omega J4 cap4 J5 cap5 N cap p *
                  Real.log (N : ℝ) / singularSeries N else 0) := by
  unfold P1OriginalFifthLimit.smallRemainder P1OriginalFifthLimit.smallCellRemainder
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · rw [if_pos ht, if_pos ht]
    have hpos := P1OriginalCoarseFifthResidual.candidateTuple_pos
      e chi m omega N cap ((N : ℝ) ^ (19 / 96 : ℝ)) p
      (Finset.mem_filter.mp hp).1
    rw [← P1OriginalCoarseFifthResidual.coarseTupleOwnCubeDifference_on_cell
      e chi m omega J4 cap4 J5 cap5 N cap hN p hpos j hj ht,
      normalized_difference_eq_actual_source]
  · simp only [if_neg ht, mul_zero]

def sourceEnvelope (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (told tnew : (Fin 5 → ℕ) → ℝ) (p : Fin 5 → ℕ) : ℝ :=
  actualSmallEulerProduct N cap (p 4 : ℝ) *
    (P1OriginalSmallCutoffActualLowerTail.tailEnvelope A B K
      (P1OriginalSmallCutoffActualLowerTail.residualLevel N
        (P1OriginalSmallCutoffActualLowerTail.oldExponent e chi m omega J4 cap4 N p) p)
      (told p) +
     P1OriginalSmallCutoffActualLowerTail.tailEnvelope A B K
      (P1OriginalSmallCutoffActualLowerTail.residualLevel N
        (P1OriginalSmallCutoffActualLowerTail.newExponent
          e chi m omega J4 cap4 J5 cap5 N p) p) (tnew p))

def weightedEnvelopeSum (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a : ℝ) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (told tnew : (Fin 5 → ℕ) → ℝ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => ∃ i, actualPrimeTupleLog N p i < a),
      |∏ i, 1 / ((p i : ℝ) - 1)| *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
          sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5
            N cap told tnew p else 0)

/-- This is the exact weighted-sum reduction.  The hypotheses are only
pointwise own-cube admissions and legal source budgets for the tuples being
summed, not a bound on the target remainder or its mean. -/
theorem exists_weighted_source_bound
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N)
    (told tnew : (Fin 5 → ℕ) → ℝ)
    (hlegal : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => ∃ i, actualPrimeTupleLog N p i < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      (∀ i, 0 < p i) ∧ 1 < (p 4 : ℝ) ∧ (p 4 : ℝ) ≤ (cap : ℝ) ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 <
        (N : ℝ) ^ P1OriginalSmallCutoffActualLowerTail.oldExponent
          e chi m omega J4 cap4 N p ∧
      (∏ i, p i : ℕ) * (p 4 : ℝ) ^ 2 <
        (N : ℝ) ^ P1OriginalSmallCutoffActualLowerTail.newExponent
          e chi m omega J4 cap4 J5 cap5 N p ∧
      P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.oldExponent
            e chi m omega J4 cap4 N p) p) (told p) ∧
      P1OriginalSmallCutoffActualLowerTail.sourceBudget (p 4 : ℝ)
        (P1OriginalSmallCutoffActualLowerTail.residualLevel N
          (P1OriginalSmallCutoffActualLowerTail.newExponent
            e chi m omega J4 cap4 J5 cap5 N p) p) (tnew p)) :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      |P1OriginalFifthLimit.smallRemainder e chi m omega a
        J4 cap4 J5 cap5 N cap| ≤
        |Real.log (N : ℝ) / singularSeries N| *
          weightedEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
            N cap told tnew := by
  obtain ⟨A, B, K, hA, hB, hK, hpoint⟩ :=
    P1OriginalSmallCutoffActualLowerTail.exists_originalDifference_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  rw [smallRemainder_eq_weighted_actual_source e chi m omega a
    J4 cap4 J5 cap5 N cap hN]
  have hsum :
      |∑ j ∈ selectedFifthCells e chi m omega J5,
        ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
          (fun p => ∃ i, actualPrimeTupleLog N p i < a),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            P1OriginalSmallCutoffActualLowerTail.originalDifference
              e chi m omega J4 cap4 J5 cap5 N cap p *
                Real.log (N : ℝ) / singularSeries N else 0)| ≤
      ∑ j ∈ selectedFifthCells e chi m omega J5,
        ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
          (fun p => ∃ i, actualPrimeTupleLog N p i < a),
        |∏ i, 1 / ((p i : ℝ) - 1)| *
          (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
            sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5
              N cap told tnew p *
                |Real.log (N : ℝ) / singularSeries N| else 0) := by
    calc
      _ ≤ ∑ j ∈ selectedFifthCells e chi m omega J5,
          |∑ p ∈ (sourceCarrier e chi m omega N cap).filter
            (fun p => ∃ i, actualPrimeTupleLog N p i < a),
            (∏ i, 1 / ((p i : ℝ) - 1)) *
              (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
                P1OriginalSmallCutoffActualLowerTail.originalDifference
                  e chi m omega J4 cap4 J5 cap5 N cap p *
                    Real.log (N : ℝ) / singularSeries N else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro p hp
        by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
        · obtain ⟨hpos, hy, hcap, hgate4, hgate5, ho, hn⟩ := hlegal j hj p hp ht
          have hb := hpoint e chi m omega J4 cap4 J5 cap5 N cap p
            hEven hpos hy hcap hgate4 hgate5 (told p) (tnew p) ho hn
          have hshape :
              P1OriginalSmallCutoffActualLowerTail.originalDifference
                  e chi m omega J4 cap4 J5 cap5 N cap p *
                    Real.log (N : ℝ) / singularSeries N =
                P1OriginalSmallCutoffActualLowerTail.originalDifference
                  e chi m omega J4 cap4 J5 cap5 N cap p *
                    (Real.log (N : ℝ) / singularSeries N) := by ring
          rw [if_pos ht, if_pos ht, abs_mul, hshape, abs_mul]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hb (abs_nonneg _)) (abs_nonneg _)
        · simp only [if_neg ht, mul_zero, abs_zero]
  calc
    _ ≤ _ := hsum
    _ = |Real.log (N : ℝ) / singularSeries N| *
        weightedEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
          N cap told tnew := by
      unfold weightedEnvelopeSum
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      apply Finset.sum_congr rfl
      intro p _hp
      split_ifs <;> ring

end

end ImbalancedChen.P1OriginalFifthWeightedSourceReduction
