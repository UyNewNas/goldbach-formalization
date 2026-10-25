import ImbalancedChen.P1OriginalFifthWeightedSourceReduction
import ImbalancedChen.P1ActualCoarsePrimeFactorEnvelope

/-!
SOURCE_ONLY / UNCOMPILED.

The original rank-four first-exit carrier and selected fifth joint mesh reduce
the five small-coordinate faces exactly to the last face.  This is a finite
arithmetic identity.  A further finite domination separates the pointwise
Euler/source envelope from the reciprocal-prime mass.  The needed uniform
prime-tuple distribution estimate is not supplied by the retained-leaf
prime-factor cutoff theorem and is not asserted here.
-/

namespace ImbalancedChen.P1OriginalFifthEnvelopeTerminalReduction

noncomputable section

open scoped Classical BigOperators
open P1OriginalCoarseFifthContinuation
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalFifthWeightedSourceReduction

def terminalEnvelopeSum (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a : ℝ) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (told tnew : (Fin 5 → ℕ) → ℝ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p 4 < a),
      |∏ i, 1 / ((p i : ℝ) - 1)| *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
          sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5
            N cap told tnew p else 0)

/-- Strict ordering on the actual fifth joint mesh collapses all five
boundary faces to the fifth face.  Off the mesh both summands vanish. -/
theorem weightedEnvelopeSum_eq_terminalEnvelopeSum
    (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a : ℝ) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (told tnew : (Fin 5 → ℕ) → ℝ) :
    weightedEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
      N cap told tnew =
      terminalEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
        N cap told tnew := by
  unfold weightedEnvelopeSum terminalEnvelopeSum
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · have hcarrier : p ∈ candidates (e : ℝ) chi m omega N cap := by
      simpa only [sourceCarrier, candidates] using hp
    have hg := (mem_candidates_iff_log_on_cell (e : ℝ) chi m omega
      N cap hN hcap p j ht).mp hcarrier
    have hanti : StrictAnti (actualPrimeTupleLog N p) :=
      ((mem_jointRegion (e : ℝ) chi m omega j _).mp hg.2).2.1
    have hface : (∃ i, actualPrimeTupleLog N p i < a) ↔
        actualPrimeTupleLog N p 4 < a := by
      constructor
      · exact P1OriginalFifthAllFacesAnalyticTail.last_lt_of_any_coordinate_lt
          (actualPrimeTupleLog N p) hanti
      · intro h; exact ⟨4, h⟩
    simp only [if_pos ht, hface]
  · simp only [if_neg ht, mul_zero, ite_self]

/-- The unweighted reciprocal-prime mass on precisely the same selected
original T3 fifth carrier and strict terminal face. -/
def terminalPrimeMass (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a : ℝ) (J5 : Finset (Label5 m))
    (N cap : ℕ) : ℝ :=
  ∑ j ∈ selectedFifthCells e chi m omega J5,
    ∑ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p 4 < a),
      |∏ i, 1 / ((p i : ℝ) - 1)| *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
          (1 : ℝ) else 0)

/-- A genuine finite separation: a pointwise source-envelope bound is
multiplied only by the original selected prime-tuple mass.  The latter is
an independent arithmetic object, with no density difference in it. -/
theorem terminalEnvelopeSum_le_pointwise_bound_mul_mass
    (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a M : ℝ) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (told tnew : (Fin 5 → ℕ) → ℝ)
    (hM : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p 4 < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5
        N cap told tnew p ≤ M) :
    terminalEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
        N cap told tnew ≤
      M * terminalPrimeMass e chi m omega a J5 N cap := by
  unfold terminalEnvelopeSum terminalPrimeMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j
  · simp only [if_pos ht, mul_one]
    rw [mul_comm M]
    exact mul_le_mul_of_nonneg_left (hM j hj p hp ht) (abs_nonneg _)
  · simp only [if_neg ht, mul_zero, mul_zero]

/-- The precise finite normalized reduction at the original Suzuki scale.
It leaves two independent inputs visible: a pointwise source envelope and
the reciprocal-prime mass of the actual first-exit fifth tuples. -/
theorem normalized_weightedEnvelopeSum_le_pointwise_bound_mul_mass
    (A B K : ℝ) (e : ℚ) (chi : ℝ) (m : ℕ)
    (omega a M : ℝ) (J4 : Finset (Label4 m)) (cap4 : Label4 m → ℚ)
    (J5 : Finset (Label5 m)) (cap5 : Label5 m → ℚ)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (told tnew : (Fin 5 → ℕ) → ℝ)
    (hM : ∀ j ∈ selectedFifthCells e chi m omega J5,
      ∀ p ∈ (sourceCarrier e chi m omega N cap).filter
        (fun p => actualPrimeTupleLog N p 4 < a),
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j →
      sourceEnvelope A B K e chi m omega J4 cap4 J5 cap5
        N cap told tnew p ≤ M) :
    |Real.log (N : ℝ) / singularSeries N| *
      weightedEnvelopeSum A B K e chi m omega a J4 cap4 J5 cap5
        N cap told tnew ≤
      |Real.log (N : ℝ) / singularSeries N| *
        (M * terminalPrimeMass e chi m omega a J5 N cap) := by
  rw [weightedEnvelopeSum_eq_terminalEnvelopeSum
    A B K e chi m omega a J4 cap4 J5 cap5 N cap hN hcap told tnew]
  exact mul_le_mul_of_nonneg_left
    (terminalEnvelopeSum_le_pointwise_bound_mul_mass
      A B K e chi m omega a M J4 cap4 J5 cap5 N cap told tnew hM)
    (abs_nonneg _)

/-- The imported retained-leaf theorem concerns prime factors of a
supported modulus.  It is recorded with its exact quantifiers here: it
does not count fifth candidates or sum their reciprocal weights. -/
theorem retained_leaf_factor_cutoff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (hN : 1 < (N : ℝ)) (d : ℕ)
    (hd : d ∈ P1ActualCoarseFixedCoefficient.roughSupport
      e chi m omega N cap w z)
    (q : ℕ) (hq : q ∈ d.primeFactors) :
    (q : ℝ) < (N : ℝ) ^ (VariableEnvelope.extendedFirstStop - 4 * e) := by
  exact P1ActualCoarsePrimeFactorEnvelope.support_primeFactor_physical_cutoff
    e chi m omega N cap w z hN d hd q hq

end

end ImbalancedChen.P1OriginalFifthEnvelopeTerminalReduction
