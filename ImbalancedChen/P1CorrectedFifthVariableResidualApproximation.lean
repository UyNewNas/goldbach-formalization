import ImbalancedChen.P1CorrectedFifthCausalTupleDictionary
import ImbalancedChen.P1VariableOwnCubeResidualUniformity

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The actual original variable-fourth profile has explicit global bounds:
its seed is either the original initial exponent or this owner's raw Q3
exponent, and every producer candidate is at most cap-2e. The uniform
moving-level residual theorem therefore applies to the ACTUAL original
fourth profile, without replacing it by an all-subsets model.

Only the arithmetic residual replacement error is closed. The prime-test
limit for this profile on the original joint region and its genuine row
walls remains OPEN, as does removing the positive lower-coordinate cut.
-/

namespace ImbalancedChen.P1CorrectedFifthVariableResidualApproximation

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P1CorrectedFifthDensityDictionary P1VariableOwnCubeResidualUniformity

def lowerFourth (D : HistoricalPrefixCapData) (e : ℚ) (chi : ℝ) (j : Label5 D.m) : ℝ :=
  min (HistoricalThirdCoarse.initial (e : ℝ))
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdCellExponent (e : ℝ) chi D.m j)

def upperFourth (D : HistoricalPrefixCapData) (e : ℚ) (chi : ℝ) (j : Label5 D.m) : ℝ :=
  max (max (HistoricalThirdCoarse.initial (e : ℝ))
    (HistoricalThirdCoarse.P1OriginalCoarseFifth.thirdCellExponent (e : ℝ) chi D.m j))
      (VariableEnvelope.cap - 2 * (e : ℝ))

/-- The actual raw Q3 fallback and every actual producer row are bounded
on every point, including row and rough-activation boundaries. -/
theorem originalVariableFourthProfile_mem_fixed_interval
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega : ℝ) (j : Label5 D.m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (t : Fin 5 → ℝ) :
    originalVariableFourthProfile e chi omega D.m j rows4 licensed4 t ∈
      Icc (lowerFourth D e chi j) (upperFourth D e chi j) := by
  let seed := HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent
    (e : ℝ) chi D.m omega j t
  have hseedlo : lowerFourth D e chi j ≤ seed := by
    dsimp [lowerFourth, seed, HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent]
    split_ifs
    · exact min_le_right _ _
    · exact min_le_left _ _
  have hseedhi : seed ≤ upperFourth D e chi j := by
    dsimp [upperFourth, seed, HistoricalThirdCoarse.P1OriginalCoarseFifth.currentExponent]
    split_ifs
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_left _ _)
  constructor
  · exact hseedlo.trans
      (P1OriginalVariableFourthContinuation.profile4_seed_le seed rows4
        (P1OriginalVariableFourthContinuation.producerEligible licensed4)
        (fun r => r.bufferedCandidate (e : ℝ))
        (historicalPrefixProject (by omega : 4 ≤ 5) t))
  · change P1OriginalVariableFourthContinuation.finiteMax rows4
      (fun r => P1OriginalVariableFourthContinuation.producerEligible licensed4 r
        (historicalPrefixProject (by omega : 4 ≤ 5) t))
      (fun r => r.bufferedCandidate (e : ℝ)
        (historicalPrefixProject (by omega : 4 ≤ 5) t)) seed ≤ upperFourth D e chi j
    apply P1OriginalVariableFourthContinuation.finiteMax_le _ _ _ _ _ hseedhi
    intro r _hr _he
    have hc : r.bufferedCandidate (e : ℝ)
        (historicalPrefixProject (by omega : 4 ≤ 5) t) ≤
          VariableEnvelope.cap - 2 * (e : ℝ) := by
      rw [r.bufferedCandidate_eq]
      exact sub_le_sub_right (VariableEnvelope.v_le_cap _) _
    exact hc.trans (le_max_right _ _)

/-- Arithmetic replacement for the actual old original-fourth profile,
on any fixed extra region. No profile or region regularity is required. -/
theorem tendsto_originalVariableFourth_ownCube_error
    (D : HistoricalPrefixCapData) (e : ℚ) (chi omega a : ℝ)
    (ha : 0 < a) (hab : a < (19 / 96 : ℝ)) (j : Label5 D.m)
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (R : Set (Fin 5 → ℝ)) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ =>
      actualPrimeBoxVariableOwnCubeMinusSum 4 N (cap N) a (19 / 96)
          (originalVariableFourthProfile e chi omega D.m j rows4 licensed4) R -
        actualPrimeBoxTestSum N (fun _ : Fin 5 => a) (fun _ => (19 / 96 : ℝ))
          (fun t => if t ∈ R then
            (if primeTupleOwnCubeForm t <
                originalVariableFourthProfile e chi omega D.m j rows4 licensed4 t then
              primeTupleMinusProfile
                (originalVariableFourthProfile e chi omega D.m j rows4 licensed4 t) t
              else 0) else 0))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N}) (𝓝 0) := by
  exact tendsto_actualPrimeBoxVariableOwnCubeMinus_error 4 a (19 / 96)
    (lowerFourth D e chi j) (upperFourth D e chi j) ha hab
    (originalVariableFourthProfile e chi omega D.m j rows4 licensed4)
    (fun t _ht => originalVariableFourthProfile_mem_fixed_interval
      D e chi omega j rows4 licensed4 t) R cap hcap

end
end ImbalancedChen.P1CorrectedFifthVariableResidualApproximation
