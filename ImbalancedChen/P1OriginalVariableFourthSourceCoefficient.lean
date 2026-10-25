import ImbalancedChen.P1OriginalVariableFourthRowModulusTransfer
import ImbalancedChen.P1OriginalVariableFourthCellTestLimit
import ImbalancedChen.P1OriginalCoarseFourthResidualDictionary

/-!
The exact fourth first-exit coefficient for the original firstStop and
rough-activated raw Q3 policy, raised to the pointwise producer Q4 cap.
The finite arithmetic identity keeps the rank-four signed PLUS residual;
the continuous positive-cell test is a separate prime-box identity.
Source-only candidate; no compiler was run.
-/

namespace ImbalancedChen
noncomputable section
open scoped Classical BigOperators
open HistoricalThirdCoarse VariableEnvelope
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthDescendantLevel
open P1OriginalVariableFourthRowModulusTransfer
open P2OriginalFourthCapProducerInterface
open P1OriginalCoarseFourthResidual
open P1FourthFullCellIntegral
open P1OriginalFourthIntegral
open P1OriginalVariableFourthCellTestLimit

namespace P1OriginalVariableFourthSourceCoefficient

/-- Literal policy difference, with the original rank-one firstStop and
rough-activated raw Q3 retained in both trees. The comparison comes from the
pointwise max's true rawQ3 seed, not from a new cap hypothesis. -/
theorem original_policy_difference_eq_fourth_saving
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (z : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (hN : 1 ≤ (N : ℝ)) :
    firstExitRetainedPolynomial (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) =
      actualHistoricalFourthSaving (initialPolicy e m (N : ℝ))
        (rawLevel e chi m omega (N : ℝ))
        (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap z := by
  apply actualHistoricalFourthSaving_eq
  intro state hstate
  exact producer_actual_h34 e chi m omega N cap hN z rows licensed state hstate

/-- The resulting weighted source coefficient is the exact admitted
four-prime PLUS residual difference. This is an arithmetic identity at N;
no sieve mean, target-density bound or box limit is invoked. -/
theorem original_policy_difference_eq_admitted_tuple_sum
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (z : ℝ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (hN : 1 ≤ (N : ℝ)) :
    (firstExitRetainedPolynomial (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z) -
      firstExitRetainedPolynomial
        (producerPolicy4 e chi m omega (N : ℝ) rows licensed)
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1 (roughPrimeUniverse N cap 0 z)) *
        Real.log (N : ℝ) / singularSeries N =
      ∑ p ∈ firstExitAdmittedTuples 4
          (HistoricalThirdCoarse.policy e chi m omega (N : ℝ))
          (roughPrimeUniverse N cap 0 z),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          literalTupleResidualDifference
            (rawLevel e chi m omega (N : ℝ))
            (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap p := by
  rw [original_policy_difference_eq_fourth_saving e chi m omega N cap z rows licensed hN]
  exact actualHistoricalFourthSaving_eq_literalTupleSum
    (initialPolicy e m (N : ℝ)) (rawLevel e chi m omega (N : ℝ))
    (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap z

/-- On one matching row the literal arithmetic term is the old rawQ3 PLUS
residual minus the row's PLUS residual. No continuous test has replaced the
finite signed Rosser factor. -/
theorem literal_fourth_plus_coefficient_eq_winning_row
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (p : Fin 4 → ℕ) (r : ProducerRow) (hr : r ∈ rows)
    (her : producerEligible licensed r (actualPrimeTupleLog N p))
    (hseed : seedExponent e chi m omega (N : ℝ) (tupleHistory p) ≤
      r.bufferedCandidate e (actualPrimeTupleLog N p))
    (hrows : ∀ s ∈ rows, producerEligible licensed s (actualPrimeTupleLog N p) →
      s.bufferedCandidate e (actualPrimeTupleLog N p) ≤
        r.bufferedCandidate e (actualPrimeTupleLog N p)) :
    literalTupleResidualDifference
        (rawLevel e chi m omega (N : ℝ))
        (producerLevel4 e chi m omega (N : ℝ) rows licensed) N cap p =
      fourthTuplePlusResidualP1 N cap
          (seedExponent e chi m omega (N : ℝ) (tupleHistory p)) p -
        fourthTuplePlusResidualP1 N cap
          (v (∑ i ∈ r.selected, actualPrimeTupleLog N p i) - 2 * e) p := by
  have hlen : (tupleHistory p).length = 4 := by simp [tupleHistory]
  have hnew := producerLevel4_eq_winning_row e chi m omega (N : ℝ)
    rows licensed (tupleHistory p) hlen r hr
    (by simpa only [tupleHistory_log] using her)
    (by simpa only [tupleHistory_log] using hseed)
    (by simpa only [tupleHistory_log] using hrows)
  rw [tupleHistory_log] at hnew
  have hold := frozenLevel_eq_rpow_seed e chi m omega (N : ℝ) (tupleHistory p)
  change rawLevel e chi m omega (N : ℝ) (rosserAncestor 3 (tupleHistory p)) =
    (N : ℝ) ^ seedExponent e chi m omega (N : ℝ) (tupleHistory p) at hold
  unfold literalTupleResidualDifference fourthTuplePlusResidualP1
  rw [hold, hnew]
  ring

/-- Restricting the original admitted fourth frontier to a positive source
cell gives the identical weighted prime-box sum. A winning row is checked
at each tuple's actual logarithmic coordinate; the row need not win outside
this source cell. -/
theorem original_winning_row_source_eq_weighted_prime_box
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ)
    (J4 : Finset (P1OriginalCoarseContinuation.FourthCell m))
    (j : P1OriginalCoarseContinuation.FourthCell m)
    (hj : j ∈ P1OriginalCoarseContinuation.selectedFourthCells e chi m omega J4)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ))
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (r : ProducerRow) (hr : r ∈ rows)
    (hwin : ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a)
        (fun _ => (19 / 96 : ℝ)),
      actualPrimeTupleLog N p ∈ P1OriginalFourthLimit.sourceRegion e m omega j →
        producerEligible licensed r (actualPrimeTupleLog N p) ∧
        seedExponent (e : ℝ) chi m omega (N : ℝ) (tupleHistory p) ≤
          r.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
        ∀ s ∈ rows, producerEligible licensed s (actualPrimeTupleLog N p) →
          s.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ≤
            r.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p)) :
    (∑ p ∈ (firstExitAdmittedTuples 4
        (HistoricalThirdCoarse.policy (e : ℝ) chi m omega (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (19 / 96 : ℝ)))).filter
          (fun p => ∀ i, a ≤ actualPrimeTupleLog N p i),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) m j then
          literalTupleResidualDifference
            (rawLevel (e : ℝ) chi m omega (N : ℝ))
            (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap p
         else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a)
          (fun _ => (19 / 96 : ℝ)),
        P1OriginalCoarseFourthArithmeticWall.signedTupleWeight p *
          (if actualPrimeTupleLog N p ∈
              P1OriginalFourthLimit.sourceRegion e m omega j then
            fourthTuplePlusResidualP1 N cap
                (seedExponent (e : ℝ) chi m omega (N : ℝ) (tupleHistory p)) p -
              fourthTuplePlusResidualP1 N cap
                (v (∑ i ∈ r.selected, actualPrimeTupleLog N p i) - 2 * (e : ℝ)) p
           else 0) := by
  rw [P1OriginalFourthLimit.positive_frontier_weighted_sum e chi m omega a
    J4 N cap hN hcap j hj
    (literalTupleResidualDifference
      (rawLevel (e : ℝ) chi m omega (N : ℝ))
      (producerLevel4 (e : ℝ) chi m omega (N : ℝ) rows licensed) N cap)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [P1OriginalCoarseFourthArithmeticWall.signedTupleWeight_eq]
  by_cases hs : actualPrimeTupleLog N p ∈ P1OriginalFourthLimit.sourceRegion e m omega j
  · obtain ⟨her, hseed, hrows⟩ := hwin p hp hs
    simp only [if_pos hs]
    rw [literal_fourth_plus_coefficient_eq_winning_row (e : ℝ) chi m omega N cap
      rows licensed p r hr her hseed hrows]
  · simp only [if_neg hs]

/-- The accompanying continuous positive-cell test uses the same winning
row exponent, but is deliberately stated separately from the finite Rosser
PLUS residual identity above. In particular it makes no local sieve-density
identification at finite N. -/
theorem labelledRawCellSum_eq_winning_row_test
    (e : ℚ) (m N : ℕ) (omega a : ℝ)
    (ha : 0 < a) (hN : 1 < N)
    (j : P1OriginalCoarseContinuation.FourthCell m)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (r : ProducerRow) (hr : r ∈ rows)
    (hwin : ∀ p ∈ actualPrimeBoxTuples N (fun _ : Fin 4 => a)
        (fun _ => (19 / 96 : ℝ)),
      actualPrimeTupleLog N p ∈ P1OriginalFourthLimit.sourceRegion e m omega j →
        producerEligible licensed r (actualPrimeTupleLog N p) ∧
        oldExponent e m j ≤
          r.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ∧
        ∀ s ∈ rows, producerEligible licensed s (actualPrimeTupleLog N p) →
          s.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) ≤
            r.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p)) :
    labelledRawCellSum e m omega a j rows licensed N =
      actualPrimeBoxTestSum N (fun _ : Fin 4 => a) (fun _ => (19 / 96 : ℝ))
        ((P1OriginalFourthLimit.sourceRegion e m omega j).indicator
          (fun t => extendedProfile (oldExponent e m j) t -
            extendedProfile
              (v (∑ i ∈ r.selected, t i) - 2 * (e : ℝ)) t)) := by
  rw [labelledRawCellSum_eq_test e m N omega a ha hN j rows licensed]
  unfold actualPrimeBoxTestSum
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hs : actualPrimeTupleLog N p ∈ P1OriginalFourthLimit.sourceRegion e m omega j
  · obtain ⟨her, hseed, hrows⟩ := hwin p hp hs
    have hprofile : producerProfile4 (e : ℝ) rows licensed (oldExponent e m j)
        (actualPrimeTupleLog N p) =
          r.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p) := by
      change finiteMax rows
        (fun s => producerEligible licensed s (actualPrimeTupleLog N p))
        (fun s => s.bufferedCandidate (e : ℝ) (actualPrimeTupleLog N p))
        (oldExponent e m j) = _
      apply le_antisymm
      · exact finiteMax_le rows _ _ _ _ hseed hrows
      · exact finiteMax_row_le rows _ _ _ r hr her
    simp only [Set.indicator_of_mem hs]
    rw [hprofile, r.bufferedCandidate_eq]
  · simp only [Set.indicator_of_not_mem hs]

end P1OriginalVariableFourthSourceCoefficient
end
end ImbalancedChen
