import ImbalancedChen.P1CorrectedFifthSmallLastGeometry
import ImbalancedChen.P1CorrectedFifthMiddleShellSplit

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Crude harmonic summation of the COMPLETE actual corrected lower-deficit
source on the moving ultratiny fifth face. The explicit actual signed
smallRemainder is used throughout. No coarse old5 remainder is substituted.
The exp(-T) suppression pays all five harmonic losses and the visible
logN/singular normalization. Only finite ownership/h45 source checks and
eventual enumeration coverage remain as caller inputs.

This proves the actual corrected moving-cut remainder tends to zero.
The middle shells and the fixed-cutoff iterated tail limit are separate.
-/

namespace ImbalancedChen.P1CorrectedFifthMovingUltratiny

noncomputable section
open Filter Topology Set
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P1CorrectedFifthDensityDictionary P1CorrectedFifthCausalTupleDictionary
open P1CorrectedFifthStoredH45Check P1CorrectedFifthSmallLastGeometry
open P1OriginalSmallCutoffActualLowerTail P1OriginalFifthMovingHarmonicEnvelope
open P1OriginalFifthMovingScaleLimit P1OriginalFifthEnvelopeTerminalReduction
open P1OriginalFifthWeightedSourceReduction

/-- Complete actual source estimate, valid for every moving a,T satisfying
the displayed primitive scalar budgets. No remainder bound is an input. -/
theorem exists_corrected_smallRemainder_exp_harmonic_bound :
    ∃ A B K : ℝ, 0 < A ∧ 0 < B ∧ 2 ≤ K ∧
      ∀ (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
        (e : ℚ) (chi omega a T : ℝ), 0 < omega → 0 < a → a ≤ omega / 6 →
        2 ≤ T → a * T ≤ omega / 2 →
        ∀ (rows : Finset ProducerRow) (licensed : ProducerRow → Prop),
        P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega →
        storedH45Check D J e rows = true →
        ∀ N cap : ℕ, 1 < N → Even N →
        (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap : ℝ) →
        T ^ 13 ≤ (omega / 2) * Real.log (N : ℝ) →
        Real.exp 1 ≤ (omega / 2) * Real.log (N : ℝ) →
        |P1CorrectedFifthGlobalSourceAssembly.smallRemainder D J e chi omega rows licensed a N cap| ≤
          (2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T) *
            |Real.log (N : ℝ) / singularSeries N|) *
          (((D.cells5 ∩ J).card : ℝ) *
            (2 * (1 + Real.log (Nat.ceil ((N : ℝ) ^ (19 / 96 : ℝ)) : ℝ))) ^ 5) := by
  obtain ⟨A, B, K, hA, hB, hK, hsource⟩ := exists_correctedTupleDifference_exp_bound
  refine ⟨A, B, K, hA, hB, hK, ?_⟩
  intro D J e chi omega a T homega ha haomega hT haT rows licensed howned hcheck
    N cap hN hEven hcap hbudget hlog
  let M : ℝ := 2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T) *
    |Real.log (N : ℝ) / singularSeries N|
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have haomega3 : a ≤ omega / 3 := by linarith
  have howners := P1CorrectedFifthMiddleShellSplit.corrected_selected_owners_eq
    D J e chi omega howned
  have hpoint : ∀ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
      (e : ℝ) chi D.m omega N cap, ∀ j ∈ D.cells5 ∩ J,
      actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j →
      actualPrimeTupleLog N p 4 < a →
      |correctedTupleDifference D J e chi omega rows licensed N cap p| ≤ M := by
    intro p hp j hj ht hs
    have hb := hsource D J e chi omega a T homega ha haomega3 hT haT rows licensed
      howned hcheck N cap hN hEven hcap hbudget hlog p hp j hj ht hs.le
    have hbud := corrected_selected_source_budgets D J e chi omega a T homega ha haomega3
      hT haT rows licensed howned hcheck N cap hN hcap hbudget hlog p hp j hj ht hs.le
    have he : (1 : ℝ) ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
    have ho := tailEnvelope_le_uniform_exp A B K _ T T hA.le hB.le le_rfl
      (he.trans hbud.1.2.2.2)
    have hn := tailEnvelope_le_uniform_exp A B K _ T T hA.le hB.le le_rfl
      (he.trans hbud.2.2.2.2)
    have henv : actualSmallEulerProduct N cap (p 4 : ℝ) *
        (tailEnvelope A B K (residualLevel N
          (originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p)) p) T +
          tailEnvelope A B K (residualLevel N (D.cap5 j : ℝ) p) T) ≤
        2 * (A + B * Real.exp (Real.sqrt K)) * Real.exp (-T) := by
      have hsum0 : 0 ≤ tailEnvelope A B K (residualLevel N
          (originalVariableFourthProfile e chi omega D.m j rows licensed (actualPrimeTupleLog N p)) p) T +
          tailEnvelope A B K (residualLevel N (D.cap5 j : ℝ) p) T := by
        unfold tailEnvelope
        positivity
      calc
        _ ≤ 1 * _ := mul_le_mul_of_nonneg_right
          (actualSmallEulerProduct_le_one N cap (p 4 : ℝ)) hsum0
        _ ≤ _ := by rw [one_mul]; linarith
    exact hb.trans (mul_le_mul_of_nonneg_right henv (abs_nonneg _))
  have hmass : |P1CorrectedFifthGlobalSourceAssembly.smallRemainder
      D J e chi omega rows licensed a N cap| ≤
      M * terminalPrimeMass e chi D.m omega a (D.cells5 ∩ J) N cap := by
    unfold P1CorrectedFifthGlobalSourceAssembly.smallRemainder
      P1CorrectedFifthGlobalSourceAssembly.smallCellRemainder
    calc
      _ ≤ ∑ j ∈ D.cells5 ∩ J,
          |∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
              (e : ℝ) chi D.m omega N cap,
            (∏ i, 1 / ((p i : ℝ) - 1)) *
              (if (∃ i, actualPrimeTupleLog N p i < a) ∧
                  actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j then
                correctedTupleDifference D J e chi omega rows licensed N cap p else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ D.cells5 ∩ J,
          ∑ p ∈ HistoricalThirdCoarse.P1OriginalCoarseFifth.candidates
              (e : ℝ) chi D.m omega N cap,
            |(∏ i, 1 / ((p i : ℝ) - 1)) *
              (if (∃ i, actualPrimeTupleLog N p i < a) ∧
                  actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j then
                correctedTupleDifference D J e chi omega rows licensed N cap p else 0)| := by
        apply Finset.sum_le_sum
        intro j _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        unfold terminalPrimeMass
        rw [← howners, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro p hp
        by_cases ht : actualPrimeTupleLog N p ∈ logPrimeMeshCell 0 (19 / 96) D.m j
        · have hd := (HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_candidates_iff_log_on_cell
            (e : ℝ) chi D.m omega N cap hN hcap p j ht).mp hp
          have hanti := ((HistoricalThirdCoarse.P1OriginalCoarseFifth.mem_jointRegion
            (e : ℝ) chi D.m omega j _).mp hd.2).2.1
          by_cases hs : ∃ i, actualPrimeTupleLog N p i < a
          · have hlast := P1OriginalFifthAllFacesAnalyticTail.last_lt_of_any_coordinate_lt
              (actualPrimeTupleLog N p) hanti hs
            simp only [hs, ht, and_self, if_true, hlast, mul_one, abs_mul]
            simpa only [mul_comm M] using
              mul_le_mul_of_nonneg_left (hpoint p hp j hj ht hlast)
                (abs_nonneg (∏ i, 1 / ((p i : ℝ) - 1)))
          · have hlast : ¬actualPrimeTupleLog N p 4 < a := fun h => hs ⟨4, h⟩
            simp only [hs, ht, false_and, if_false, hlast, mul_zero, abs_zero]
        · simp [ht]
  have hterminal := terminalPrimeMass_le_moving_harmonic_bound
    e chi D.m omega a (D.cells5 ∩ J) N cap hN hcap
  rw [← howners] at hterminal
  exact hmass.trans (mul_le_mul_of_nonneg_left hterminal hM)

/-- The TRUE corrected signed remainder vanishes at the explicit moving
ultratiny cutoff. The proof uses complete source suppression and all-window
harmonic mass, with no moving-window prime asymptotic or remainder premise. -/
theorem corrected_smallRemainder_movingCutoff_tendsto_zero
    (D : HistoricalPrefixCapData) (J : Finset (FifthLabel D.m))
    (e : ℚ) (chi omega : ℝ) (homega : 0 < omega)
    (rows : Finset ProducerRow) (licensed : ProducerRow → Prop)
    (howned : P1VariableFifthSelectedStoredBinding.OriginalOwnedRows D J e chi omega)
    (hcheck : storedH45Check D J e rows = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in evenTargets,
      (N : ℝ) ^ (19 / 96 : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => P1CorrectedFifthGlobalSourceAssembly.smallRemainder
        D J e chi omega rows licensed (movingCutoff omega N) N (cap N))
      evenTargets (𝓝 0) := by
  obtain ⟨A, B, K, hA, hB, _hK, hbound⟩ :=
    exists_corrected_smallRemainder_exp_harmonic_bound
  let C : ℝ := 2 * (A + B * Real.exp (Real.sqrt K)) * ((D.cells5 ∩ J).card : ℝ)
  have hmajor : Tendsto (fun N : ℕ => C * normalizedMovingMajorant N) evenTargets (𝓝 0) := by
    simpa only [mul_zero] using
      (normalizedMovingMajorant_tendsto_zero.const_mul C).mono_left inf_le_left
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) ?_ hmajor
  filter_upwards [(eventually_moving_scale_budgets omega homega).filter_mono inf_le_left,
    hcap, (show ∀ᶠ N : ℕ in evenTargets, 0 < N ∧ Even N from
      (Filter.eventually_mem_principal _).filter_mono inf_le_right)] with N hb hc he
  obtain ⟨hN, ha0, ha, hT, haT, hbudget, hlog⟩ := hb
  have h := hbound D J e chi omega (movingCutoff omega N) (movingBudget N)
    homega ha0 ha hT haT rows licensed howned hcheck N (cap N) (by omega) he.2 hc hbudget hlog
  calc
    _ ≤ _ := h
    _ = C * normalizedMovingMajorant N := by
      dsimp [C, normalizedMovingMajorant, harmonicFactor]
      ring

end
end ImbalancedChen.P1CorrectedFifthMovingUltratiny
