import ImbalancedChen.P4AFull87VariableSeedHistory
import ImbalancedChen.P4AOriginalFull87DataPolicy

/-! Exact current level for arbitrary OriginalData, including the union
bank. Earlier programs read the supplied rows. Every saved, eleven and
later guard refers to the actual predecessor in that same data tree. -/
namespace ImbalancedChen.P4AFull87DataSeedHistory
noncomputable section
open scoped Classical BigOperators
open P4AFull87VariableSeedHistory P1FiniteAffineDecisionProgram
open P4AOriginalFourthFifthAffinePrograms P4AOriginalCompleteSixthAffinePrograms
open P5OriginalCommonRefinedConstructor P4AOriginalFull87DataPolicy
open P4AOriginalCompleteSixthChronology (laterEligible applyLater)
theorem data_variableSavedProgram_at_history (d : OriginalData) (N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 d N pre = baseValue b N pre) :
    (variableSavedProgram d b).eval (primeHistoryLogCoordinates N 6 pre) =
      savedExponent d N pre := by
  have hf := variableFifthAtSix_at_history d b N pre hlen hb
  simp only [variableSavedProgram, eval_maxRows, Finset.toList_toFinset,
    savedExponent, savedEligible, hlen, true_and, hb]
  congr 1
  · funext i
    apply propext
    simpa only [hf,liftSeed_exact _ _ b N pre hlen] using variableSavedTests_exact d b i
      (primeHistoryLogCoordinates N 6 pre)
  · funext i
    exact savedEndpoint_exact i _
  · exact hf

theorem data_variableElevenProgram_at_history (d : OriginalData) (N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 d N pre = baseValue b N pre) :
    (variableElevenProgram d b).eval (primeHistoryLogCoordinates N 6 pre) =
      elevenExponent d N pre := by
  have hf := variableFifthAtSix_at_history d b N pre hlen hb
  simp only [variableElevenProgram, eval_maxRows, elevenExponent, eligibleSixth,
    hlen, true_and]
  congr 1
  · funext c
    apply propext
    simpa only [hf] using variableElevenTests_exact d b c
      (primeHistoryLogCoordinates N 6 pre)
  · funext c
    exact elevenNewA_exact c _
  · exact data_variableSavedProgram_at_history d N b pre hlen hb

theorem data_variableAfterProgram_at_history (d : OriginalData) (N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 d N pre = baseValue b N pre)
    (j : ℕ) :
    (variableAfterProgram d b j).eval (primeHistoryLogCoordinates N 6 pre) =
      afterLater d N pre j := by
  induction j with
  | zero => exact data_variableElevenProgram_at_history d N b pre hlen hb
  | succ j ih =>
      simp only [variableAfterProgram, laterStep, eval_maxRows, Finset.toList_toFinset,
        afterLater, applyLater, laterEligible, hlen, true_and]
      congr 1
      · funext c
        apply propext
        simpa only [ih] using laterTests_exact j (variableAfterProgram d b j) c
          (primeHistoryLogCoordinates N 6 pre)
      · funext c
        exact laterEndpointA_exact c _
      · exact ih

theorem data_variableCompleteProgram_at_history (d : OriginalData) (N : ℝ) (b : Program 3)
    (pre : List ℕ) (hlen : pre.length = 6) (hb : lambda3 d N pre = baseValue b N pre) :
    (variableCompleteProgram d b).eval (primeHistoryLogCoordinates N 6 pre) =
      currentSixthExponent d N pre :=
  data_variableAfterProgram_at_history d N b pre hlen hb 8

theorem data_complete_at_own_six (d : OriginalData) (N : ℝ) (pre : List ℕ)
    (hl : pre.length = 6) :
    let b := third d (seedCode d N pre)
    (variableCompleteProgram d b).eval (primeHistoryLogCoordinates N 6 pre) =
      currentSixthExponent d N pre :=
  data_variableCompleteProgram_at_history d N _ pre hl (seed_exact _ N pre hl)

end
end ImbalancedChen.P4AFull87DataSeedHistory
