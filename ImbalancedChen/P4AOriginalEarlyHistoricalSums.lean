import ImbalancedChen.P4AOriginalEarlyFiniteStages

namespace ImbalancedChen.P4AOriginalEarlyHistoricalSums
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData common3 old3 policy4 policy5 originalSeed)
open P5OriginalCommonFourthSourceLedger (originalFourthSaving)
open P4AOriginalNewFifthUnion (data original)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P5OriginalCommonPositivePresieve (normalize normalize_add)
open P4AOriginalEarlyFiniteStages (W)
open P1OriginalVariableFourthContinuation (producerEligible)
open P5OriginalCommonRefinedSeedHull (oldFourth oldFifth)
open P5OriginalFifthArchiveFiniteIdentity (oldQ4 oldQ5)

abbrev oldLevel3 (d : OriginalData) (N : ℕ) := HistoricalThirdCoarse.rawLevel d.e d.chi d.m d.omega (N:ℝ)
abbrev B4 (d : OriginalData) (N cap : ℕ) (z : ℝ) :=
  firstExitAdmittedTuples 4 (old3 d N) (roughPrimeUniverse N cap 0 z)
abbrev B5 (d : OriginalData) (N cap : ℕ) (z : ℝ) :=
  firstExitFrontierTuples 4 (old3 d N) (roughPrimeUniverse N cap 0 z)
abbrev O4 (d : OriginalData) (N cap : ℕ) :=
  P1OriginalCoarseFourthResidual.literalTupleResidualDifference (oldLevel3 d N) (oldQ4 d N) N cap
abbrev O5 (d : OriginalData) (N cap : ℕ) :=
  P1CorrectedFifthCausalTupleDictionary.literalTupleDifference (oldQ4 d N) (oldQ5 d N) N cap

/-- Both old and new fifth banks occur in d+. Their unrounded reference
charge is the signed sum over ALL next candidates of the old third tree. -/
theorem unrounded_sums (e : ℚ) (q : ℕ) (a : ℝ) (N : ℕ) (hN : 1≤(N:ℝ)) :
    let d := data e q a
    P4AOriginalEarlyHistoricalFloors.gain e q a N =
      (∑p∈B4 d N N (cutoff N),W p*O4 d N N p)+(∑p∈B5 d N N (cutoff N),W p*O5 d N N p) := by
  let d := data e q a
  dsimp only
  rw [P4AOriginalEarlyHistoricalFloors.split e q a N hN,P4AOriginalNewFifthPhysical.newGain_eq]
  have h4 : normalize N (originalFourthSaving (original e q a) N N (cutoff N)) =
      ∑p∈B4 d N N (cutoff N),W p*O4 d N N p :=
    P1OriginalCoarseFourthResidual.actualHistoricalFourthSaving_eq_literalTupleSum _ _ _ N N (cutoff N)
  have h5 : P4AOriginalNewFifthMean.rawDifference e q a N N =
      ∑p∈B5 d N N (cutoff N),W p*O5 d N N p := by
    unfold P4AOriginalNewFifthMean.rawDifference
    rw [P5OriginalCommonFifthPhysicalCaller.raw_fourth_sub_fifth_eq_actualCharge _ N N hN,
      P5OriginalCommonFifthPhysicalCaller.normalized_actualCharge_eq_literalCharge,
      P4AOriginalNewFifthMean.true_literal_charge]
    rfl
  rw [h4,h5]
  ring

end
end ImbalancedChen.P4AOriginalEarlyHistoricalSums
