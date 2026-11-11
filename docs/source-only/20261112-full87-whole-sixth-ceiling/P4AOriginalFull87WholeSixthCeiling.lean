import ImbalancedChen.P4AOriginalFull87LicensedSixthCeiling
import ImbalancedChen.P4AOriginalCompleteSixthChronology
import ImbalancedChen.P5OriginalCommonRefinedConstructor
import ImbalancedChen.P4AOriginalFull87FiniteParentCaps
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An unconditional (apart from the ORIGINAL nonnegative buffer e) global
subunit scalar ceiling for the real common third, fourth, fifth and sixth
chronology. This is NOT the false claim that every fifth seed is <= 153/256:
the original initial seed 299/500 - 2e can exceed 153/256 for small e.
We keep 299/500 as a uniform bound, including the inherited fifth and
third-inactive raw sixth branches.

No stopped-leaf q modulus, small-factor L, PP license, numerical gain
or reserve payment is inferred from this scalar estimate.
-/

namespace ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope
open HistoricalThirdCoarse
open P5OriginalCommonRefinedConstructor
open P1OriginalVariableFourthContinuation (finiteMax_le)
open P1GuardFrozenFiniteCapAlgebra (protect rounded rounded_mono rounded_error)
open P4AOriginalFull87FiniteParentCaps (cap5 cap5_eq_protect)
open P4AOriginalFull87HistoryCore (width width_pos)

private theorem tent_le_initial_ceiling (x : ℝ) :
    VariableEnvelope.v x ≤ (299 / 500 : ℝ) :=
  (VariableEnvelope.v_le_cap x).trans (by norm_num [VariableEnvelope.cap])

/-- The ACTUAL frozen third seed, including the unselected joint-cell
fallback, lies below the original 299/500 starting exponent. -/
theorem originalSeed_le_initial_ceiling
    (d : OriginalData) (he : (0 : ℝ) ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) :
    originalSeed d N pre ≤ (299 / 500 : ℝ) := by
  have hinit : HistoricalThirdCoarse.initial (d.e : ℝ) ≤
      (299 / 500 : ℝ) := by
    dsimp [HistoricalThirdCoarse.initial, extendedDistributionCap]
    linarith
  change P1CoarseFirstCubeFallbackMargin.effectiveExponent
      (d.e : ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre) ≤ _
  unfold P1CoarseFirstCubeFallbackMargin.effectiveExponent
  split_ifs
  · exact (HistoricalThirdCoarse.exponent_le_initial
      (d.e : ℝ) d.chi he d.m _).trans hinit
  · exact hinit

/-- Both literal second/third fallback branches use v, rather than a
new upper-bound field. -/
theorem fallbackSeed_le_initial_ceiling
    (d : OriginalData) (he : (0 : ℝ) ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) :
    fallbackSeed d N pre ≤ (299 / 500 : ℝ) := by
  unfold fallbackSeed
  split_ifs
  · exact tent_le_initial_ceiling _
  · exact tent_le_initial_ceiling _
  · exact originalSeed_le_initial_ceiling d he N pre

/-- The real original common third parent, with both old and corrected
fallback actions, obeys the same subunit ceiling on EVERY history. -/
theorem lambda3_le_initial_ceiling
    (d : OriginalData) (he : (0 : ℝ) ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) :
    lambda3 d N pre ≤ (299 / 500 : ℝ) := by
  change max (originalSeed d N pre) (fallbackSeed d N pre) ≤ _
  exact max_le
    (originalSeed_le_initial_ceiling d he N pre)
    (fallbackSeed_le_initial_ceiling d he N pre)

/-- The original fourth finite producer retains its real lambda3 seed,
and EVERY buffered pointwise row is below the same bound. -/
theorem exponent4_le_initial_ceiling
    (d : OriginalData) (he : (0 : ℝ) ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) :
    P5OriginalCommonRefinedConstructor.exponent4 d N pre ≤
      (299 / 500 : ℝ) := by
  unfold P5OriginalCommonRefinedConstructor.exponent4
  split_ifs
  · apply finiteMax_le
    · exact lambda3_le_initial_ceiling d he N pre
    · intro r _ _
      rw [P2OriginalFourthCapProducerInterface.ProducerRow.bufferedCandidate_eq]
      have hv := tent_le_initial_ceiling
        (∑ i ∈ r.selected, primeHistoryLogCoordinates N 4 pre i)
      linarith
  · exact lambda3_le_initial_ceiling d he N pre

/-- The original fifth finite producer keeps the actual fourth ancestor.
Its own pointwise candidate uses precisely the original selected mask. -/
theorem exponent5_le_initial_ceiling
    (d : OriginalData) (he : (0 : ℝ) ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) :
    P5OriginalCommonRefinedConstructor.exponent5 d N pre ≤
      (299 / 500 : ℝ) := by
  unfold P5OriginalCommonRefinedConstructor.exponent5
  split_ifs
  · apply finiteMax_le
    · exact exponent4_le_initial_ceiling d he N (rosserAncestor 4 pre)
    · intro r _ _
      exact (P1OriginalVariableFifthContinuation.candidate_le_global_cap
        (d.e : ℝ) he r.selected (primeHistoryLogCoordinates N 5 pre)).trans
          (by norm_num [VariableEnvelope.cap])
  · exact exponent4_le_initial_ceiling d he N (rosserAncestor 4 pre)

/-- The exact raw fifth predecessor is globally bounded, with no
source-owner, accepted action, or N-dependent theta as a hypothesis. -/
theorem actualParent5_le_initial_ceiling
    (d : OriginalData) (he : (0 : ℝ) ≤ (d.e : ℝ))
    (N : ℝ) (pre : List ℕ) :
    actualParent5 d N pre ≤ (299 / 500 : ℝ) := by
  change P5OriginalCommonRefinedConstructor.exponent5 d N
    (rosserAncestor 5 pre) ≤ _
  exact exponent5_le_initial_ceiling d he N _

/-- The finite fifth predecessor preserves the original third seed
once; its rounded fifth candidate cannot exceed the raw bound. -/
theorem finite_cap5_le_initial_ceiling
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : (0 : ℝ) ≤ ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (pre : List ℕ) :
    cap5 n e q om N pre ≤ (299 / 500 : ℝ) := by
  let d := P4AOriginalCompleteSixthChronology.data e q om
  have hd : (0 : ℝ) ≤ (d.e : ℝ) := he
  have hs := originalSeed_le_initial_ceiling d hd N pre
  have he5 := exponent5_le_initial_ceiling d hd N pre
  have hr : (rounded n (P5OriginalCommonRefinedConstructor.exponent5 d N pre) : ℝ) ≤
      (299 / 500 : ℝ) := by
    have hmono := rounded_mono n he5
    have hbase := (rounded_error n VariableEnvelope.cap
      (by norm_num [VariableEnvelope.cap]) le_rfl).2.2
    exact hmono.trans (hbase.trans (by norm_num [VariableEnvelope.cap]))
  rw [cap5_eq_protect]
  change max (originalSeed d N pre)
    ((rounded n (P5OriginalCommonRefinedConstructor.exponent5 d N pre) : ℝ)) ≤ _
  exact max_le hs hr

/-- All eight chronological raw sixth stages, even on third-inactive
histories, have the original upper envelope. Later stages retain their
actual current-dependent guards, not re-evaluated rounded guards. -/
theorem raw_currentSixth_le_initial_ceiling
    (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : (0 : ℝ) ≤ ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (pre : List ℕ) :
    P4AOriginalCompleteSixthChronology.currentSixthExponent e q om N pre ≤
      (299 / 500 : ℝ) := by
  have hfifth : P4AOriginalCompleteSixthChronology.fifth e q om N pre ≤
      (299 / 500 : ℝ) := by
    change actualParent5 (P4AOriginalCompleteSixthChronology.data e q om) N pre ≤ _
    exact actualParent5_le_initial_ceiling _ he N pre
  exact P4AOriginalCompleteSixthChronology.current_le_of_subset_tents
    e q om N (299 / 500 : ℝ) pre hfifth
    (fun m _ => tent_le_initial_ceiling _)

/-- ACTUAL new sixth accepted actions, their inherited finite fifth seed,
and third-inactive untouched raw chronology all satisfy one uniform bound.
This does not identify their source/gain or bound complete leaf moduli. -/
theorem level6_all_histories_le_initial_ceiling
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : (0 : ℝ) ≤ ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (pre : List ℕ) :
    P4AOriginalFull87LicensedSixthPolicy.level6Exponent n e q om N pre ≤
      (299 / 500 : ℝ) := by
  unfold P4AOriginalFull87LicensedSixthPolicy.level6Exponent
  split_ifs
  · have hl := P4AOriginalFull87LicensedSixthCeiling.licensedCap_le_real_fifth_or_envelope
      n e q om N pre
    apply hl.trans
    apply max_le
    · exact finite_cap5_le_initial_ceiling n e q om N he (rosserAncestor 5 pre)
    · have hw := width_pos n
      have hc : VariableEnvelope.cap ≤ (299 / 500 : ℝ) := by
        norm_num [VariableEnvelope.cap]
      linarith
  · exact raw_currentSixth_le_initial_ceiling e q om N he pre

/-- The actual sixth frozen level is bounded by the fixed power N^(.598).
No claim about complete a*b or all terminal rough leaf products is made. -/
theorem level6_power_le_initial_ceiling
    (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (he : (0 : ℝ) ≤ ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 ≤ N) (pre : List ℕ) :
    N ^ P4AOriginalFull87LicensedSixthPolicy.level6Exponent n e q om N pre ≤
      N ^ (299 / 500 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hN
    (level6_all_histories_le_initial_ceiling n e q om N he pre)

end
end ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
