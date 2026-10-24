import ImbalancedChen.CurrentNumericalTransfer
import ImbalancedChen.CurrentChenUpsilon6KernelBuffer
import Mathlib.Tactic.Ring

/-!
# Original lower coefficient arithmetic, P5 group, 24 October z

SOURCE ONLY; UNCOMPILED. No number-theoretic estimate is asserted.

These are the original rational inputs in the frozen manuscript repository,
`global-selected-numeric-completion-20261010.json`, fields
`direct_lower_terms`, `lower_selected_integrals`, and its subsequent ledger.
The final substitutions come from `corpus-renewal-improvement-assembly-20261010.json`.
`directReconstruction` means the complete *rational endpoint reconstruction*;
it is not a name for the true Chen mean or a certified integral.

The original eleven occurrences have ten stored endpoints: U10+U11 is one
joint upper endpoint. No unsupported split of that endpoint is introduced.
The historical L6 value is explicitly named `savedL6`; it is not identified
with the corrected Runbo product-domain integral by this file.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section

open MeasureTheory

def savedL1 : ℝ := 16277054284462455830437051 / 1208925819614629174706176
def savedL2 : ℝ := 8586547972866441938526945 / 1208925819614629174706176
def savedL5 : ℝ := 1435297520488717065538013 / 604462909807314587353088
def savedL6 : ℝ := 3650774173156900914101685 / 1208925819614629174706176
def savedU3 : ℝ := 24556212011015763559960381 / 1208925819614629174706176
def savedU4 : ℝ := 16995904880905900972965867 / 1208925819614629174706176
def savedU7 : ℝ := 1672464594622060236183097 / 1208925819614629174706176
def savedU8 : ℝ := 4904703865205402441361491 / 1208925819614629174706176
def savedU9 : ℝ := 3937512077512215599969887 / 1208925819614629174706176
def savedU1011 : ℝ := 408427750921032759710349 / 604462909807314587353088

/-- Literal manuscript root, in Chen-quarter units. -/
def root (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ) : ℝ :=
  (3 * L1 + L2 + L5 + L6 - U3 - U4 - 2 * U7 - U8 - U9 - U1011) / 4

def savedRoot : ℝ := root savedL1 savedL2 savedL5 savedL6
  savedU3 savedU4 savedU7 savedU8 savedU9 savedU1011

theorem savedRoot_value :
    savedRoot = 9382962514662675908971291 / 4835703278458516698824704 := by
  norm_num [savedRoot, root, savedL1, savedL2, savedL5, savedL6,
    savedU3, savedU4, savedU7, savedU8, savedU9, savedU1011]

/-- Already in Chen units: this gain does not receive a second quarter. -/
def priorityParentReplacement : ℝ := 106520738437439293219 / 604462909807314587353088
def ordinaryStartChange : ℝ :=
  -(141178561378510030798830300751831 / 2596148429267413814265248164610048)
def removedH248 : ℝ := 43198430030913582340978331223541 / 2596148429267413814265248164610048
def savedI3a : ℝ := 286155423045837952285758520439 / 2596148429267413814265248164610048
def savedI3h : ℝ := 558585322622278274261130249927829 / 5192296858534827628530496329220096
def savedI4a : ℝ := 43583968139129322236011742355 / 5192296858534827628530496329220096
def savedI4h : ℝ := 36771509969327265106013502711805 / 1298074214633706907132624082305024
def savedI5a : ℝ := 1289344564544057031 / 302231454903657293676544
def savedI5h : ℝ := 2801031391809399207203 / 1208925819614629174706176
def slantedRestoration : ℝ := 5900940623085383187303 / 1208925819614629174706176

def weightedSixIntegrals : ℝ :=
  3 * savedI3a + savedI3h + 3 * savedI4a + savedI4h + 3 * savedI5a + savedI5h

/-- Entire obsolete H248 correction is subtracted before the new start. -/
def directAtK0 : ℝ := savedRoot + priorityParentReplacement +
  (ordinaryStartChange - removedH248 + weightedSixIntegrals + slantedRestoration) / 4

def adoptedAtK0 : ℝ :=
  10169845841195726878936621165692227 / 5192296858534827628530496329220096

theorem directAtK0_value :
    directAtK0 =
      10169845841606139705128569148493405 / 5192296858534827628530496329220096 := by
  rw [directAtK0, savedRoot_value]
  norm_num [priorityParentReplacement, ordinaryStartChange, removedH248,
    weightedSixIntegrals, savedI3a, savedI3h, savedI4a, savedI4h,
    savedI5a, savedI5h, slantedRestoration]

def retainedRoundingSurplus : ℝ :=
  205206413095973991400589 / 2596148429267413814265248164610048

theorem directAtK0_eq_adopted_add_surplus :
    directAtK0 = adoptedAtK0 + retainedRoundingSurplus := by
  rw [directAtK0_value]
  norm_num [adoptedAtK0, retainedRoundingSurplus]

theorem retainedRoundingSurplus_pos : 0 < retainedRoundingSurplus := by
  norm_num [retainedRoundingSurplus]

def K0 : ℝ := 67619 / 10000
def originalFeedbackSlope : ℝ :=
  8598593512394265568060189496377494375 / 21943620079829156838350226955345854464
def table248to312 : ℝ := 1332969598935451086936362257 / 1298074214633706907132624082305024
def table312to430 : ℝ := 282218209595396890358020075 / 1298074214633706907132624082305024
def E0Gross : ℝ := 2095161 / 1000000000
def E1Gross : ℝ := 3799514 / 1000000000
def oldSavedFloorPayment : ℝ := 2372094 / 1000000000
def replacementSavedFloorPayment : ℝ := 466977 / 200000000
def extraSameMaskGross : ℝ := 558583 / 1000000000

def baselineContinuation : ℝ := originalFeedbackSlope * (K0 - currentK) +
  table248to312 + table312to430 + E0Gross + E1Gross - oldSavedFloorPayment

def sameMaskIncrement : ℝ :=
  extraSameMaskGross + (oldSavedFloorPayment - replacementSavedFloorPayment)

theorem sameMaskIncrement_value : sameMaskIncrement = 37237 / 62500000 := by
  norm_num [sameMaskIncrement, extraSameMaskGross, oldSavedFloorPayment,
    replacementSavedFloorPayment]

/-- The adopted baseline is reconstructed from its original K0 endpoint. -/
theorem adopted_baseline_value :
    adoptedAtK0 + baselineContinuation =
      1345575129530003739571681432301188857312754737 /
        685738127494661151198444592354557952000000000 := by
  norm_num [adoptedAtK0, baselineContinuation, originalFeedbackSlope, K0, currentK,
    table248to312, table312to430, E0Gross, E1Gross, oldSavedFloorPayment]

def directReconstruction : ℝ := directAtK0 + baselineContinuation + sameMaskIncrement
def adoptedReconstruction : ℝ := adoptedAtK0 + baselineContinuation + sameMaskIncrement

theorem direct_eq_adopted_add_surplus :
    directReconstruction = adoptedReconstruction + retainedRoundingSurplus := by
  dsimp [directReconstruction, adoptedReconstruction]
  rw [directAtK0_eq_adopted_add_surplus]
  ring

theorem adoptedReconstruction_value :
    adoptedReconstruction =
      1345983686820460038728276256001756964104092721 /
        685738127494661151198444592354557952000000000 := by
  rw [adoptedReconstruction, adopted_baseline_value, sameMaskIncrement_value]
  norm_num

/-- The selected sixth saved endpoint loses four times the quarter-unit payment.
This is a saved-estimator identity, not an upper estimate for a removed count. -/
theorem retained_savedL6_value :
    savedL6 - 4 * replacementSavedFloorPayment =
      1421673188323272382945058469141 / 472236648286964521369600000000 := by
  norm_num [savedL6, replacementSavedFloorPayment]

def baselineReserve : ℝ :=
  2504748318091942808229694219379799307550987 /
    5485905019957289209587556738836463616000000000
def eachReserve : ℝ := baselineReserve + sameMaskIncrement / 8

theorem eachReserve_value :
    eachReserve = 2913305608548241964824517919947906098888971 /
      5485905019957289209587556738836463616000000000 := by
  rw [eachReserve, sameMaskIncrement_value]
  norm_num [baselineReserve]

theorem exact_currentC_slack :
    adoptedReconstruction - 2 * eachReserve - currentC =
      13457260926863633771775678584711245753 /
        2742952509978644604793778369418231808000000000 := by
  rw [adoptedReconstruction_value, eachReserve_value]
  norm_num [currentC]

theorem currentC_lt_adopted_after_reserves :
    currentC < adoptedReconstruction - 2 * eachReserve := by
  have h := exact_currentC_slack
  have hp : (0 : ℝ) < 13457260926863633771775678584711245753 /
      2742952509978644604793778369418231808000000000 := by norm_num
  linarith

theorem currentC_lt_direct_after_reserves :
    currentC < directReconstruction - 2 * eachReserve := by
  rw [direct_eq_adopted_add_surplus]
  linarith [currentC_lt_adopted_after_reserves, retainedRoundingSurplus_pos]

/-- The exact original lower coefficient functional, including every original
endpoint correction; a changed sixth coefficient is inserted in its own slot. -/
def reconstructionWithSixth (sixth : ℝ) : ℝ :=
  root savedL1 savedL2 savedL5 sixth savedU3 savedU4 savedU7 savedU8 savedU9 savedU1011 +
    priorityParentReplacement +
    (ordinaryStartChange - removedH248 + weightedSixIntegrals + slantedRestoration) / 4 +
    baselineContinuation + sameMaskIncrement

/-- No equality between historical and corrected sixth coefficients is assumed. -/
theorem sixth_substitution_exact (sixth : ℝ) :
    directReconstruction - reconstructionWithSixth sixth = (savedL6 - sixth) / 4 := by
  dsimp [directReconstruction, directAtK0, savedRoot, reconstructionWithSixth, root]
  ring

/-- Quantitative error in this individual original coefficient is quartered.
The hypothesis is a local numerical enclosure, not a complete ledger. -/
theorem sixth_substitution_error_le (sixth error : ℝ)
    (h : |savedL6 - sixth| ≤ error) :
    |directReconstruction - reconstructionWithSixth sixth| ≤ error / 4 := by
  rw [sixth_substitution_exact, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- The actual ordinary corrected Runbo coefficient at zero buffer. Its domain
is the original half-open pair rectangle intersected with u+t ≤ 833/2500.
It is intentionally not identified with the enhanced h248 saved L6. -/
def correctedOrdinarySixth : ℝ :=
  ∫ x in currentChenUpsilon6LogDomain 0, currentChenUpsilon6OrdinaryKernel x

theorem correctedOrdinarySixth_integrable :
    IntegrableOn currentChenUpsilon6OrdinaryKernel (currentChenUpsilon6LogDomain 0) := by
  exact integrableOn_currentChenUpsilon6OrdinaryKernel_domain 0

/-- This exact residual is the missing original sixth comparison exposed by
the algebra. It is not silently consumed as a nonnegative reserve. -/
theorem correctedOrdinarySixth_gap_exact :
    directReconstruction - reconstructionWithSixth correctedOrdinarySixth =
      (savedL6 - correctedOrdinarySixth) / 4 := by
  exact sixth_substitution_exact correctedOrdinarySixth

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
