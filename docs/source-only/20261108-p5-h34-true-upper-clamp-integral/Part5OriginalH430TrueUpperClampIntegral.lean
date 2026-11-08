import ImbalancedChen.Part5OriginalH430TrueUpperU34Phase

/-!
P5.6 / h34 — integral-level use of the *actual* upper U3/U4 H430
coefficient, following the literal phase packet.

The U3 tail clamp occupies a nonzero interval.  Its upper cost is an
ordinary real constant times the genuine tail branch weight.  This file
carries that identity under the real set integral, retaining the negative
1/4 Chen root sign, and relates the U3/U4 common actual domain without
replacing either labelled occurrence or claiming a historical owner.

The denominator bound is proved from the true interval geometry, rather
than a fictitious zero-measure clamp.  No U3/U4 integer count, PP input,
Euler payment, or original selected-count permission is inferred here.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430TrueUpperClampIntegral

noncomputable section

open MeasureTheory Set
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables
open Part5UpperTables.OriginalU34
open Part5OriginalH430TrueUpperU34Phase

/-- The real positive-width H430 clamp interval, with the original U3
right endpoint (not the ordinary lower h-start). -/
def trueU3ClampBand : Set ℝ := Ico u3TailClampStart (1 / 3)

/-- On the actual tail clamp band, both factors in its genuine
denominator are positive. -/
theorem true_clamp_denominator_positive {t : ℝ}
    (ht : t ∈ trueU3ClampBand) :
    0 < tailResidual t * t := by
  change t ∈ Ico u3TailClampStart (1 / 3 : ℝ) at ht
  have hs : (0 : ℝ) < u3TailClampStart := by
    norm_num [u3TailClampStart, a]
  have htpos : 0 < t := lt_of_lt_of_le hs ht.1
  have hrpos : 0 < tailResidual t := by
    dsimp [tailResidual]
    linarith [ht.2]
  exact mul_pos hrpos htpos

/-- The sharp simple lower bound comes from
(1/3-t)*(t-1/6) >= 0, not a uniform residual approximation. -/
theorem true_clamp_denominator_lower {t : ℝ}
    (ht : t ∈ trueU3ClampBand) :
    (1 / 18 : ℝ) ≤ tailResidual t * t := by
  change t ∈ Ico u3TailClampStart (1 / 3 : ℝ) at ht
  have hs : (1 / 6 : ℝ) ≤ u3TailClampStart := by
    norm_num [u3TailClampStart, a]
  have htlo : (1 / 6 : ℝ) ≤ t := hs.trans ht.1
  have hprod : 0 ≤ ((1 / 3 : ℝ) - t) * (t - 1 / 6) :=
    mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr htlo)
  dsimp [tailResidual]
  nlinarith [hprod]

/-- Exact real tail weight is positive and bounded by 72 throughout
the finite positive-width clamp band; no H430 table positivity is used. -/
theorem true_clamp_tail_weight_bounds {t : ℝ}
    (ht : t ∈ trueU3ClampBand) :
    0 < branchWeight tailResidual t ∧ branchWeight tailResidual t ≤ 72 := by
  have hden := true_clamp_denominator_positive ht
  have hlo := true_clamp_denominator_lower ht
  constructor
  · unfold branchWeight
    exact div_pos (by norm_num) hden
  · unfold branchWeight
    apply (div_le_iff₀ hden).mpr
    nlinarith

/-- The U3 upper coefficient on the first genuine H430 phase may be
moved *inside the original integral* without a scalar-owner premise. -/
theorem u3_first_phase_integral_exact :
    (∫ t in Ico a tailCutoff, U3H430Coefficient t) =
      ∫ t in Ico a tailCutoff,
        (upperAmplitude (mainResidual t / a) -
          upperRoot H430Numerators (mainResidual t / a)) *
          branchWeight mainResidual t := by
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact u3_first_phase_true_H430 ht

/-- The distinct middle tail interval uses the unclamped raw root. -/
theorem u3_middle_phase_integral_exact :
    (∫ t in Ico tailCutoff u3TailClampStart, U3H430Coefficient t) =
      ∫ t in Ico tailCutoff u3TailClampStart,
        (upperAmplitude (tailResidual t / a) -
          upperRoot H430Numerators (tailResidual t / a)) *
          branchWeight tailResidual t := by
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact u3_middle_phase_true_H430 ht

/-- The final U3 upper band factors out the genuine H430 knot-2
scalar. This is an integral, not merely a pointwise phase statement. -/
theorem u3_clamped_band_integral_exact :
    (∫ t in trueU3ClampBand, U3H430Coefficient t) =
      (upperAmplitude 2 - upperRoot H430Numerators 2) *
        ∫ t in trueU3ClampBand, branchWeight tailResidual t := by
  calc
    _ = ∫ t in trueU3ClampBand,
          (upperAmplitude 2 - upperRoot H430Numerators 2) *
            branchWeight tailResidual t := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t ht
      exact u3_clamped_phase_true_H430 ht
    _ = _ := by rw [integral_const_mul]

/-- The negative quarter weight is the actual U3 sign in Chen's
eleven-occurrence root functional. No positivity of the H430 cost is
inferred and no different root occurrence is merged into this one. -/
theorem u3_clamped_band_signed_quarter_exact :
    (∫ t in trueU3ClampBand, -(U3H430Coefficient t) / 4) =
      (-((upperAmplitude 2 - upperRoot H430Numerators 2) / 4)) *
        ∫ t in trueU3ClampBand, branchWeight tailResidual t := by
  calc
    _ = ∫ t in trueU3ClampBand,
          (-((upperAmplitude 2 - upperRoot H430Numerators 2) / 4)) *
            branchWeight tailResidual t := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t ht
      rw [u3_clamped_phase_true_H430 ht]
      ring
    _ = _ := by rw [integral_const_mul]

/-- The full literal U4 upper domain has no H430 clamp and retains its
genuine main-envelope residual, not the ordinary lower h-start. -/
theorem u4_entire_upper_integral_exact :
    (∫ t in Ico a (59 / 250 : ℝ), U4H430Coefficient t) =
      ∫ t in Ico a (59 / 250 : ℝ),
        (upperAmplitude (mainResidual t / a) -
          upperRoot H430Numerators (mainResidual t / a)) *
          branchWeight mainResidual t := by
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact u4_entire_phase_true_H430 ht

/-- The two labelled upper costs agree on their genuine common
coordinate interval. This identity does not identify their original
q/tag count sources or license double payment by one historical event. -/
theorem u3_u4_common_integral_exact :
    (∫ t in Ico a (59 / 250 : ℝ), U3H430Coefficient t) =
      ∫ t in Ico a (59 / 250 : ℝ), U4H430Coefficient t := by
  apply setIntegral_congr_fun measurableSet_Ico
  intro t ht
  exact U3_eq_main_on_U4 ht

end
end ImbalancedChen.Part5OriginalH430TrueUpperClampIntegral
