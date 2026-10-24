import ImbalancedChen.P1HistoricalFourthFullCellIntegral

/-!
Signs of the full historical fourth upper-residual integral.

The actual canonical upper factor is antitone on s>1: the existing
`upper_antitone_gt_one` proves this from the genuine summable odd Suzuki
source layers. The closed endpoint and actual full-cell integral are reused
from the sibling P1 modules; neither object is redefined here.

All sign results concern the limiting continuous residuals and integrals.
No monotonicity of finite signed arithmetic Rosser densities is asserted.
-/

namespace ImbalancedChen.P1FourthIntegralSign

noncomputable section

open Set MeasureTheory
open MathlibNt.SieveTheory
open OriginalU2CoupledRecurrenceSourceOnly
open P1FourthNearOneKernel P1FourthFullCellIntegral
open scoped Classical BigOperators

/-- Remove only the positive normalization from the actual source theorem. -/
theorem canonicalUpper_antitone_gt_one :
    AntitoneOn suzukiContinuousUpperFactor (Ioi 1) := by
  intro x hx y hy hxy
  have h := upper_antitone_gt_one hx hy hxy
  change suzukiContinuousUpperFactor y / A ≤ suzukiContinuousUpperFactor x / A at h
  exact (div_le_div_iff_of_pos_right A_pos).mp h

/-- The filled endpoint has the correct antitone order as well. -/
theorem closedUpper_antitone_ge_one : AntitoneOn closedUpper (Ici 1) := by
  intro x hx y hy hxy
  change 1 ≤ x at hx
  change 1 ≤ y at hy
  by_cases hx1 : x = 1
  · subst x
    simpa only [closedUpper_one] using closedUpper_le_amplitude hy
  · have hxgt : 1 < x := by linarith
    have hygt : 1 < y := hxgt.trans_le hxy
    rw [closedUpper_eq_actual (s := x) hxgt, closedUpper_eq_actual (s := y) hygt]
    exact canonicalUpper_antitone_gt_one hxgt hygt hxy

theorem residual_mono_level (t : Fin 4 → ℝ) (ht : 0 < t (Fin.last 3))
    {old new : ℝ} (hlevel : old ≤ new) : residual old t ≤ residual new t := by
  exact div_le_div_of_nonneg_right (sub_le_sub_right hlevel _) ht.le

theorem maxOneNormalized_antitone_level (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3)) {old new : ℝ} (hlevel : old ≤ new) :
    maxOneNormalized new t ≤ maxOneNormalized old t := by
  apply div_le_div_of_nonneg_right _ ht.le
  exact closedUpper_antitone_ge_one (le_max_left _ _) (le_max_left _ _)
    (max_le_max le_rfl (residual_mono_level t ht hlevel))

theorem extendedProfile_antitone_level (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3)) {old new : ℝ} (hlevel : old ≤ new) :
    extendedProfile new t ≤ extendedProfile old t := by
  exact mul_le_mul_of_nonneg_left
    (maxOneNormalized_antitone_level t ht hlevel) (by positivity)

theorem normalized_antitone_legal (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3)) {old new : ℝ} (hlevel : old ≤ new)
    (hold : 1 ≤ residual old t) : normalized new t ≤ normalized old t := by
  have hr := residual_mono_level t ht hlevel
  exact div_le_div_of_nonneg_right
    (closedUpper_antitone_ge_one hold (hold.trans hr) hr) ht.le

theorem density_antitone_legal (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3)) {old new : ℝ} (hlevel : old ≤ new)
    (hold : 1 ≤ residual old t) : density new t ≤ density old t := by
  exact mul_le_mul_of_nonneg_left
    (normalized_antitone_legal t ht hlevel hold) (by positivity)

/-- The literal actual profile is used only on its strict legal domain. -/
theorem rawProfile_antitone_legal (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3)) {old new : ℝ} (hlevel : old ≤ new)
    (hold : 1 < residual old t) :
    fourthPlusProfileP1 new t ≤ fourthPlusProfileP1 old t := by
  have hnew : 1 < residual new t := hold.trans_le (residual_mono_level t ht hlevel)
  have h := density_antitone_legal t ht hlevel hold.le
  rw [density_eq_actual old t hold, density_eq_actual new t hnew] at h
  exact h

theorem extendedProfile_nonneg (lambda : ℝ) (t : Fin 4 → ℝ)
    (ht : 0 < t (Fin.last 3)) : 0 ≤ extendedProfile lambda t := by
  exact mul_nonneg (by positivity)
    (div_nonneg (closedUpper_nonneg (le_max_left _ _)) ht.le)

theorem jointCell_coordinates_pos (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) (i : Fin 4) : 0 < t i := by
  exact (show (0 : ℝ) < (D.a : ℝ) by exact_mod_cast ha).trans_le
    (jointCell_coordinate_bounds D hab j ht i).1

theorem reciprocalWeight_nonneg_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 4 → Fin (D.m + 1))
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) : 0 ≤ reciprocalWeight t := by
  exact Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr
    (jointCell_coordinates_pos D ha hab j ht i).le)

/-- levelCheck compares the original effective third ancestor with new4. -/
theorem extendedProfile_old_sub_new_nonneg_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    0 ≤ extendedProfile (D.old4 j : ℝ) t - extendedProfile (D.cap4 j : ℝ) t := by
  have hlevel : (D.old4 j : ℝ) ≤ D.cap4 j := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj
  exact sub_nonneg.mpr (extendedProfile_antitone_level t
    (jointCell_coordinates_pos D ha hab j ht _) hlevel)

theorem rawProfile_old_sub_new_nonneg_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    0 ≤ fourthPlusProfileP1 (D.old4 j : ℝ) t - fourthPlusProfileP1 (D.cap4 j : ℝ) t := by
  have hlevel : (D.old4 j : ℝ) ≤ D.cap4 j := by
    exact_mod_cast (D.levelCheck_sound hcheck).2.1 j hj
  exact sub_nonneg.mpr (rawProfile_antitone_legal t
    (jointCell_coordinates_pos D ha hab j ht _) hlevel
    (old_residual_gt_one D ha hab j ht))

theorem fullCellIntegrand_nonneg_on_joint (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4)
    {t : Fin 4 → ℝ} (ht : t ∈ jointCell D j) :
    0 ≤ (extendedProfile (D.old4 j : ℝ) t - extendedProfile (D.cap4 j : ℝ) t) *
      reciprocalWeight t := by
  exact mul_nonneg
    (extendedProfile_old_sub_new_nonneg_on_joint D ha hab hcheck j hj ht)
    (reciprocalWeight_nonneg_on_joint D ha hab j ht)

/-- This is the sibling's independently defined full cell integral. -/
theorem fullCellIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    0 ≤ fullCellIntegral D j := by
  exact setIntegral_nonneg (measurableSet_jointCell D j)
    (fun _ ht => fullCellIntegrand_nonneg_on_joint D ha hab hcheck j hj ht)

theorem fullIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true) :
    0 ≤ fullIntegral D := by
  exact Finset.sum_nonneg (fun j hj => fullCellIntegral_nonneg D ha hab hcheck j hj)

theorem dictionaryCellIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    0 ≤ D.fourthCellIntegralP1 j := by
  rw [← fullCellIntegral_eq_dictionary D ha hab hcheck j hj]
  exact fullCellIntegral_nonneg D ha hab hcheck j hj

theorem dictionaryCorrectionIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true) :
    0 ≤ D.fourthCorrectionIntegralP1 := by
  rw [← fullIntegral_eq_dictionary D ha hab hcheck]
  exact fullIntegral_nonneg D ha hab hcheck

/-- The already proved null parent-wall dictionary carries the same sign
to the full weak-gate integral; no discrete wall is discarded. -/
theorem weakJointCellIntegral_nonneg (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hcheck : D.levelCheck = true)
    (j : Fin 4 → Fin (D.m + 1)) (hj : j ∈ D.cells4) :
    0 ≤ ∫ t in weakJointCell D j,
      (extendedProfile (D.old4 j : ℝ) t - extendedProfile (D.cap4 j : ℝ) t) *
        reciprocalWeight t := by
  rw [← integral_jointCell_eq_weakJointCell D j]
  exact fullCellIntegral_nonneg D ha hab hcheck j hj

end

end ImbalancedChen.P1FourthIntegralSign
