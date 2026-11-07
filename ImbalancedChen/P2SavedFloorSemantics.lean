import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity
import ImbalancedChen.Certificates.PairedV2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
SOURCE_WRITTEN_UNCOMPILED. Code-only candidate, 2026-10-24.

This file supplies an analytic meaning for a lower ordinary pair estimator,
including the ACTUAL first saved E0 row. The zero claim below is about the
existing normalized lower sieve factor, not merely the stored numeral zero.

The ordinary high-t residual is 57/64 - (5/2)t - u. The profile is the
existing actualExtendedThirdLowerFactor: the actual normalized continuous
lower sieve factor, extended by zero at/below 2. Its name reflects its first
consumer; no third-prefix coordinates occur in the pair kernel below.

The independent directed corner estimator below is NOT asserted equal to
the historical Python I80 evaluation. Establishing that equality for the
positive saved rows still needs the actual sharp pair512 producer and its
ordinary/defect table suppliers. In particular this file does not establish
the sum 11290806845175652020270 or the adopted replacement loss bound.
-/

namespace ImbalancedChen.P2SavedFloorSemantics

noncomputable section

open MeasureTheory Set
open scoped Interval

def ordinaryA : ℝ := 417 / 5000

def ordinaryResidual (t u : ℝ) : ℝ := 57 / 64 - (5 / 2) * t - u

/-- The literal ordinary pair cap, before choosing its high-t branch. -/
def ordinaryPairCap (t : ℝ) : ℝ := min ((1 + t) / 2) (57 / 64 - (3 / 2) * t)

theorem ordinaryResidual_eq_cap_residual {t u : ℝ} (ht : (25 / 128 : ℝ) ≤ t) :
    ordinaryResidual t u = ordinaryPairCap t - t - u := by
  have hbranch : (57 / 64 : ℝ) - (3 / 2) * t ≤ (1 + t) / 2 := by
    linarith
  rw [ordinaryPairCap, min_eq_right hbranch]
  unfold ordinaryResidual
  ring

/-- The actual ordinary lower pair density, in the normalization in which
the eleven-term pair contribution has coefficient 4 before Chen division.
The lower factor is divided by the fixed smallest-prime exponent a. -/
def ordinaryPairKernel (t u : ℝ) : ℝ :=
  4 * actualExtendedThirdLowerFactor (ordinaryResidual t u / ordinaryA) /
    (ordinaryA * t * u)

/-- Literal real iterated integral on a closed outer pair rectangle.
Interval integrals ignore only their one-dimensional endpoint sets. -/
def ordinaryCellIntegral (tl tr ul ur : ℝ) : ℝ :=
  ∫ t in tl..tr, ∫ u in ul..ur, ordinaryPairKernel t u

theorem ordinaryA_pos : 0 < ordinaryA := by
  norm_num [ordinaryA]

theorem ordinaryResidual_antitone {t₁ t₂ u₁ u₂ : ℝ}
    (ht : t₁ ≤ t₂) (hu : u₁ ≤ u₂) :
    ordinaryResidual t₂ u₂ ≤ ordinaryResidual t₁ u₁ := by
  dsimp [ordinaryResidual]
  linarith

theorem ordinaryPairKernel_nonneg {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    0 ≤ ordinaryPairKernel t u := by
  unfold ordinaryPairKernel
  exact div_nonneg (mul_nonneg (by norm_num)
    (actualExtendedThirdLowerFactor_nonneg _))
    (mul_nonneg (mul_nonneg ordinaryA_pos.le ht.le) hu.le)

/-- An entire cell whose largest residual is at most 2a really has zero
ordinary lower density. This is stronger than an integer-floor check. -/
theorem ordinaryPairKernel_eq_zero_of_residual_le_two {t u : ℝ}
    (h : ordinaryResidual t u ≤ 2 * ordinaryA) :
    ordinaryPairKernel t u = 0 := by
  have hs : ordinaryResidual t u / ordinaryA ≤ 2 :=
    (div_le_iff₀ ordinaryA_pos).mpr h
  simp only [ordinaryPairKernel,
    actualExtendedThirdLowerFactor_of_le_two hs, mul_zero, zero_div]

theorem ordinaryPairKernel_eq_zero_on_rectangle {tl tr ul ur : ℝ}
    (hzero : ordinaryResidual tl ul ≤ 2 * ordinaryA)
    {t u : ℝ} (ht : t ∈ Icc tl tr) (hu : u ∈ Icc ul ur) :
    ordinaryPairKernel t u = 0 := by
  apply ordinaryPairKernel_eq_zero_of_residual_le_two
  exact (ordinaryResidual_antitone ht.1 hu.1).trans hzero

/-- Genuine integral semantics for zero-floor E0 rectangles; there is no
integrability premise because the function is proved identically zero on
the actual integration rectangle. -/
theorem ordinaryCellIntegral_eq_zero {tl tr ul ur : ℝ}
    (ht : tl ≤ tr) (hu : ul ≤ ur)
    (hzero : ordinaryResidual tl ul ≤ 2 * ordinaryA) :
    ordinaryCellIntegral tl tr ul ur = 0 := by
  have hinner : ∀ t ∈ Icc tl tr,
      (∫ u in ul..ur, ordinaryPairKernel t u) = 0 := by
    intro t htl
    calc
      (∫ u in ul..ur, ordinaryPairKernel t u) = ∫ _u in ul..ur, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hul
        rw [Set.uIcc_of_le hu] at hul
        exact ordinaryPairKernel_eq_zero_on_rectangle hzero htl hul
      _ = 0 := by simp
  unfold ordinaryCellIntegral
  calc
    (∫ t in tl..tr, ∫ u in ul..ur, ordinaryPairKernel t u) =
        ∫ _t in tl..tr, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t htl
      rw [Set.uIcc_of_le ht] at htl
      exact hinner t htl
    _ = 0 := by simp

/-- The lower-right corner gives a valid Darboux density throughout a
positive high-t pair cell. Both the actual lower factor and its positive
denominator are compared in the necessary directions. -/
theorem ordinaryPairKernel_corner_le {tl tr ul ur t u : ℝ}
    (htl : 0 < tl) (hul : 0 < ul)
    (ht : t ∈ Icc tl tr) (hu : u ∈ Icc ul ur) :
    ordinaryPairKernel tr ur ≤ ordinaryPairKernel t u := by
  have ht0 : 0 < t := htl.trans_le ht.1
  have hu0 : 0 < u := hul.trans_le hu.1
  have htr0 : 0 < tr := ht0.trans_le ht.2
  have hur0 : 0 < ur := hu0.trans_le hu.2
  have harg : ordinaryResidual tr ur / ordinaryA ≤
      ordinaryResidual t u / ordinaryA :=
    div_le_div_of_nonneg_right (ordinaryResidual_antitone ht.2 hu.2)
      ordinaryA_pos.le
  have hprofile := monotone_actualExtendedThirdLowerFactor harg
  have hden : ordinaryA * t * u ≤ ordinaryA * tr * ur := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left ht.2 ordinaryA_pos.le)
      hu.2 hu0.le (mul_nonneg ordinaryA_pos.le htr0.le)
  unfold ordinaryPairKernel
  calc
    4 * actualExtendedThirdLowerFactor (ordinaryResidual tr ur / ordinaryA) /
        (ordinaryA * tr * ur) ≤
      4 * actualExtendedThirdLowerFactor (ordinaryResidual tr ur / ordinaryA) /
        (ordinaryA * t * u) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (actualExtendedThirdLowerFactor_nonneg _))
        (by positivity) hden
    _ ≤ 4 * actualExtendedThirdLowerFactor (ordinaryResidual t u / ordinaryA) /
        (ordinaryA * t * u) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprofile (by norm_num)) (by positivity)

/-- Continuity and integrability are proved for the real density, including
the s=2 branch. They are not introduced as numerical certificate premises. -/
theorem ordinaryPairKernel_intervalIntegrable {t ul ur : ℝ}
    (ht : 0 < t) (hul : 0 < ul) (hu : ul ≤ ur) :
    IntervalIntegrable (ordinaryPairKernel t) volume ul ur := by
  have hr : Continuous (fun u : ℝ => ordinaryResidual t u / ordinaryA) := by
    unfold ordinaryResidual
    fun_prop
  have hn : Continuous (fun u : ℝ =>
      4 * actualExtendedThirdLowerFactor (ordinaryResidual t u / ordinaryA)) :=
    continuous_const.mul (continuous_actualExtendedThirdLowerFactor.comp hr)
  apply ContinuousOn.intervalIntegrable
  apply hn.continuousOn.div (by fun_prop)
  intro u hu'
  rw [Set.uIcc_of_le hu] at hu'
  exact (mul_pos (mul_pos ordinaryA_pos ht) (hul.trans_le hu'.1)).ne'

private def positiveExtension (tl ul t u : ℝ) : ℝ :=
  ordinaryPairKernel (max tl t) (max ul u)

private theorem continuous_positiveExtension {tl ul : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) :
    Continuous (fun p : ℝ × ℝ => positiveExtension tl ul p.1 p.2) := by
  have ht : Continuous (fun p : ℝ × ℝ => max tl p.1) :=
    continuous_const.max continuous_fst
  have hu : Continuous (fun p : ℝ × ℝ => max ul p.2) :=
    continuous_const.max continuous_snd
  have hr : Continuous (fun p : ℝ × ℝ =>
      ordinaryResidual (max tl p.1) (max ul p.2) / ordinaryA) := by
    unfold ordinaryResidual
    fun_prop
  have hn : Continuous (fun p : ℝ × ℝ =>
      4 * actualExtendedThirdLowerFactor
        (ordinaryResidual (max tl p.1) (max ul p.2) / ordinaryA)) :=
    continuous_const.mul (continuous_actualExtendedThirdLowerFactor.comp hr)
  exact hn.div ((continuous_const.mul ht).mul hu) (fun p =>
    (mul_pos (mul_pos ordinaryA_pos (htl.trans_le (le_max_left _ _)))
      (hul.trans_le (le_max_left _ _))).ne')

theorem ordinaryPairKernel_outer_intervalIntegrable {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    IntervalIntegrable (fun t => ∫ u in ul..ur, ordinaryPairKernel t u)
      volume tl tr := by
  have hcontinuous : Continuous
      (fun t => ∫ u in Icc ul ur, positiveExtension tl ul t u) :=
    continuous_parametric_integral_of_continuous
      (continuous_positiveExtension htl hul) isCompact_Icc
  have heq : Set.EqOn
      (fun t => ∫ u in ul..ur, ordinaryPairKernel t u)
      (fun t => ∫ u in Icc ul ur, positiveExtension tl ul t u) (Icc tl tr) := by
    intro t ht'
    calc
      (∫ u in ul..ur, ordinaryPairKernel t u) =
          ∫ u in ul..ur, positiveExtension tl ul t u := by
        apply intervalIntegral.integral_congr
        intro u hu'
        rw [Set.uIcc_of_le hu] at hu'
        simp only [positiveExtension, max_eq_right ht'.1, max_eq_right hu'.1]
      _ = ∫ u in Icc ul ur, positiveExtension tl ul t u := by
        rw [intervalIntegral.integral_of_le hu, integral_Icc_eq_integral_Ioc]
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le ht]
  exact hcontinuous.continuousOn.congr heq

/-- Literal Q80 decoder. Chen-unit conversion has a further division by 4. -/
def q80 : ℝ := 2 ^ 80

def savedQ80Value (n : ℕ) : ℝ := (n : ℝ) / q80

theorem q80_pos : 0 < q80 := by
  norm_num [q80]

theorem savedQ80Value_eq_rational (n : ℕ) :
    savedQ80Value n = (((n : ℚ) / (2 ^ 80 : ℚ) : ℚ) : ℝ) := by
  simp [savedQ80Value, q80]

def ordinaryCornerMass (tl tr ul ur : ℝ) : ℝ :=
  (tr - tl) * (ur - ul) * ordinaryPairKernel tr ur

/-- A mathematically specified directed floor of the corner Darboux mass.
This gives a real estimator to which a rational evaluator can be bound. -/
def directedCornerQ80 (tl tr ul ur : ℝ) : ℕ :=
  Nat.floor (q80 * ordinaryCornerMass tl tr ul ur)

theorem ordinaryCornerMass_nonneg {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    0 ≤ ordinaryCornerMass tl tr ul ur := by
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hu))
    (ordinaryPairKernel_nonneg (htl.trans_le ht) (hul.trans_le hu))

theorem directedCornerQ80_le_mass {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    savedQ80Value (directedCornerQ80 tl tr ul ur) ≤
      ordinaryCornerMass tl tr ul ur := by
  unfold savedQ80Value directedCornerQ80
  apply (div_le_iff₀ q80_pos).mpr
  have hf := Nat.floor_le (mul_nonneg q80_pos.le
    (ordinaryCornerMass_nonneg htl hul ht hu))
  simpa only [mul_comm] using hf

/-- The decoded directed output is a lower estimator for the actual
rectangle's density times area, at every point of that rectangle. -/
theorem directedCornerQ80_le_rectangle_sample {tl tr ul ur t u : ℝ}
    (htl : 0 < tl) (hul : 0 < ul)
    (ht : t ∈ Icc tl tr) (hu : u ∈ Icc ul ur) :
    savedQ80Value (directedCornerQ80 tl tr ul ur) ≤
      (tr - tl) * (ur - ul) * ordinaryPairKernel t u := by
  apply (directedCornerQ80_le_mass htl hul (ht.1.trans ht.2)
    (hu.1.trans hu.2)).trans
  exact mul_le_mul_of_nonneg_left (ordinaryPairKernel_corner_le htl hul ht hu)
    (mul_nonneg (sub_nonneg.mpr (ht.1.trans ht.2))
      (sub_nonneg.mpr (hu.1.trans hu.2)))

/-- The actual Q80 directed corner output is a lower bound for the genuine
iterated ordinary pair integral. All analytical premises have been proved
above from positivity and monotonicity of the actual pinned lower factor. -/
theorem directedCornerQ80_le_actual_integral {tl tr ul ur : ℝ}
    (htl : 0 < tl) (hul : 0 < ul) (ht : tl ≤ tr) (hu : ul ≤ ur) :
    savedQ80Value (directedCornerQ80 tl tr ul ur) ≤
      ordinaryCellIntegral tl tr ul ur := by
  have hinner : ∀ t ∈ Icc tl tr,
      (ur - ul) * ordinaryPairKernel tr ur ≤
        ∫ u in ul..ur, ordinaryPairKernel t u := by
    intro t ht'
    have hi := intervalIntegral.integral_mono_on hu
      (intervalIntegrable_const : IntervalIntegrable
        (fun _u : ℝ => ordinaryPairKernel tr ur) volume ul ur)
      (ordinaryPairKernel_intervalIntegrable (htl.trans_le ht'.1) hul hu)
      (fun u hu' => ordinaryPairKernel_corner_le htl hul ht' hu')
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
  have houter := intervalIntegral.integral_mono_on ht
    (intervalIntegrable_const : IntervalIntegrable
      (fun _t : ℝ => (ur - ul) * ordinaryPairKernel tr ur) volume tl tr)
    (ordinaryPairKernel_outer_intervalIntegrable htl hul ht hu) hinner
  have hmass : ordinaryCornerMass tl tr ul ur ≤ ordinaryCellIntegral tl tr ul ur := by
    simpa only [ordinaryCornerMass, ordinaryCellIntegral,
      intervalIntegral.integral_const, smul_eq_mul, mul_assoc] using houter
  exact (directedCornerQ80_le_mass htl hul ht hu).trans hmass

/-- A crossing cell can have zero conservative floor even when its actual
integral need not vanish. Only its smallest residual is used here. -/
theorem directedCornerQ80_eq_zero_of_crossing {tl tr ul ur : ℝ}
    (hcross : ordinaryResidual tr ur ≤ 2 * ordinaryA) :
    directedCornerQ80 tl tr ul ur = 0 := by
  simp [directedCornerQ80, ordinaryCornerMass,
    ordinaryPairKernel_eq_zero_of_residual_le_two hcross]

open Certificates.PairedV2

/-- Exact actual first-row binding. Its historic saved Q80 output decodes
to precisely the actual ordinary lower-profile integral on this cell.
Neither a lower-count theorem nor a final loss bound is a premise. -/
theorem first_savedQ80_eq_actual_ordinary_integral :
    savedQ80Value firstDiscardedQ80 =
      ordinaryCellIntegral (tLower firstTIndex : ℝ) (tUpper firstTIndex : ℝ)
        (uLower firstUIndex : ℝ) (uUpper firstUIndex : ℝ) := by
  have ht : (tLower firstTIndex : ℝ) ≤ (tUpper firstTIndex : ℝ) := by
    norm_num [tLower, tUpper, firstTIndex, mu, d]
  have hu : (uLower firstUIndex : ℝ) ≤ (uUpper firstUIndex : ℝ) := by
    norm_num [uLower, uUpper, firstUIndex, a, h]
  have hz : ordinaryResidual (tLower firstTIndex : ℝ) (uLower firstUIndex : ℝ) ≤
      2 * ordinaryA := by
    norm_num [ordinaryResidual, ordinaryA, tLower, uLower, firstTIndex,
      firstUIndex, mu, d, a, h]
  rw [ordinaryCellIntegral_eq_zero ht hu hz]
  simp [savedQ80Value, firstDiscardedQ80]

/-- The same first-row equality on Chen units, with exactly one /4. -/
theorem first_savedQ80_chen_units :
    savedQ80Value firstDiscardedQ80 / 4 =
      ordinaryCellIntegral (tLower firstTIndex : ℝ) (tUpper firstTIndex : ℝ)
        (uLower firstUIndex : ℝ) (uUpper firstUIndex : ℝ) / 4 := by
  rw [first_savedQ80_eq_actual_ordinary_integral]

end

end ImbalancedChen.P2SavedFloorSemantics
