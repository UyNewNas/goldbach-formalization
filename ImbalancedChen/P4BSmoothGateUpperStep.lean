import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic.Linarith

/-!
# P4B: a genuine infinitely smooth scalar upper step

YELLOW / SOURCE ONLY / UNCOMPILED.

The definition uses the pinned `Real.smoothTransition` directly. Its exact
zero/one thresholds and its ContDiff theorem are proved consequences of the
pinned implementation, rather than fields of an assumed admissibility record.
The strict indicator remains zero at x=0; the closed indicator equals one
there. This is scalar regularity and geometry only, with no P3 or SW licence.
-/

namespace ImbalancedChen.P4B

noncomputable section

/-- Genuine C-infinity upper step on the one-sided width interval. -/
def smoothGateUpperStep (width x : ℝ) : ℝ :=
  Real.smoothTransition (1 + x / width)

/-- The pinned transition is bounded globally, even at totalized width zero. -/
theorem smoothGateUpperStep_bounds (width x : ℝ) :
    0 ≤ smoothGateUpperStep width x ∧ smoothGateUpperStep width x ≤ 1 := by
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem smoothGateUpperStep_nonneg (width x : ℝ) :
    0 ≤ smoothGateUpperStep width x := by
  exact (smoothGateUpperStep_bounds width x).1

theorem smoothGateUpperStep_le_one (width x : ℝ) :
    smoothGateUpperStep width x ≤ 1 := by
  exact (smoothGateUpperStep_bounds width x).2

/-- The one plateau begins at the exact closed original gate. -/
theorem smoothGateUpperStep_eq_one_iff {width x : ℝ} (hwidth : 0 < width) :
    smoothGateUpperStep width x = 1 ↔ 0 ≤ x := by
  rw [smoothGateUpperStep, Real.smoothTransition.eq_one_iff_one_le]
  constructor
  · intro h
    have hdiv : (0 : ℝ) ≤ x / width := by linarith only [h]
    have hx := (le_div_iff₀ hwidth).mp hdiv
    simpa only [zero_mul] using hx
  · intro hx
    have hdiv := div_nonneg hx hwidth.le
    linarith only [hdiv]

theorem smoothGateUpperStep_eq_one {width x : ℝ}
    (hwidth : 0 < width) (hx : 0 ≤ x) :
    smoothGateUpperStep width x = 1 := by
  exact (smoothGateUpperStep_eq_one_iff hwidth).mpr hx

/-- The zero plateau includes the exact expanded endpoint -width. -/
theorem smoothGateUpperStep_eq_zero_iff {width x : ℝ} (hwidth : 0 < width) :
    smoothGateUpperStep width x = 0 ↔ x ≤ -width := by
  rw [smoothGateUpperStep, Real.smoothTransition.zero_iff_nonpos]
  constructor
  · intro h
    have hdiv : x / width ≤ -1 := by linarith only [h]
    have hx := (div_le_iff₀ hwidth).mp hdiv
    linarith only [hx]
  · intro hx
    have hdiv : x / width ≤ -1 := (div_le_iff₀ hwidth).mpr (by linarith only [hx])
    linarith only [hdiv]

theorem smoothGateUpperStep_eq_zero {width x : ℝ}
    (hwidth : 0 < width) (hx : x ≤ -width) :
    smoothGateUpperStep width x = 0 := by
  exact (smoothGateUpperStep_eq_zero_iff hwidth).mpr hx

/-- Nonzero support has a strict expanded endpoint. -/
theorem smoothGateUpperStep_nonzero_support {width x : ℝ}
    (hwidth : 0 < width) (hnonzero : smoothGateUpperStep width x ≠ 0) :
    -width < x := by
  by_contra h
  exact hnonzero (smoothGateUpperStep_eq_zero hwidth (le_of_not_gt h))

/-- Actual strict scalar indicator domination; at the wall x=0 the upper
step is one while the strict indicator is zero. -/
theorem smoothGateUpperStep_strict_indicator_le {width : ℝ}
    (hwidth : 0 < width) (x : ℝ) :
    (if 0 < x then (1 : ℝ) else 0) ≤ smoothGateUpperStep width x := by
  by_cases hx : 0 < x
  · simpa only [if_pos hx, smoothGateUpperStep_eq_one hwidth hx.le]
      using (le_refl (1 : ℝ))
  · rw [if_neg hx]
    exact smoothGateUpperStep_nonneg width x

/-- Actual closed scalar indicator domination preserves its inclusive wall. -/
theorem smoothGateUpperStep_closed_indicator_le {width : ℝ}
    (hwidth : 0 < width) (x : ℝ) :
    (if 0 ≤ x then (1 : ℝ) else 0) ≤ smoothGateUpperStep width x := by
  by_cases hx : 0 ≤ x
  · simpa only [if_pos hx, smoothGateUpperStep_eq_one hwidth hx]
      using (le_refl (1 : ℝ))
  · rw [if_neg hx]
    exact smoothGateUpperStep_nonneg width x

/-- C-infinity follows by genuine composition with an affine function.
This holds at every requested order n, including infinity. -/
theorem contDiff_smoothGateUpperStep (width : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (smoothGateUpperStep width) := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.add (contDiff_id.div_const width))

theorem continuous_smoothGateUpperStep (width : ℝ) :
    Continuous (smoothGateUpperStep width) := by
  exact (contDiff_smoothGateUpperStep (n := 0) width).continuous

/-- With positive width the smooth upper step is monotone in its margin. -/
theorem monotone_smoothGateUpperStep {width : ℝ} (hwidth : 0 < width) :
    Monotone (smoothGateUpperStep width) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact add_le_add_right (div_le_div_of_nonneg_right hxy hwidth.le) 1

/-- Enlarging a positive width enlarges the upper envelope pointwise.
The one plateau handles nonnegative margins, so no sign restriction on x
is introduced into this global nesting statement. -/
theorem smoothGateUpperStep_mono_width {width widthMax : ℝ}
    (hwidth : 0 < width) (hwidthMax : width ≤ widthMax) (x : ℝ) :
    smoothGateUpperStep width x ≤ smoothGateUpperStep widthMax x := by
  have hwidthMaxPos : 0 < widthMax := hwidth.trans_le hwidthMax
  by_cases hx : 0 ≤ x
  · simpa only [smoothGateUpperStep_eq_one hwidth hx,
      smoothGateUpperStep_eq_one hwidthMaxPos hx] using (le_refl (1 : ℝ))
  · apply Real.smoothTransition.monotone
    apply add_le_add_right
    apply (div_le_div_iff₀ hwidth hwidthMaxPos).mpr
    exact mul_le_mul_of_nonpos_left hwidthMax (lt_of_not_ge hx).le

/-- Nonzero surplus over the strict indicator lies in (-width,0]. -/
theorem smoothGateUpperStep_strict_surplus_support {width x : ℝ}
    (hwidth : 0 < width)
    (hsurplus : smoothGateUpperStep width x - (if 0 < x then (1 : ℝ) else 0) ≠ 0) :
    -width < x ∧ x ≤ 0 := by
  constructor
  · by_contra h
    have hx : x ≤ -width := le_of_not_gt h
    have hxnonpos : x ≤ 0 := by linarith only [hx, hwidth]
    apply hsurplus
    simp only [smoothGateUpperStep_eq_zero hwidth hx,
      if_neg (not_lt.mpr hxnonpos), sub_self]
  · by_contra h
    have hx : 0 < x := lt_of_not_ge h
    apply hsurplus
    simp only [smoothGateUpperStep_eq_one hwidth hx.le, if_pos hx, sub_self]

/-- Nonzero surplus over a closed gate excludes its original wall too. -/
theorem smoothGateUpperStep_closed_surplus_support {width x : ℝ}
    (hwidth : 0 < width)
    (hsurplus : smoothGateUpperStep width x - (if 0 ≤ x then (1 : ℝ) else 0) ≠ 0) :
    -width < x ∧ x < 0 := by
  constructor
  · by_contra h
    have hx : x ≤ -width := le_of_not_gt h
    have hxneg : x < 0 := by linarith only [hx, hwidth]
    apply hsurplus
    simp only [smoothGateUpperStep_eq_zero hwidth hx, if_neg (not_le.mpr hxneg), sub_self]
  · by_contra h
    have hx : 0 ≤ x := le_of_not_gt h
    apply hsurplus
    simp only [smoothGateUpperStep_eq_one hwidth hx, if_pos hx, sub_self]

end
end ImbalancedChen.P4B