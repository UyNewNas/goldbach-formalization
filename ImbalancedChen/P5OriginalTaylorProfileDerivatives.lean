import ImbalancedChen.P5OriginalTaylorLogBounds

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The m1 and m2 formulas and derivative-cancellation minimum from
certify_fifth_prefix_taylor_pilot.py, not a generic assumed Hessian bound.
The actual first-interval f, f' and f'' are the already defined functions.
No Taylor integral lower bound is a hypothesis.
-/
namespace ImbalancedChen.P5OriginalTaylorProfileDerivatives
noncomputable section
open Set
open P5OldFifthPointwiseQ P5OldFifthFirstFConcavity
open P5OriginalTaylorLogBounds

def pilotM1 (a : ℝ) : ℝ :=
  (a / (a - 1) - logLower14 (a - 1)) / a ^ 2

def pilotM2 (a : ℝ) : ℝ :=
  2 / (a ^ 2 * (a - 1)) + 1 / (a * (a - 1) ^ 2)

theorem firstSlope_antitoneOn : AntitoneOn firstSlope (Icc (2 : ℝ) 4) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 2 4)
    (f' := firstCurvature)
  · intro s hs
    exact (hasDerivAt_firstSlope (by linarith [hs.1])).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact (hasDerivAt_firstSlope (by linarith [hs'.1])).hasDerivWithinAt
  · intro s hs
    have hs' : s ∈ Icc (2 : ℝ) 4 := interior_subset hs
    exact firstCurvature_nonpos hs'.1 hs'.2

theorem firstSlope_le_pilotM1_at_left (a : ℝ) (ha : 2 ≤ a) :
    firstSlope a ≤ pilotM1 a := by
  have hl := (original_log14_bounds (a - 1) (by linarith)).1
  exact div_le_div_of_nonneg_right (sub_le_sub_left hl _) (sq_nonneg a)

theorem pilotM1_nonneg (a : ℝ) (ha2 : 2 ≤ a) (ha4 : a ≤ 4) :
    0 ≤ pilotM1 a :=
  (firstSlope_nonneg ha2 ha4).trans (firstSlope_le_pilotM1_at_left a ha2)

theorem firstSlope_abs_le_pilotM1 {a s : ℝ}
    (ha2 : 2 ≤ a) (has : a ≤ s) (hs4 : s ≤ 4) :
    |firstSlope s| ≤ pilotM1 a := by
  have hs2 : 2 ≤ s := ha2.trans has
  rw [abs_of_nonneg (firstSlope_nonneg hs2 hs4)]
  exact (firstSlope_antitoneOn ⟨ha2, has.trans hs4⟩ ⟨hs2, hs4⟩ has).trans
    (firstSlope_le_pilotM1_at_left a ha2)

theorem pilotM2_nonneg (a : ℝ) (ha : 2 ≤ a) : 0 ≤ pilotM2 a := by
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  unfold pilotM2
  positivity

/-- The nonnegative logarithm is discarded from minus f'', exactly as
in the manuscript; the two remaining reciprocal terms decrease with s. -/
theorem firstCurvature_abs_le_pilotM2 {a s : ℝ}
    (ha2 : 2 ≤ a) (has : a ≤ s) (hs4 : s ≤ 4) :
    |firstCurvature s| ≤ pilotM2 a := by
  have hs2 : 2 ≤ s := ha2.trans has
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hs0 : 0 < s := by linarith
  have hs1 : 0 < s - 1 := by linarith
  have hlog : 0 ≤ Real.log (s - 1) := Real.log_nonneg (by linarith)
  have hid : -firstCurvature s =
      2 / (s ^ 2 * (s - 1)) + 1 / (s * (s - 1) ^ 2) -
        2 * Real.log (s - 1) / s ^ 3 := by
    unfold firstCurvature
    field_simp [hs0.ne', hs1.ne']
    <;> ring
  have hsq : a ^ 2 ≤ s ^ 2 := (sq_le_sq₀ ha0.le hs0.le).2 has
  have hsq1 : (a - 1) ^ 2 ≤ (s - 1) ^ 2 :=
    (sq_le_sq₀ ha1.le hs1.le).2 (sub_le_sub_right has 1)
  have hd1 : a ^ 2 * (a - 1) ≤ s ^ 2 * (s - 1) :=
    mul_le_mul hsq (sub_le_sub_right has 1) ha1.le (sq_nonneg s)
  have hd2 : a * (a - 1) ^ 2 ≤ s * (s - 1) ^ 2 :=
    mul_le_mul has hsq1 (sq_nonneg (a - 1)) hs0.le
  have h1 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (mul_pos (sq_pos_of_pos ha0) ha1) hd1
  have h2 := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (mul_pos ha0 (sq_pos_of_pos ha1)) hd2
  rw [abs_of_nonpos (firstCurvature_nonpos hs2 hs4), hid]
  unfold pilotM2
  have hdiscard : 0 ≤ 2 * Real.log (s - 1) / s ^ 3 := by positivity
  linarith

theorem firstF_difference_le_pilotM1 {a sn so delta : ℝ}
    (ha2 : 2 ≤ a) (hao : a ≤ so) (hon : so ≤ sn)
    (hn4 : sn ≤ 4) (hdelta : sn - so ≤ delta) :
    |firstF sn - firstF so| ≤ pilotM1 a * delta := by
  have hder : ∀ s ∈ Icc so sn,
      HasDerivWithinAt firstF (firstSlope s) (Icc so sn) s := by
    intro s hs
    exact (hasDerivAt_firstF (by linarith [hs.1])).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc so sn, ‖firstSlope s‖ ≤ pilotM1 a := by
    intro s hs
    simpa only [Real.norm_eq_abs] using
      firstSlope_abs_le_pilotM1 ha2 (hao.trans hs.1) (hs.2.trans hn4)
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (convex_Icc so sn)
    (show so ∈ Icc so sn from ⟨le_rfl, hon⟩)
    (show sn ∈ Icc so sn from ⟨hon, le_rfl⟩)
  have hlocal : |firstF sn - firstF so| ≤ pilotM1 a * (sn - so) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hon)] using hmean
  exact hlocal.trans (mul_le_mul_of_nonneg_left hdelta
    (pilotM1_nonneg a ha2 (hao.trans (hon.trans hn4))))

theorem firstSlope_difference_le_pilotM2 {a sn so delta : ℝ}
    (ha2 : 2 ≤ a) (hao : a ≤ so) (hon : so ≤ sn)
    (hn4 : sn ≤ 4) (hdelta : sn - so ≤ delta) :
    |firstSlope sn - firstSlope so| ≤ pilotM2 a * delta := by
  have hder : ∀ s ∈ Icc so sn,
      HasDerivWithinAt firstSlope (firstCurvature s) (Icc so sn) s := by
    intro s hs
    exact (hasDerivAt_firstSlope (by linarith [hs.1])).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc so sn, ‖firstCurvature s‖ ≤ pilotM2 a := by
    intro s hs
    simpa only [Real.norm_eq_abs] using
      firstCurvature_abs_le_pilotM2 ha2 (hao.trans hs.1) (hs.2.trans hn4)
  have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (convex_Icc so sn)
    (show so ∈ Icc so sn from ⟨le_rfl, hon⟩)
    (show sn ∈ Icc so sn from ⟨hon, le_rfl⟩)
  have hlocal : |firstSlope sn - firstSlope so| ≤ pilotM2 a * (sn - so) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hon)] using hmean
  exact hlocal.trans (mul_le_mul_of_nonneg_left hdelta (pilotM2_nonneg a ha2))

def pilotFirstBound (a delta Dn Do T : ℝ) : ℝ :=
  min (pilotM1 a * (Dn + Do)) (pilotM1 a * T + pilotM2 a * delta * Do)

/-- The original min of the two first-derivative bounds.  In particular
the cancellation term is retained, rather than replaced by a signed sum. -/
theorem original_derivative_cancellation {a sn so delta dn do_ Dn Do T : ℝ}
    (ha2 : 2 ≤ a) (hao : a ≤ so) (hon : so ≤ sn) (hn4 : sn ≤ 4)
    (hdelta : sn - so ≤ delta) (hdn : |dn| ≤ Dn) (hdo : |do_| ≤ Do)
    (hdiff : |dn - do_| ≤ T) :
    |firstSlope sn * dn - firstSlope so * do_| ≤
      pilotFirstBound a delta Dn Do T := by
  have hMn := firstSlope_abs_le_pilotM1 ha2 (hao.trans hon) hn4
  have hMo := firstSlope_abs_le_pilotM1 ha2 hao (hon.trans hn4)
  have hMd := firstSlope_difference_le_pilotM2 ha2 hao hon hn4 hdelta
  have hM10 := pilotM1_nonneg a ha2 (hao.trans (hon.trans hn4))
  have hM20 := pilotM2_nonneg a ha2
  have hD0 : 0 ≤ Do := (abs_nonneg do_).trans hdo
  have hdelta0 : 0 ≤ delta := (sub_nonneg.mpr hon).trans hdelta
  have hplain : |firstSlope sn * dn - firstSlope so * do_| ≤
      pilotM1 a * (Dn + Do) := by
    calc
      _ ≤ |firstSlope sn * dn| + |firstSlope so * do_| := abs_sub _ _
      _ = |firstSlope sn| * |dn| + |firstSlope so| * |do_| := by rw [abs_mul, abs_mul]
      _ ≤ pilotM1 a * Dn + pilotM1 a * Do := add_le_add
        (mul_le_mul hMn hdn (abs_nonneg dn) hM10)
        (mul_le_mul hMo hdo (abs_nonneg do_) hM10)
      _ = _ := by ring
  have hcancel : |firstSlope sn * dn - firstSlope so * do_| ≤
      pilotM1 a * T + pilotM2 a * delta * Do := by
    have hid : firstSlope sn * dn - firstSlope so * do_ =
        firstSlope sn * (dn - do_) + (firstSlope sn - firstSlope so) * do_ := by ring
    rw [hid]
    calc
      _ ≤ |firstSlope sn * (dn - do_)| + |(firstSlope sn - firstSlope so) * do_| := abs_add _ _
      _ = |firstSlope sn| * |dn - do_| + |firstSlope sn - firstSlope so| * |do_| := by
        rw [abs_mul, abs_mul]
      _ ≤ pilotM1 a * T + (pilotM2 a * delta) * Do := add_le_add
        (mul_le_mul hMn hdiff (abs_nonneg _) hM10)
        (mul_le_mul hMd hdo (abs_nonneg _) (mul_nonneg hM20 hdelta0))
  exact le_min hplain hcancel

end
end ImbalancedChen.P5OriginalTaylorProfileDerivatives
