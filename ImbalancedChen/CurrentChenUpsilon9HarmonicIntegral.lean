import ImbalancedChen.CurrentChenUpsilon9HarmonicSlices

/-!
# The actual ninth logarithmic integral

The genuine moving inner integral is evaluated by a logarithmic primitive
on its full closed interval.  Its upper endpoint has two equal positive
logarithm arguments, so their difference is exactly zero.  This gives an
exact one-dimensional dictionary for the original two-dimensional J;
no numerical enclosure or adopted coefficient is supplied as a premise.
-/

namespace ImbalancedChen

noncomputable section

open MeasureTheory Set

private theorem hasDerivAt_currentChenUpsilon9HarmonicPrimitive {x y : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hgap : 0 < 1 - x - y) :
    HasDerivAt (fun u : ℝ =>
        (Real.log u - Real.log (1 - x - u)) / (x * (1 - x)))
      (1 / (x * y * (1 - x - y))) y := by
  have hlog := ((hasDerivAt_id y).const_sub (1 - x)).log hgap.ne'
  have hd := ((Real.hasDerivAt_log hy.ne').sub hlog).div_const (x * (1 - x))
  apply hd.congr_deriv
  field_simp [hx.ne', (sub_pos.mpr hx1).ne', hy.ne', hgap.ne']
  change (1 - x - y - -y) * (1 - x - y) = (1 - x) * (1 - x - y)
  ring

/-- Actual evaluation of the inner slice, including the degenerate
endpoint case d=(1-x)/2.  All logarithm arguments are positive. -/
theorem currentChenUpsilon9Harmonic_inner_integral {x d : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hd : 0 < d) (hdcap : d ≤ (1 - x) / 2) :
    (∫ y in Ico d ((1 - x) / 2), 1 / (x * y * (1 - x - y))) =
      Real.log ((1 - x - d) / d) / (x * (1 - x)) := by
  let F := fun y : ℝ =>
    (Real.log y - Real.log (1 - x - y)) / (x * (1 - x))
  have hgap : ∀ y ∈ Icc d ((1 - x) / 2), 0 < 1 - x - y := by
    intro y hy
    linarith only [hx1, hy.2]
  have hcont : ContinuousOn (fun y : ℝ => 1 / (x * y * (1 - x - y)))
      (Icc d ((1 - x) / 2)) := by
    apply continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).mul (continuousOn_const.sub continuousOn_id))
    intro y hy
    exact (mul_pos (mul_pos hx (hd.trans_le hy.1)) (hgap y hy)).ne'
  have hderiv : ∀ y ∈ uIcc d ((1 - x) / 2),
      HasDerivAt F (1 / (x * y * (1 - x - y))) y := by
    intro y hy
    rw [uIcc_of_le hdcap] at hy
    exact hasDerivAt_currentChenUpsilon9HarmonicPrimitive hx hx1
      (hd.trans_le hy.1) (hgap y hy)
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdcap,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable_of_Icc hdcap)]
  have hgd : 0 < 1 - x - d := hgap d ⟨le_rfl, hdcap⟩
  dsimp only [F]
  rw [show 1 - x - (1 - x) / 2 = (1 - x) / 2 by ring,
    sub_self, zero_div, zero_sub, Real.log_div hgd.ne' hd.ne']
  ring

/-- Exact one-dimensional logarithmic form of the genuine original J.
The half-open outer interval comes from the actual arithmetic selector. -/
theorem currentChenUpsilon9HarmonicIntegral_eq_logIntegral :
    currentChenUpsilon9HarmonicIntegral =
      ∫ x in Ico (19 / 125 : ℝ) (59 / 250 : ℝ),
        Real.log ((1 - x - 59 / 250) / (59 / 250)) / (x * (1 - x)) := by
  rw [currentChenUpsilon9HarmonicIntegral_eq_nested]
  apply setIntegral_congr_fun measurableSet_Ico
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 19 / 125) hx.1
  have hx1 : x < 1 := by linarith only [hx.2]
  exact currentChenUpsilon9Harmonic_inner_integral hx0 hx1 (by norm_num)
    (by linarith only [hx.2])

end

end ImbalancedChen
