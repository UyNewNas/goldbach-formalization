import ImbalancedChen.Part3OriginalHolomorphicOddWindow

/-! The first angular moment of the odd Petersson window.  A nonsingular
primitive gives an exact cancellation at every positive window parameter. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicWindowMoment20261113

open Real Set MeasureTheory
open OriginalHolomorphicOddWindow20261113

private def primitive (u y : ℝ) : ℝ :=
  let b := sinh u
  let d := cosh u - b
  d*y - b*arctan ((d*(sin y*cos y))/(b + d*(sin y)^2))

theorem amplitude_continuous {u : ℝ} (hu : 0<u) : Continuous (amplitude u) := by
  have hb := sinh_pos_iff.mpr hu
  exact (continuous_const.mul (continuous_sin.pow 2)).div
    (continuous_const.add (continuous_sin.pow 2))
    (fun y => (add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg (sin y))).ne')

private theorem primitive_derivative {u : ℝ} (hu : 0<u) (y : ℝ) :
    HasDerivAt (primitive u) (amplitude u y) y := by
  let b := sinh u
  let d := cosh u - b
  let N : ℝ → ℝ := fun x => d*(sin x*cos x)
  let D : ℝ → ℝ := fun x => b + d*(sin x)^2
  have hb : 0<b := sinh_pos_iff.mpr hu
  have hd : 0<d := by
    change 0<cosh u-sinh u
    rw [cosh_sub_sinh]
    exact exp_pos _
  have hden : 0<D y := add_pos_of_pos_of_nonneg hb (mul_nonneg hd.le (sq_nonneg _))
  have hsum : 0<b^2+(sin y)^2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hb) (sq_nonneg _)
  have hyp : 2*b*d+d^2=1 := by
    dsimp [b,d]
    linear_combination cosh_sq_sub_sinh_sq u
  have trig := sin_sq_add_cos_sq y
  have adj : (D y)^2+(N y)^2=b^2+(sin y)^2 := by
    dsimp only [D,N]
    linear_combination d^2*(sin y)^2*trig + (sin y)^2*hyp
  have det : d*((cos y)^2-(sin y)^2)*D y - N y*(2*d*sin y*cos y) =
      b*d-(sin y)^2 := by
    dsimp only [D,N]
    linear_combination (b*d-d^2*(sin y)^2)*trig - (sin y)^2*hyp
  have ratio : 1+(N y/D y)^2=(b^2+(sin y)^2)/(D y)^2 := by
    rw [←adj]
    field_simp [hden.ne'] <;> ring
  have hn : HasDerivAt N (d*((cos y)^2-(sin y)^2)) y := by
    apply (((hasDerivAt_sin y).mul (hasDerivAt_cos y)).const_mul d).congr_deriv
    dsimp <;> ring
  have hD : HasDerivAt D (2*d*sin y*cos y) y := by
    apply ((((hasDerivAt_sin y).pow 2).const_mul d).const_add b).congr_deriv
    ring
  have hangle : HasDerivAt (fun x => arctan (N x / D x))
      ((b*d-(sin y)^2)/(b^2+(sin y)^2)) y := by
    apply (hn.div hD hden.ne').arctan.congr_deriv
    change 1/(1+(N y/D y)^2) *
      ((d*((cos y)^2-(sin y)^2)*D y-N y*(2*d*sin y*cos y))/(D y)^2) = _
    rw [det,ratio]
    field_simp [hden.ne',hsum.ne'] <;> ring
  apply (((hasDerivAt_id y).const_mul d).sub (hangle.const_mul b)).congr_deriv
  change d*1-b*((b*d-(sin y)^2)/(b^2+(sin y)^2)) =
    cosh u*(sin y)^2/(b^2+(sin y)^2)
  field_simp [hsum.ne'] <;> dsimp [d] <;> ring

theorem amplitude_integral {u : ℝ} (hu : 0<u) :
    (∫ y in (0:ℝ)..π/2, amplitude u y) = (π/2)*exp (-u) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => primitive_derivative hu y)
    ((amplitude_continuous hu).intervalIntegrable (0:ℝ) (π/2))]
  simp only [primitive,sin_zero,cos_zero,sin_pi_div_two,cos_pi_div_two,
    mul_zero,zero_mul,zero_div,arctan_zero,sub_zero,cosh_sub_sinh]
  ring

theorem corrected_integral_zero {t : ℝ} (ht : 0<t) :
    (∫ y in (0:ℝ)..π/2, correctedAmplitude t y) = 0 := by
  have ht' := (amplitude_continuous ht).intervalIntegrable (0:ℝ) (π/2)
  have h2 := (amplitude_continuous (by norm_num : (0:ℝ)<2)).intervalIntegrable (0:ℝ) (π/2)
  unfold correctedAmplitude
  rw [intervalIntegral.integral_sub ht' (h2.const_mul _),intervalIntegral.integral_const_mul,
    amplitude_integral ht,amplitude_integral (by norm_num : (0:ℝ)<2)]
  calc
    _ = (π/2)*(exp (-t)-exp ((2-t)+(-2))) := by rw [exp_add]; ring
    _ = 0 := by rw [show (2-t)+(-2) = -t by ring]; ring

theorem corrected_window_remove_constant {t : ℝ} (ht : 0<t) (x : ℝ) :
    (∫ y in (0:ℝ)..π/2, correctedAmplitude t y*cos (x*cos y)) =
      ∫ y in (0:ℝ)..π/2, correctedAmplitude t y*(cos (x*cos y)-1) := by
  have v : Continuous (correctedAmplitude t) := (amplitude_continuous ht).sub
    (continuous_const.mul (amplitude_continuous (by norm_num : (0:ℝ)<2)))
  have q := (v.mul (continuous_cos.comp (continuous_const.mul continuous_cos))).intervalIntegrable
    (0:ℝ) (π/2)
  simp_rw [mul_sub,mul_one]
  rw [intervalIntegral.integral_sub q (v.intervalIntegrable (0:ℝ) (π/2)),
    corrected_integral_zero ht,sub_zero]

end ImbalancedChen.Part3.OriginalHolomorphicWindowMoment20261113
end
