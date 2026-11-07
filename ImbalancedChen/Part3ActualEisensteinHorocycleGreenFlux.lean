import ImbalancedChen.Part3ActualEisensteinHorocycleJetMean
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Exact constant/nonconstant separation of the actual horocycle Green flux

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.
All four mixed terms vanish by the proved zero means of the actual
continued remainder and its actual height derivative. Thus the full
horocycle flux differs from the exact completed-constant flux by the
already exponentially bounded nonconstant flux. Both constant powers and
the central regularization are retained. No quotient-side Green identity
or spectral completeness is inferred.
-/
namespace ImbalancedChen.Part3.ActualEisensteinHorocycleGreenFlux20261026b
noncomputable section
open Set MeasureTheory
open CompletedEisensteinReflection20261025a
open ActualEisensteinHorocycleRemainder20261026b ActualEisensteinHorocycleJetMean20261026b
open CompletedEisensteinCuspTail20261025a ActualEisensteinHeightDerivativeTail20261026b

private theorem affine_horocycle_pairing (A B : ℂ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hfm : (∫ x in (0 : ℝ)..1, f x) = 0) (hgm : (∫ x in (0 : ℝ)..1, g x) = 0) :
    (∫ x in (0 : ℝ)..1, star (A + f x) * (B + g x)) =
      star A * B + ∫ x in (0 : ℝ)..1, star (f x) * g x := by
  have hstar : (∫ x in (0 : ℝ)..1, star (f x)) = 0 := by
    have hh : (∫ x in (0 : ℝ)..1, star (f x)) = star (∫ x in (0 : ℝ)..1, f x) := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
        Complex.star_def, integral_conj]
    rw [hh, hfm, star_zero]
  have hAA : Continuous (fun _ : ℝ => star A * B) := continuous_const
  have hAg : Continuous (fun x => star A * g x) := hg.const_mul _
  have hfB : Continuous (fun x => star (f x) * B) := hf.star.mul_const _
  have hfg : Continuous (fun x => star (f x) * g x) := hf.star.mul hg
  simp only [star_add, add_mul, mul_add]
  rw [intervalIntegral.integral_add ((hAA.add hAg).intervalIntegrable 0 1)
    ((hfB.add hfg).intervalIntegrable 0 1),
    intervalIntegral.integral_add (hAA.intervalIntegrable 0 1) (hAg.intervalIntegrable 0 1),
    intervalIntegral.integral_add (hfB.intervalIntegrable 0 1) (hfg.intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_mul_const, hgm, hstar, sub_zero, one_smul, mul_zero, zero_mul,
    add_zero, zero_add]

def actualGreenCurrent (s u : ℂ) (y x : ℝ) : ℂ :=
  star (completedEisensteinFourier s y x) * deriv (fun v : ℝ => completedEisensteinFourier u v x) y -
    star (deriv (fun v : ℝ => completedEisensteinFourier s v x) y) * completedEisensteinFourier u y x

def constantGreenCurrent (s u : ℂ) (y : ℝ) : ℂ :=
  star (completedConstant y s) * deriv (fun v : ℝ => completedConstant v u) y -
    star (deriv (fun v : ℝ => completedConstant v s) y) * completedConstant y u

/-- Exact cancellation of ALL mixed constant/nonconstant horocycle terms. -/
theorem actualGreenCurrent_horocycle_split (s u : ℂ)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    {y : ℝ} (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, actualGreenCurrent s u y x) =
      constantGreenCurrent s u y + ∫ x in (0 : ℝ)..1, nonconstantGreenCurrent s u y x := by
  have hRs := actualRemainder_continuous_x s hy
  have hRu := actualRemainder_continuous_x u hy
  have hDs := actualRemainderY_continuous_x s hs0 hs1 hy
  have hDu := actualRemainderY_continuous_x u hu0 hu1 hy
  have he (v : ℂ) (x : ℝ) : completedEisensteinFourier v y x =
      completedConstant y v + actualRemainder v y x := by unfold actualRemainder; ring
  have hd (v : ℂ) (x : ℝ) : deriv (fun z : ℝ => completedEisensteinFourier v z x) y =
      deriv (fun z : ℝ => completedConstant z v) y + actualRemainderY v y x := by
    unfold actualRemainderY
    ring
  unfold actualGreenCurrent
  simp_rw [he, hd]
  rw [intervalIntegral.integral_sub
    (((continuous_const.add hRs).star.mul (continuous_const.add hDu)).intervalIntegrable 0 1)
    (((continuous_const.add hDs).star.mul (continuous_const.add hRu)).intervalIntegrable 0 1),
    affine_horocycle_pairing _ _ _ _ hRs hDu
      (actualRemainder_mean_zero s hy) (actualRemainderY_mean_zero u hu0 hu1 hy),
    affine_horocycle_pairing _ _ _ _ hDs hRu
      (actualRemainderY_mean_zero s hs0 hs1 hy) (actualRemainder_mean_zero u hy)]
  unfold constantGreenCurrent nonconstantGreenCurrent
  rw [intervalIntegral.integral_sub ((hRs.star.mul hDu).intervalIntegrable 0 1)
    ((hDs.star.mul hRu).intervalIntegrable 0 1)]
  ring

/-- The ACTUAL full horocycle boundary flux converges exponentially to
its exact completed-constant flux, uniformly on fixed spectral strips. -/
theorem actualGreenCurrent_constant_error_bound (M : ℕ) {s u : ℂ}
    (hs : |s.re| ≤ (M : ℝ)) (hu : |u.re| ≤ (M : ℝ))
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hu0 : u ≠ 0) (hu1 : u ≠ 1)
    {y : ℝ} (hy : 1 ≤ y) :
    ‖(∫ x in (0 : ℝ)..1, actualGreenCurrent s u y x) - constantGreenCurrent s u y‖ ≤
      2 * (cuspTailConstant M * derivativeTailConstant M) *
        (Real.exp (-(Real.pi / 2) * y)) ^ 2 := by
  rw [actualGreenCurrent_horocycle_split s u hs0 hs1 hu0 hu1
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hy), add_sub_cancel_left]
  exact nonconstantGreenCurrent_horocycle_bound M hs hu hs0 hs1 hu0 hu1 hy

end
end ImbalancedChen.Part3.ActualEisensteinHorocycleGreenFlux20261026b
