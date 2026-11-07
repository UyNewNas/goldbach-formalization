import ImbalancedChen.Part3TwoKSchwingerBetaEvaluation
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Literal actual K_(i*tau)(q) K_(i*sigma)(q) Mellin integral for every real
s>0. The squared-coordinate Jacobian gives exactly 2^(s-3), and the
proved Schwinger/Beta evaluation supplies all four Gamma factors.
General complex orders and complex s are not claimed in this module.
No KL orthogonality, completeness or spectral-measure theorem is assumed.
-/

namespace ImbalancedChen.Part3.ActualImaginaryTwoKMellin20261025a
noncomputable section
open Set MeasureTheory Filter Complex
open ComplexOrderKBridgeSourceOnly
open TwoKSchwingerAbsolute20261025a TwoKSchwingerBetaEvaluation20261025a

def actualTwoKMellinDensity (tau sigma s q : ℝ) : ℂ :=
  (q : ℂ) ^ ((s : ℂ) - 1) * complexOrderK ((tau : ℂ) * I) q *
    complexOrderK ((sigma : ℂ) * I) q

def squaredCoordinate (q : ℝ) : ℝ := q ^ 2 / 4

theorem squaredCoordinate_hasDerivAt (q : ℝ) :
    HasDerivAt squaredCoordinate (q / 2) q := by
  convert ((hasDerivAt_id q).pow 2).div_const 4 using 1 <;>
    simp only [squaredCoordinate, id_eq, Nat.cast_ofNat, pow_one] <;> ring

theorem squaredCoordinate_injOn : InjOn squaredCoordinate (Ioi (0 : ℝ)) := by
  intro q hq r hr he
  unfold squaredCoordinate at he
  nlinarith

theorem squaredCoordinate_image : squaredCoordinate '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    change 0 < q ^ 2 / 4
    positivity
  · intro hx
    refine ⟨2 * Real.sqrt x, mul_pos (by norm_num) (Real.sqrt_pos.mpr hx), ?_⟩
    unfold squaredCoordinate
    nlinarith [Real.sq_sqrt hx.le]

theorem actualSchwingerProduct_at_squaredCoordinate (tau sigma s : ℝ)
    {q : ℝ} (hq : 0 < q) :
    actualSchwingerProduct tau sigma s (squaredCoordinate q) =
      4 * ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 2) *
        complexOrderK ((tau : ℂ) * I) q * complexOrderK ((sigma : ℂ) * I) q := by
  have hc : 0 < q / 2 := half_pos hq
  have hcC : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hx : squaredCoordinate q = (q / 2) * (q / 2) := by unfold squaredCoordinate; ring
  have hsqrt : Real.sqrt (squaredCoordinate q) = q / 2 := by
    rw [show squaredCoordinate q = (q / 2) ^ 2 by unfold squaredCoordinate; ring,
      Real.sqrt_sq_eq_abs, abs_of_pos hc]
  have harg : 2 * Real.sqrt (squaredCoordinate q) = q := by rw [hsqrt]; ring
  have hp : ((squaredCoordinate q : ℝ) : ℂ) ^ (mellinParameter tau sigma s - 1) *
      ((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
      ((q / 2 : ℝ) : ℂ) ^ ((sigma : ℂ) * I) =
      ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 2) := by
    rw [hx, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hc.le hc.le,
      ← Complex.cpow_add _ _ hcC, ← Complex.cpow_add _ _ hcC,
      ← Complex.cpow_add _ _ hcC]
    congr 1
    unfold mellinParameter
    ring
  unfold actualSchwingerProduct
  rw [harg, hsqrt]
  calc
    _ = 4 *
        (((squaredCoordinate q : ℝ) : ℂ) ^ (mellinParameter tau sigma s - 1) *
          ((q / 2 : ℝ) : ℂ) ^ ((tau : ℂ) * I) *
          ((q / 2 : ℝ) : ℂ) ^ ((sigma : ℂ) * I)) *
        complexOrderK ((tau : ℂ) * I) q * complexOrderK ((sigma : ℂ) * I) q := by ring
    _ = _ := by rw [hp]

/-- Exact Jacobian normalization. Multiplying by q/2 turns the squared
Mellin coordinate into 2^(3-s) times the literal q-Mellin density. -/
theorem actualSchwingerProduct_jacobian (tau sigma s : ℝ) {q : ℝ} (hq : 0 < q) :
    |q / 2| • actualSchwingerProduct tau sigma s (squaredCoordinate q) =
      (2 : ℂ) ^ (3 - (s : ℂ)) * actualTwoKMellinDensity tau sigma s q := by
  have hc : 0 < q / 2 := half_pos hq
  have hcC : ((q / 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hcP : ((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 2) =
      ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 1) := by
    rw [← Complex.cpow_one ((q / 2 : ℝ) : ℂ), ← Complex.cpow_add _ _ hcC]
    congr 1
    ring
  have hqsplit : (q : ℂ) ^ ((s : ℂ) - 1) =
      (2 : ℂ) ^ ((s : ℂ) - 1) * ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 1) := by
    have he : q = 2 * (q / 2) := by ring
    conv_lhs => rw [he]
    rw [Complex.ofReal_mul]
    simpa only [Complex.ofReal_ofNat] using
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2) hc.le ((s : ℂ) - 1)
  have htwo : (2 : ℂ) ^ (3 - (s : ℂ)) * (2 : ℂ) ^ ((s : ℂ) - 1) = 4 := by
    rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
    have he : (3 : ℂ) - (s : ℂ) + ((s : ℂ) - 1) = 2 := by ring
    rw [he, Complex.cpow_two]
    norm_num
  rw [Complex.real_smul, abs_of_pos hc, actualSchwingerProduct_at_squaredCoordinate tau sigma s hq]
  unfold actualTwoKMellinDensity
  rw [hqsplit]
  calc
    _ = 4 * (((q / 2 : ℝ) : ℂ) * ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 2)) *
        complexOrderK ((tau : ℂ) * I) q * complexOrderK ((sigma : ℂ) * I) q := by ring
    _ = 4 * ((q / 2 : ℝ) : ℂ) ^ ((s : ℂ) - 1) *
        complexOrderK ((tau : ℂ) * I) q * complexOrderK ((sigma : ℂ) * I) q := by rw [hcP]
    _ = _ := by rw [← htwo]; ring

theorem mellinScale_cancel (s : ℝ) :
    (2 : ℂ) ^ ((s : ℂ) - 3) * (2 : ℂ) ^ (3 - (s : ℂ)) = 1 := by
  rw [← Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
  have he : ((s : ℂ) - 3) + (3 - (s : ℂ)) = 0 := by ring
  rw [he, Complex.cpow_zero]

/-- Full absolute convergence of the literal product Mellin integral for
imaginary orders, for every real s>0. -/
theorem actualTwoKMellinDensity_integrable (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    IntegrableOn (actualTwoKMellinDensity tau sigma s) (Ioi 0) := by
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun q _ => (squaredCoordinate_hasDerivAt q).hasDerivWithinAt)
    squaredCoordinate_injOn (actualSchwingerProduct tau sigma s)
  rw [squaredCoordinate_image] at hchange
  have h := (hchange.mp (actualSchwingerProduct_integrable tau sigma hs)).const_mul
    ((2 : ℂ) ^ ((s : ℂ) - 3))
  apply h.congr_fun _ measurableSet_Ioi
  intro q hq
  rw [actualSchwingerProduct_jacobian tau sigma s hq,
    ← mul_assoc, mellinScale_cancel, one_mul]

theorem actualTwoKMellin_integral_eq_squared (tau sigma : ℝ) (s : ℝ) :
    (∫ q in Ioi (0 : ℝ), actualTwoKMellinDensity tau sigma s q) =
      (2 : ℂ) ^ ((s : ℂ) - 3) *
        ∫ x in Ioi (0 : ℝ), actualSchwingerProduct tau sigma s x := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun q _ => (squaredCoordinate_hasDerivAt q).hasDerivWithinAt)
    squaredCoordinate_injOn (actualSchwingerProduct tau sigma s)
  rw [squaredCoordinate_image] at hchange
  have he : (∫ x in Ioi (0 : ℝ), actualSchwingerProduct tau sigma s x) =
      (2 : ℂ) ^ (3 - (s : ℂ)) *
        ∫ q in Ioi (0 : ℝ), actualTwoKMellinDensity tau sigma s q := by
    rw [hchange, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro q hq
    exact actualSchwingerProduct_jacobian tau sigma s hq
  rw [he, ← mul_assoc, mellinScale_cancel, one_mul]

/-- The actual imaginary-order two-K Mellin product formula. Every factor
comes from a proved integral; no orthogonality or product formula is assumed. -/
theorem actual_imaginary_twoK_mellin (tau sigma : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ q in Ioi (0 : ℝ),
      (q : ℂ) ^ ((s : ℂ) - 1) * complexOrderK ((tau : ℂ) * I) q *
        complexOrderK ((sigma : ℂ) * I) q) =
      (2 : ℂ) ^ ((s : ℂ) - 3) / Complex.Gamma (s : ℂ) *
        Complex.Gamma (((s : ℂ) + (tau : ℂ) * I + (sigma : ℂ) * I) / 2) *
        Complex.Gamma (((s : ℂ) + (tau : ℂ) * I - (sigma : ℂ) * I) / 2) *
        Complex.Gamma (((s : ℂ) - (tau : ℂ) * I + (sigma : ℂ) * I) / 2) *
        Complex.Gamma (((s : ℂ) - (tau : ℂ) * I - (sigma : ℂ) * I) / 2) := by
  change (∫ q in Ioi (0 : ℝ), actualTwoKMellinDensity tau sigma s q) = _
  rw [actualTwoKMellin_integral_eq_squared, actualSchwingerProduct_integral_four_gamma tau sigma hs]
  have hA : gammaA tau sigma s = ((s : ℂ) + (tau : ℂ) * I - (sigma : ℂ) * I) / 2 := by
    unfold gammaA mellinParameter
    ring
  have hB : gammaB tau sigma s = ((s : ℂ) - (tau : ℂ) * I + (sigma : ℂ) * I) / 2 := by
    unfold gammaB mellinParameter
    ring
  have hD : gammaD tau sigma s = ((s : ℂ) + (tau : ℂ) * I + (sigma : ℂ) * I) / 2 := by
    unfold gammaD gammaA gammaB mellinParameter
    ring
  rw [hA, hB, hD, mellinParameter]
  ring

end
end ImbalancedChen.Part3.ActualImaginaryTwoKMellin20261025a
