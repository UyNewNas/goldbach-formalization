import ImbalancedChen.Part3ActualLogCoverKModel
import ImbalancedChen.Part3ActualNegativeCutKZeroLimits
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual logarithmic-cover turn identities. The core coordinate exp(2L)
is proved invariant under L->L+/-pi*i. The I phase follows from the
literal exponential prefactor, the nonintegral K jump from its literal
I-minus-I expression, and the zero-order jump independently from its
actual derivative-core formula. The resulting cover values are bound
to the previously proved upper/lower cut limits. No monodromy formula
is an input. These identities do not prove larger-sector E18 decay.
-/

namespace ImbalancedChen.Part3.ActualLogCoverKTurns20261026b

noncomputable section
open Set Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly ComplexOrderKBridgeSourceOnly
open ActualComplexArgumentISlit20261026b ActualComplexArgumentKLaplace20261026b
open ActualCutPlaneKIModel20261026b ActualCutPlaneKZeroModel20261026b
open ActualCutPlaneKOrderZeroRemovable20261026b
open ActualNegativeCutPowerLimits20261026b ActualNegativeCutIKLimits20261026b
open ActualNegativeCutKZeroLimits20261026b ActualLogCoverKModel20261026b

theorem coverCoordinate_add_pi (L : ℂ) :
    Complex.exp (2 * (L + (Real.pi : ℂ) * Complex.I)) = Complex.exp (2 * L) := by
  rw [show 2 * (L + (Real.pi : ℂ) * Complex.I) =
      2 * L + 2 * (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem coverCoordinate_sub_pi (L : ℂ) :
    Complex.exp (2 * (L - (Real.pi : ℂ) * Complex.I)) = Complex.exp (2 * L) := by
  rw [show 2 * (L - (Real.pi : ℂ) * Complex.I) =
      2 * L - 2 * (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]

theorem logCoverI_add_pi (nu L : ℂ) :
    logCoverI nu (L + (Real.pi : ℂ) * Complex.I) = upperPhase nu * logCoverI nu L := by
  have hp : Complex.exp (nu * (L + (Real.pi : ℂ) * Complex.I)) =
      upperPhase nu * Complex.exp (nu * L) := by
    rw [show nu * (L + (Real.pi : ℂ) * Complex.I) =
      (Real.pi : ℂ) * Complex.I * nu + nu * L by ring, Complex.exp_add]
    rfl
  unfold logCoverI
  rw [coverCoordinate_add_pi, hp]
  ring

theorem logCoverI_sub_pi (nu L : ℂ) :
    logCoverI nu (L - (Real.pi : ℂ) * Complex.I) = lowerPhase nu * logCoverI nu L := by
  have hp : Complex.exp (nu * (L - (Real.pi : ℂ) * Complex.I)) =
      lowerPhase nu * Complex.exp (nu * L) := by
    rw [show nu * (L - (Real.pi : ℂ) * Complex.I) =
      -((Real.pi : ℂ) * Complex.I * nu) + nu * L by ring, Complex.exp_add]
    rfl
  unfold logCoverI
  rw [coverCoordinate_sub_pi, hp]
  ring

theorem logCoverKNonintegral_add_pi (nu L : ℂ)
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) :
    logCoverKNonintegral nu (L + (Real.pi : ℂ) * Complex.I) =
      lowerPhase nu * logCoverKNonintegral nu L - (Real.pi : ℂ) * Complex.I * logCoverI nu L := by
  unfold logCoverKNonintegral
  rw [logCoverI_add_pi (-nu) L, logCoverI_add_pi nu L, upperPhase_neg]
  simp_rw [upperPhase_eq_cos_sin, lowerPhase_eq_cos_sin]
  field_simp [hs] <;> ring

theorem logCoverKNonintegral_sub_pi (nu L : ℂ)
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) :
    logCoverKNonintegral nu (L - (Real.pi : ℂ) * Complex.I) =
      upperPhase nu * logCoverKNonintegral nu L + (Real.pi : ℂ) * Complex.I * logCoverI nu L := by
  unfold logCoverKNonintegral
  rw [logCoverI_sub_pi (-nu) L, logCoverI_sub_pi nu L, lowerPhase_neg]
  simp_rw [upperPhase_eq_cos_sin, lowerPhase_eq_cos_sin]
  field_simp [hs] <;> ring

/-- Zero-order turn law from the independent actual derivative-core model. -/
theorem logCoverKZero_add_pi (L : ℂ) :
    logCoverKZero (L + (Real.pi : ℂ) * Complex.I) =
      logCoverKZero L - (Real.pi : ℂ) * Complex.I * logCoverI 0 L := by
  unfold logCoverKZero
  rw [logCoverI_add_pi, coverCoordinate_add_pi]
  simp only [upperPhase, mul_zero, Complex.exp_zero, one_mul]
  ring

theorem logCoverKZero_sub_pi (L : ℂ) :
    logCoverKZero (L - (Real.pi : ℂ) * Complex.I) =
      logCoverKZero L + (Real.pi : ℂ) * Complex.I * logCoverI 0 L := by
  unfold logCoverKZero
  rw [logCoverI_sub_pi, coverCoordinate_sub_pi]
  simp only [lowerPhase, mul_zero, neg_zero, Complex.exp_zero, one_mul]
  ring

theorem logCoverK_add_pi {nu : ℂ} (hnu : nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) (L : ℂ) :
    logCoverK nu (L + (Real.pi : ℂ) * Complex.I) =
      lowerPhase nu * logCoverK nu L - (Real.pi : ℂ) * Complex.I * logCoverI nu L := by
  rcases hnu with rfl | hs
  · simpa only [logCoverK, if_pos rfl, lowerPhase, mul_zero, neg_zero, Complex.exp_zero, one_mul] using
      logCoverKZero_add_pi L
  · have hn : nu ≠ 0 := by intro h; apply hs; simp only [h, mul_zero, Complex.sin_zero]
    simpa only [logCoverK, if_neg hn] using logCoverKNonintegral_add_pi nu L hs

theorem logCoverK_sub_pi {nu : ℂ} (hnu : nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) (L : ℂ) :
    logCoverK nu (L - (Real.pi : ℂ) * Complex.I) =
      upperPhase nu * logCoverK nu L + (Real.pi : ℂ) * Complex.I * logCoverI nu L := by
  rcases hnu with rfl | hs
  · simpa only [logCoverK, if_pos rfl, upperPhase, mul_zero, Complex.exp_zero, one_mul] using
      logCoverKZero_sub_pi L
  · have hn : nu ≠ 0 := by intro h; apply hs; simp only [h, mul_zero, Complex.sin_zero]
    simpa only [logCoverK, if_neg hn] using logCoverKNonintegral_sub_pi nu L hs

/-- A full turn is obtained by two proved half turns, retaining both
actual I phase factors instead of assuming a periodic K branch. -/
theorem logCoverK_add_two_pi {nu : ℂ} (hnu : nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) (L : ℂ) :
    logCoverK nu (L + 2 * (Real.pi : ℂ) * Complex.I) =
      lowerPhase nu ^ 2 * logCoverK nu L -
        (Real.pi : ℂ) * Complex.I * (lowerPhase nu + upperPhase nu) * logCoverI nu L := by
  rw [show L + 2 * (Real.pi : ℂ) * Complex.I =
      (L + (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I by ring,
    logCoverK_add_pi hnu, logCoverK_add_pi hnu, logCoverI_add_pi]
  ring

theorem logCoverK_sub_two_pi {nu : ℂ} (hnu : nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) (L : ℂ) :
    logCoverK nu (L - 2 * (Real.pi : ℂ) * Complex.I) =
      upperPhase nu ^ 2 * logCoverK nu L +
        (Real.pi : ℂ) * Complex.I * (upperPhase nu + lowerPhase nu) * logCoverI nu L := by
  rw [show L - 2 * (Real.pi : ℂ) * Complex.I =
      (L - (Real.pi : ℂ) * Complex.I) - (Real.pi : ℂ) * Complex.I by ring,
    logCoverK_sub_pi hnu, logCoverK_sub_pi hnu, logCoverI_sub_pi]
  ring

theorem supplied_order_sin_or_zero {nu : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) :
    nu = 0 ∨ Complex.sin ((Real.pi : ℂ) * nu) ≠ 0 := by
  rcases horder with hzero | hp | hi
  · exact Or.inl hzero
  · exact Or.inr (sin_pi_order_ne_zero_of_positive_strip hp.1 hp.2)
  · exact Or.inr (sin_pi_order_ne_zero_of_imaginary hi.2)

theorem logCoverI_real_half (nu : ℂ) {x : ℝ} (hx : 0 < x) :
    logCoverI nu (Real.log (x / 2) : ℂ) = generalI nu x := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hh : Complex.log ((x : ℂ) / 2) = (Real.log (x / 2) : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by simp only [Complex.ofReal_div, Complex.ofReal_ofNat],
      ← Complex.ofReal_log (half_pos hx).le]
  rw [← hh, logCoverI_principal_half_log nu hxC, complexArgumentI_real]

theorem logCoverK_real_half {nu : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) {x : ℝ} (hx : 0 < x) :
    logCoverK nu (Real.log (x / 2) : ℂ) = complexOrderK nu x := by
  have hh : Complex.log ((x : ℂ) / 2) = (Real.log (x / 2) : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by simp only [Complex.ofReal_div, Complex.ofReal_ofNat],
      ← Complex.ofReal_log (half_pos hx).le]
  have h := logCoverK_eq_actual_rightHalfPlane (nu := nu) (z := (x : ℂ)) horder (by simpa using hx)
  rw [hh, ActualComplexArgumentKLaplace20261026b.complexArgumentK_real] at h
  exact h

theorem logCoverK_upper_boundary_value {nu : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) {x : ℝ} (hx : 0 < x) :
    logCoverK nu ((Real.log (x / 2) : ℂ) + (Real.pi : ℂ) * Complex.I) =
      lowerPhase nu * complexOrderK nu x - (Real.pi : ℂ) * Complex.I * generalI nu x := by
  rw [logCoverK_add_pi (supplied_order_sin_or_zero horder), logCoverK_real_half horder hx,
    logCoverI_real_half nu hx]

theorem logCoverK_lower_boundary_value {nu : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) {x : ℝ} (hx : 0 < x) :
    logCoverK nu ((Real.log (x / 2) : ℂ) - (Real.pi : ℂ) * Complex.I) =
      upperPhase nu * complexOrderK nu x + (Real.pi : ℂ) * Complex.I * generalI nu x := by
  rw [logCoverK_sub_pi (supplied_order_sin_or_zero horder), logCoverK_real_half horder hx,
    logCoverI_real_half nu hx]

/-- The previously proved actual cut limit lands at the corresponding
cover value, including the independently constructed zero-order value. -/
theorem cutK_tendsto_upper_cover_value {nu : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) {x : ℝ} (hx : 0 < x) :
    Tendsto (cutPlaneKWithZero nu) (upperCutFilter x)
      (𝓝 (logCoverK nu ((Real.log (x / 2) : ℂ) + (Real.pi : ℂ) * Complex.I))) := by
  rw [logCoverK_upper_boundary_value horder hx]
  rcases horder with rfl | hp | hi
  · simpa only [cutPlaneKWithZero, if_pos rfl, lowerPhase, mul_zero, neg_zero,
      Complex.exp_zero, one_mul] using actual_KZero_negative_cut_upper hx
  · have hn : nu ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hp.1
    simpa only [cutPlaneKWithZero, if_neg hn] using actual_K_negative_cut_upper (nu := nu) (Or.inl hp) hx
  · have hn : nu ≠ 0 := by intro h; exact hi.2 (by simp only [h, Complex.zero_im])
    simpa only [cutPlaneKWithZero, if_neg hn] using actual_K_negative_cut_upper (nu := nu) (Or.inr hi) hx

theorem cutK_tendsto_lower_cover_value {nu : ℂ}
    (horder : nu = 0 ∨ (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0)) {x : ℝ} (hx : 0 < x) :
    Tendsto (cutPlaneKWithZero nu) (lowerCutFilter x)
      (𝓝 (logCoverK nu ((Real.log (x / 2) : ℂ) - (Real.pi : ℂ) * Complex.I))) := by
  rw [logCoverK_lower_boundary_value horder hx]
  rcases horder with rfl | hp | hi
  · simpa only [cutPlaneKWithZero, if_pos rfl, upperPhase, mul_zero,
      Complex.exp_zero, one_mul] using actual_KZero_negative_cut_lower hx
  · have hn : nu ≠ 0 := by intro h; simpa only [h, Complex.zero_re, lt_self_iff_false] using hp.1
    simpa only [cutPlaneKWithZero, if_neg hn] using actual_K_negative_cut_lower (nu := nu) (Or.inl hp) hx
  · have hn : nu ≠ 0 := by intro h; exact hi.2 (by simp only [h, Complex.zero_im])
    simpa only [cutPlaneKWithZero, if_neg hn] using actual_K_negative_cut_lower (nu := nu) (Or.inr hi) hx

end
end ImbalancedChen.Part3.ActualLogCoverKTurns20261026b
