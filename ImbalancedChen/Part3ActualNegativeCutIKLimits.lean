import ImbalancedChen.Part3ActualNegativeCutPowerLimits
import ImbalancedChen.Part3ActualCutPlaneKIModel
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual upper/lower slit limits of the literal I and nonintegral K models.
The I phases follow from the proved one-sided powers and continuity of
the actual entire Gamma core at the positive quadratic coordinate. The
K jump is then derived algebraically from the actual I-minus-I model and
the nonzero sine denominator, and bound to actual positive-real K values
only on the order ranges for which the real K/I supplier exists.

These are the m=+/-1 values of primary DLMF 10.34.E1 and E2, derived here
without assuming a Bessel monodromy formula. Zero order is a separate leaf.
-/

namespace ImbalancedChen.Part3.ActualNegativeCutIKLimits20261026b

noncomputable section
open Set Filter
open scoped Topology
open GeneralComplexISeriesSourceOnly ComplexOrderKBridgeSourceOnly
open ActualComplexArgumentISlit20261026b ActualCutPlaneKIModel20261026b
open ActualNegativeCutPowerLimits20261026b

theorem half_square_tendsto (x : ℝ) :
    Tendsto (fun z : ℂ => (z / 2) ^ (2 : ℕ)) (𝓝 (-(x : ℂ)))
      (𝓝 (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) := by
  have hc : Continuous (fun z : ℂ => (z / 2) ^ (2 : ℕ)) := by fun_prop
  have h := hc.tendsto (-(x : ℂ))
  have hv : ((-(x : ℂ)) / 2) ^ (2 : ℕ) = (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ)) := by
    push_cast
    ring
  rw [hv] at h
  exact h

/-- The upper I limit is a power limit times a genuine core-series limit. -/
theorem complexArgumentI_tendsto_upper {nu : ℂ} (hnu : -1 < nu.re) {x : ℝ} (hx : 0 < x) :
    Tendsto (complexArgumentI nu) (upperCutFilter x) (𝓝 (upperPhase nu * generalI nu x)) := by
  have hcoordinate : Tendsto (fun z : ℂ => (z / 2) ^ (2 : ℕ)) (upperCutFilter x)
      (𝓝 (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) :=
    (half_square_tendsto x).mono_left nhdsWithin_le_nhds
  have hcore := ((continuous_generalICore hnu).tendsto (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))).comp hcoordinate
  simpa only [complexArgumentI, generalI, mul_assoc] using (half_cpow_tendsto_upper nu hx).mul hcore

/-- The lower approach has the opposite principal-log phase. -/
theorem complexArgumentI_tendsto_lower {nu : ℂ} (hnu : -1 < nu.re) {x : ℝ} (hx : 0 < x) :
    Tendsto (complexArgumentI nu) (lowerCutFilter x) (𝓝 (lowerPhase nu * generalI nu x)) := by
  have hcoordinate : Tendsto (fun z : ℂ => (z / 2) ^ (2 : ℕ)) (lowerCutFilter x)
      (𝓝 (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))) :=
    (half_square_tendsto x).mono_left nhdsWithin_le_nhds
  have hcore := ((continuous_generalICore hnu).tendsto (((x / 2 : ℝ) : ℂ) ^ (2 : ℕ))).comp hcoordinate
  simpa only [complexArgumentI, generalI, mul_assoc] using (half_cpow_tendsto_lower nu hx).mul hcore

private theorem upper_connection_algebra (nu A B : ℂ)
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) :
    (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
      (lowerPhase nu * A - upperPhase nu * B) =
      lowerPhase nu * ((Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) * (A - B)) -
        (Real.pi : ℂ) * Complex.I * B := by
  simp_rw [upperPhase_eq_cos_sin, lowerPhase_eq_cos_sin]
  field_simp [hs] <;> ring

private theorem lower_connection_algebra (nu A B : ℂ)
    (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0) :
    (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
      (upperPhase nu * A - lowerPhase nu * B) =
      upperPhase nu * ((Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) * (A - B)) +
        (Real.pi : ℂ) * Complex.I * B := by
  simp_rw [upperPhase_eq_cos_sin, lowerPhase_eq_cos_sin]
  field_simp [hs] <;> ring

theorem cutPlaneKNonintegral_tendsto_upper {nu : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1) (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (cutPlaneKNonintegral nu) (upperCutFilter x)
      (𝓝 (lowerPhase nu * cutPlaneKNonintegral nu (x : ℂ) -
        (Real.pi : ℂ) * Complex.I * generalI nu x)) := by
  have hm : -1 < (-nu).re := by rw [Complex.neg_re]; linarith
  have h := ((complexArgumentI_tendsto_upper hm hx).sub
    (complexArgumentI_tendsto_upper hL hx)).const_mul
      ((Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)))
  have hv : (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
      (upperPhase (-nu) * generalI (-nu) x - upperPhase nu * generalI nu x) =
      lowerPhase nu * cutPlaneKNonintegral nu (x : ℂ) -
        (Real.pi : ℂ) * Complex.I * generalI nu x := by
    rw [upperPhase_neg, cutPlaneKNonintegral_real]
    exact upper_connection_algebra nu _ _ hs
  rw [hv] at h
  exact h

theorem cutPlaneKNonintegral_tendsto_lower {nu : ℂ}
    (hL : -1 < nu.re) (hU : nu.re < 1) (hs : Complex.sin ((Real.pi : ℂ) * nu) ≠ 0)
    {x : ℝ} (hx : 0 < x) :
    Tendsto (cutPlaneKNonintegral nu) (lowerCutFilter x)
      (𝓝 (upperPhase nu * cutPlaneKNonintegral nu (x : ℂ) +
        (Real.pi : ℂ) * Complex.I * generalI nu x)) := by
  have hm : -1 < (-nu).re := by rw [Complex.neg_re]; linarith
  have h := ((complexArgumentI_tendsto_lower hm hx).sub
    (complexArgumentI_tendsto_lower hL hx)).const_mul
      ((Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)))
  have hv : (Real.pi : ℂ) / (2 * Complex.sin ((Real.pi : ℂ) * nu)) *
      (lowerPhase (-nu) * generalI (-nu) x - lowerPhase nu * generalI nu x) =
      upperPhase nu * cutPlaneKNonintegral nu (x : ℂ) +
        (Real.pi : ℂ) * Complex.I * generalI nu x := by
    rw [lowerPhase_neg, cutPlaneKNonintegral_real]
    exact lower_connection_algebra nu _ _ hs
  rw [hv] at h
  exact h

/-- The upper jump is bound to the actual K_ν(x) for the exact supplied
positive-strip and nonzero-imaginary order ranges. -/
theorem actual_K_negative_cut_upper {nu : ℂ}
    (horder : (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (cutPlaneKNonintegral nu) (upperCutFilter x)
      (𝓝 (lowerPhase nu * complexOrderK nu x - (Real.pi : ℂ) * Complex.I * generalI nu x)) := by
  rcases horder with ⟨hL, hU⟩ | ⟨hre, him⟩
  · have h := cutPlaneKNonintegral_tendsto_upper (nu := nu) (by linarith : -1 < nu.re) hU
      (sin_pi_order_ne_zero_of_positive_strip hL hU) hx
    rw [cutPlaneKNonintegral_real_positive_strip hL hU hx] at h
    exact h
  · have h := cutPlaneKNonintegral_tendsto_upper (nu := nu) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      (sin_pi_order_ne_zero_of_imaginary him) hx
    rw [cutPlaneKNonintegral_real_imaginary hre him hx] at h
    exact h

theorem actual_K_negative_cut_lower {nu : ℂ}
    (horder : (0 < nu.re ∧ nu.re < 1) ∨ (nu.re = 0 ∧ nu.im ≠ 0))
    {x : ℝ} (hx : 0 < x) :
    Tendsto (cutPlaneKNonintegral nu) (lowerCutFilter x)
      (𝓝 (upperPhase nu * complexOrderK nu x + (Real.pi : ℂ) * Complex.I * generalI nu x)) := by
  rcases horder with ⟨hL, hU⟩ | ⟨hre, him⟩
  · have h := cutPlaneKNonintegral_tendsto_lower (nu := nu) (by linarith : -1 < nu.re) hU
      (sin_pi_order_ne_zero_of_positive_strip hL hU) hx
    rw [cutPlaneKNonintegral_real_positive_strip hL hU hx] at h
    exact h
  · have h := cutPlaneKNonintegral_tendsto_lower (nu := nu) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
      (sin_pi_order_ne_zero_of_imaginary him) hx
    rw [cutPlaneKNonintegral_real_imaginary hre him hx] at h
    exact h

end
end ImbalancedChen.Part3.ActualNegativeCutIKLimits20261026b
