import ImbalancedChen.Part3ActualPoissonNormalizedFScalar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# P3 ordinary Eq24-to-Eq25 polynomial comparison

Source-written, uncompiled candidate. This imports and uses the actual
quadratic prefactor identity; it supplies no spectral estimate.
-/

namespace ImbalancedChen.P3ZRegularSpectralPolynomial

noncomputable section

/-- The only loss in replacing the rational ordinary factor by the
polynomial is the nonnegative product `L*V*T`. -/
theorem ordinary_rational_le_polynomial {L V Z T : ℝ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hZ : 0 < Z) (hT : 0 ≤ T) :
    Z * (L + Z + T) * (V + Z + T) / (Z + T) ≤
      (L + Z) * (V + Z) + Z * T := by
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hZ hT)).mpr
  have hdiscard : 0 ≤ L * V * T := mul_nonneg (mul_nonneg hL hV) hT
  nlinarith only [hdiscard]

/-- An inflated cutoff costs at most its square, for the literal ordinary
polynomial with the full factor `D^2` still present. -/
theorem ordinary_polynomial_le_inflated_cutoff {A U C D L V Z R : ℝ}
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hC : 0 < C) (hD : 0 < D)
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hZ : 0 ≤ Z) (hR : 1 ≤ R)
    (hcutoff : V ≤ R * C / D) :
    D ^ 2 * V * ((L + Z) * (V + Z) + Z * (A * V * U / C ^ 2)) ≤
      R ^ 2 * (C * (L + Z) * (C + D * Z) + A * U * Z) := by
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
  have hDV : D * V ≤ R * C := by
    have h := (le_div_iff₀ hD).mp hcutoff
    nlinarith only [h]
  have hDVnonneg : 0 ≤ D * V := mul_nonneg hD.le hV
  have hRCnonneg : 0 ≤ R * C := mul_nonneg hRnonneg hC.le
  have hsq : D ^ 2 * V ^ 2 ≤ R ^ 2 * C ^ 2 := by
    have h := mul_nonneg (sub_nonneg.mpr hDV) (add_nonneg hRCnonneg hDVnonneg)
    nlinarith only [h]
  have hRle : R ≤ R ^ 2 := by
    have h := mul_nonneg hRnonneg (sub_nonneg.mpr hR)
    nlinarith only [h]
  have hlinear : D ^ 2 * V ≤ R ^ 2 * C * D := by
    calc
      D ^ 2 * V = (D * V) * D := by ring
      _ ≤ (R * C) * D := mul_le_mul_of_nonneg_right hDV hD.le
      _ ≤ (R ^ 2 * C) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRle hC.le) hD.le
  have hnormalized : D ^ 2 * V ^ 2 / C ^ 2 ≤ R ^ 2 := by
    exact (div_le_iff₀ (sq_pos_of_pos hC)).mpr hsq
  have hbase :
      (L + Z) * (D ^ 2 * V ^ 2 + D ^ 2 * V * Z) ≤
        (L + Z) * (R ^ 2 * C ^ 2 + R ^ 2 * C * D * Z) := by
    exact mul_le_mul_of_nonneg_left
      (add_le_add hsq (mul_le_mul_of_nonneg_right hlinear hZ)) (add_nonneg hL hZ)
  have htop :
      (A * U * Z) * (D ^ 2 * V ^ 2 / C ^ 2) ≤ (A * U * Z) * R ^ 2 := by
    exact mul_le_mul_of_nonneg_left hnormalized (mul_nonneg (mul_nonneg hA hU) hZ)
  calc
    D ^ 2 * V * ((L + Z) * (V + Z) + Z * (A * V * U / C ^ 2)) =
        (L + Z) * (D ^ 2 * V ^ 2 + D ^ 2 * V * Z) +
          (A * U * Z) * (D ^ 2 * V ^ 2 / C ^ 2) := by ring
    _ ≤ (L + Z) * (R ^ 2 * C ^ 2 + R ^ 2 * C * D * Z) +
          (A * U * Z) * R ^ 2 := add_le_add hbase htop
    _ = R ^ 2 * (C * (L + Z) * (C + D * Z) + A * U * Z) := by ring

/-- Exact ordinary Eq24-to-Eq25 algebra after the actual physical
quadratic prefactor has been restored. The outside `D^2` is retained. -/
theorem regular_return_le_inflated_cutoff {A U C D L V Z R : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hL : 0 ≤ L) (hV : 0 < V) (hZ : 0 < Z) (hR : 1 ≤ R)
    (hcutoff : V ≤ R * C / D) :
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
        (L + Z + A * V * U / C ^ 2) * (V + Z + A * V * U / C ^ 2) ≤
      R ^ 2 * (C * (L + Z) * (C + D * Z) + A * U * Z) := by
  have hT : 0 ≤ A * V * U / C ^ 2 := by positivity
  have hscalar : 0 ≤ D ^ 2 * V := mul_nonneg (sq_nonneg D) hV.le
  calc
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
        (L + Z + A * V * U / C ^ 2) * (V + Z + A * V * U / C ^ 2) =
        D ^ 2 * V *
          (Z * (L + Z + A * V * U / C ^ 2) * (V + Z + A * V * U / C ^ 2) /
            (Z + A * V * U / C ^ 2)) := by
      rw [ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.quadratic_prefactor
        hA hV hU hZ hC D]
      ring
    _ ≤ D ^ 2 * V *
          ((L + Z) * (V + Z) + Z * (A * V * U / C ^ 2)) :=
      mul_le_mul_of_nonneg_left (ordinary_rational_le_polynomial hL hV.le hZ hT) hscalar
    _ ≤ R ^ 2 * (C * (L + Z) * (C + D * Z) + A * U * Z) :=
      ordinary_polynomial_le_inflated_cutoff hA.le hU.le hC hD hL hV.le hZ.le hR hcutoff

/-- The original cutoff `V <= C/D` has no inflated-cutoff loss. -/
theorem regular_return_le_polynomial {A U C D L V Z : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hL : 0 ≤ L) (hV : 0 < V) (hZ : 0 < Z) (hcutoff : V ≤ C / D) :
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
        (L + Z + A * V * U / C ^ 2) * (V + Z + A * V * U / C ^ 2) ≤
      C * (L + Z) * (C + D * Z) + A * U * Z := by
  simpa only [one_mul, one_pow] using
    (regular_return_le_inflated_cutoff hA hU hC hD hL hV hZ
      (R := 1) (by norm_num) (by simpa only [one_mul] using hcutoff))

/-- If the literal cutoff is `x^delta * C/D`, the ordinary return costs
`x^(2*delta)`. This is a proved degree-two loss, not a spectral theorem. -/
theorem regular_return_le_rpow_cutoff {A U C D L V Z x delta : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hL : 0 ≤ L) (hV : 0 < V) (hZ : 0 < Z)
    (hx : 1 ≤ x) (hdelta : 0 ≤ delta) (hcutoff : V ≤ x ^ delta * C / D) :
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
        (L + Z + A * V * U / C ^ 2) * (V + Z + A * V * U / C ^ 2) ≤
      x ^ (2 * delta) * (C * (L + Z) * (C + D * Z) + A * U * Z) := by
  have hpow : (x ^ delta) ^ (2 : ℕ) = x ^ (2 * delta) := by
    rw [← Real.rpow_mul_natCast (le_trans (by norm_num) hx)]
    congr 1
    ring
  have h := regular_return_le_inflated_cutoff hA hU hC hD hL hV hZ
    (Real.one_le_rpow hx hdelta) hcutoff
  rw [hpow] at h
  exact h

end

end ImbalancedChen.P3ZRegularSpectralPolynomial
