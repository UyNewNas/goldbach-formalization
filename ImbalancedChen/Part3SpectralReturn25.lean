import Mathlib

/-!
The scalar prefactor and the ordinary and improved polynomial comparisons
are extracted from archived Goldbach commit 082e55b2b0a82c422b3b9391f41ec21d1f2cbad9,
from Part3ActualPoissonNormalizedFScalar, Part3ZRegularSpectralPolynomial,
and Part3ZExceptionalSpectralPolynomial. The local source choice is limited
to their numerical identities in manuscript §7, equations (24)–(25).
The finite sum assembly keeps the zero-mode term with its own normalization.
-/

namespace ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly
noncomputable section
/-- Exact quadratic prefactor algebra; no spectral inequality is assumed. -/
theorem quadratic_prefactor {A V U Z C : ℝ} (hA : 0<A) (hV : 0<V)
    (hU : 0<U) (hZ : 0<Z) (hC : 0<C) (D : ℝ) :
    (D/C)^2 * (V*C^4*Z/(A*V*U+C^2*Z)) =
      D^2*V*Z/(Z+A*V*U/C^2) := by
  have hd : A*V*U+C^2*Z ≠ 0 := (show 0 < A*V*U+C^2*Z by positivity).ne'
  have he : Z+A*V*U/C^2 ≠ 0 := (show 0 < Z+A*V*U/C^2 by positivity).ne'
  field_simp [hC.ne',hd,he]; ring

end
end ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly

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

namespace ImbalancedChen.P3ZExceptionalSpectralPolynomial

noncomputable section

def exceptionalReturn (A U C D V Z theta : ℝ) : ℝ :=
  (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
    (C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta) * (V + Z) ^ (1 - 2 * theta)

def exceptionalPolynomial (U C D Z theta : ℝ) : ℝ :=
  C * (C * D * Real.sqrt Z) ^ (2 * theta) *
    (U + Z) ^ (1 - theta) * (C + D * Z) ^ (1 - 2 * theta)

theorem exceptionalPolynomial_nonneg {U C D Z theta : ℝ}
    (hU : 0 < U) (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z) :
    0 ≤ exceptionalPolynomial U C D Z theta := by
  unfold exceptionalPolynomial
  positivity

/-- The actual restored prefactor is at most D^2 V; its denominator
contains the nonnegative additional scale A*V*U/C^2. -/
theorem restored_prefactor_le {A U C D V Z : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) :
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) ≤ D ^ 2 * V := by
  rw [ImbalancedChen.Part3.ActualPoissonNormalizedFSourceOnly.quadratic_prefactor
    hA hV hU hZ hC D]
  apply (div_le_iff₀ (show 0 < Z + A * V * U / C ^ 2 by positivity)).mpr
  have hrest : 0 ≤ D ^ 2 * V * (A * V * U / C ^ 2) := by positivity
  nlinarith only [hrest]

/-- Exact normalization of the exceptional powers. In particular the D
factor is converted to D^(2*theta), not discarded. -/
theorem exceptional_power_normalization {C D Z : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z) (theta : ℝ) :
    (C * D) * (C ^ 2 * Z) ^ theta * ((C + D * Z) / D) ^ (1 - 2 * theta) =
      C * (C * D * Real.sqrt Z) ^ (2 * theta) * (C + D * Z) ^ (1 - 2 * theta) := by
  have hCpow : (C ^ 2) ^ theta = C ^ (2 * theta) := by
    rw [← Real.rpow_two C, ← Real.rpow_mul hC.le]
  have hZpow : (Real.sqrt Z) ^ (2 * theta) = Z ^ theta := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  have hscaled : (C ^ 2 * Z) ^ theta = C ^ (2 * theta) * Z ^ theta := by
    rw [Real.mul_rpow (sq_nonneg C) hZ.le, hCpow]
  have htarget : (C * D * Real.sqrt Z) ^ (2 * theta) =
      C ^ (2 * theta) * D ^ (2 * theta) * Z ^ theta := by
    rw [Real.mul_rpow (mul_nonneg hC.le hD.le) (Real.sqrt_nonneg Z),
      Real.mul_rpow hC.le hD.le, hZpow]
  have hquot := Real.div_rpow (show 0 ≤ C + D * Z by positivity) hD.le (1 - 2 * theta)
  have hDpow : D / D ^ (1 - 2 * theta) = D ^ (2 * theta) := by
    calc
      D / D ^ (1 - 2 * theta) = D ^ (1 - (1 - 2 * theta)) := by
        symm
        simpa only [Real.rpow_one] using (Real.rpow_sub hD (1 : ℝ) (1 - 2 * theta))
      _ = D ^ (2 * theta) := by
        congr 1
        ring
  rw [hscaled, htarget, hquot]
  calc
    (C * D) * (C ^ (2 * theta) * Z ^ theta) *
        ((C + D * Z) ^ (1 - 2 * theta) / D ^ (1 - 2 * theta)) =
        C * C ^ (2 * theta) * Z ^ theta * (C + D * Z) ^ (1 - 2 * theta) *
          (D / D ^ (1 - 2 * theta)) := by ring
    _ = C * (C ^ (2 * theta) * D ^ (2 * theta) * Z ^ theta) *
        (C + D * Z) ^ (1 - 2 * theta) := by rw [hDpow]; ring

/-- The exact cutoff degree is 2-2*theta. This theorem retains the
physical normalization and all powers of D. -/
theorem exceptional_return_le_sharp_inflated_cutoff {A U C D V Z theta R : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) (_htheta : 0 ≤ theta) (htheta_upper : theta ≤ 1 / 2)
    (hR : 1 ≤ R) (hcutoff : V ≤ R * C / D) :
    exceptionalReturn A U C D V Z theta ≤
      R ^ (2 - 2 * theta) * exceptionalPolynomial U C D Z theta := by
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hbeta : 0 ≤ 1 - 2 * theta := by linarith
  have hDV : D * V ≤ R * C := by
    have h := (le_div_iff₀ hD).mp hcutoff
    nlinarith only [h]
  have hpref : (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) ≤
      R * (C * D) := by
    calc
      _ ≤ D ^ 2 * V := restored_prefactor_le hA hU hC hD hV hZ
      _ = (D * V) * D := by ring
      _ ≤ (R * C) * D := mul_le_mul_of_nonneg_right hDV hD.le
      _ = R * (C * D) := by ring
  have hRZ : Z ≤ R * Z := by
    have h := mul_le_mul_of_nonneg_right hR hZ.le
    simpa only [one_mul] using h
  have hlength : V + Z ≤ R * ((C + D * Z) / D) := by
    calc
      V + Z ≤ R * C / D + R * Z := add_le_add hcutoff hRZ
      _ = R * ((C + D * Z) / D) := by field_simp [hD.ne']
  have hlength_pow := Real.rpow_le_rpow (show 0 ≤ V + Z by positivity) hlength hbeta
  have hRpower : R * R ^ (1 - 2 * theta) = R ^ (2 - 2 * theta) := by
    calc
      R * R ^ (1 - 2 * theta) = R ^ (1 : ℝ) * R ^ (1 - 2 * theta) := by
        rw [Real.rpow_one]
      _ = R ^ (1 + (1 - 2 * theta)) := (Real.rpow_add hRpos _ _).symm
      _ = R ^ (2 - 2 * theta) := by
        congr 1
        ring
  unfold exceptionalReturn exceptionalPolynomial
  calc
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
        (C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta) * (V + Z) ^ (1 - 2 * theta) =
        ((D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z))) *
          ((C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta)) * (V + Z) ^ (1 - 2 * theta) := by ring
    _ ≤ (R * (C * D)) * ((C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta)) *
          (R * ((C + D * Z) / D)) ^ (1 - 2 * theta) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hpref (by positivity)) hlength_pow
        (by positivity) (by positivity)
    _ = (R * R ^ (1 - 2 * theta)) *
          ((C * D) * (C ^ 2 * Z) ^ theta * ((C + D * Z) / D) ^ (1 - 2 * theta)) *
          (U + Z) ^ (1 - theta) := by
      rw [Real.mul_rpow hRpos.le (show 0 ≤ (C + D * Z) / D by positivity)]
      ring
    _ = R ^ (2 - 2 * theta) *
          (C * (C * D * Real.sqrt Z) ^ (2 * theta) * (C + D * Z) ^ (1 - 2 * theta)) *
          (U + Z) ^ (1 - theta) := by
      rw [hRpower, exceptional_power_normalization hC hD hZ theta]
    _ = R ^ (2 - 2 * theta) *
          (C * (C * D * Real.sqrt Z) ^ (2 * theta) *
            (U + Z) ^ (1 - theta) * (C + D * Z) ^ (1 - 2 * theta)) := by ring

theorem exceptional_return_le_inflated_cutoff {A U C D V Z theta R : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) (htheta : 0 ≤ theta) (htheta_upper : theta ≤ 1 / 2)
    (hR : 1 ≤ R) (hcutoff : V ≤ R * C / D) :
    exceptionalReturn A U C D V Z theta ≤
      R ^ 2 * exceptionalPolynomial U C D Z theta := by
  have hdegree : R ^ (2 - 2 * theta) ≤ R ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  calc
    _ ≤ R ^ (2 - 2 * theta) * exceptionalPolynomial U C D Z theta :=
      exceptional_return_le_sharp_inflated_cutoff hA hU hC hD hV hZ htheta htheta_upper hR hcutoff
    _ ≤ R ^ 2 * exceptionalPolynomial U C D Z theta := by
      simpa only [Real.rpow_two] using mul_le_mul_of_nonneg_right hdegree
        (exceptionalPolynomial_nonneg hU hC hD hZ)

/-- Literal enhanced exceptional Eq24-to-Eq25 expression at the original cutoff. -/
theorem exceptional_return_le_polynomial {A U C D V Z theta : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) (htheta : 0 ≤ theta) (htheta_upper : theta ≤ 1 / 2)
    (hcutoff : V ≤ C / D) :
    (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)) *
        (C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta) * (V + Z) ^ (1 - 2 * theta) ≤
      C * (C * D * Real.sqrt Z) ^ (2 * theta) *
        (U + Z) ^ (1 - theta) * (C + D * Z) ^ (1 - 2 * theta) := by
  simpa only [exceptionalReturn, exceptionalPolynomial, one_pow, one_mul] using
    (exceptional_return_le_inflated_cutoff hA hU hC hD hV hZ htheta htheta_upper
      (R := 1) (by norm_num) (by simpa only [one_mul] using hcutoff))

theorem exceptional_return_le_seven_thirtyseconds {A U C D V Z : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) (hcutoff : V ≤ C / D) :
    exceptionalReturn A U C D V Z ((7 : ℝ) / 32) ≤
      C * (C * D * Real.sqrt Z) ^ ((7 : ℝ) / 16) *
        (U + Z) ^ ((25 : ℝ) / 32) * (C + D * Z) ^ ((9 : ℝ) / 16) := by
  have h := exceptional_return_le_polynomial hA hU hC hD hV hZ
    (theta := (7 : ℝ) / 32) (by norm_num) (by norm_num) hcutoff
  norm_num [exceptionalReturn] at h ⊢
  exact h

end

end ImbalancedChen.P3ZExceptionalSpectralPolynomial

namespace ImbalancedChen.Part3.SpectralReturn25

noncomputable section

open scoped BigOperators
open ImbalancedChen.P3ZRegularSpectralPolynomial (regular_return_le_inflated_cutoff)
open ImbalancedChen.P3ZExceptionalSpectralPolynomial
  (exceptionalPolynomial exceptionalPolynomial_nonneg exceptional_return_le_sharp_inflated_cutoff)

/-- Ordinary packet coefficient in (24), with `A = |a|` and `T = T0`. -/
def ordinary24 (A U V Z T theta : ℝ) (ν : ℕ) : ℝ :=
  (A * (ν : ℝ)) ^ theta * (U / (ν : ℝ) + Z + T) * (V + Z + T)

/-- The regular packet coefficient in the returned expression (25). -/
def ordinary25 (A U C D Z theta : ℝ) (ν : ℕ) : ℝ :=
  (A * (ν : ℝ)) ^ theta * (C * (U / (ν : ℝ) + Z) * (C + D * Z) + A * U * Z)

/-- The literal right side of (24), before the `x^epsilon` allowance. -/
def eq24Cost (A U C V Z theta : ℝ) (S : Finset ℕ) (B : ℕ → ℝ) (Ball : ℝ) : ℝ :=
  let T := A * V * U / C ^ 2
  let P := V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)
  P * ((∑ ν ∈ S, ordinary24 A U V Z T theta ν * (B ν) ^ 2) +
    (C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta) * (V + Z) ^ (1 - 2 * theta) * Ball ^ 2)

/-- Both nonzero-frequency terms of (25) together with its single zero mode.
The improvement and zero mode retain the total squared coefficient mass. -/
def eq25Cost (A U C D Z theta : ℝ) (S : Finset ℕ) (B : ℕ → ℝ) (Ball : ℝ) : ℝ :=
  (∑ ν ∈ S, ordinary25 A U C D Z theta ν * (B ν) ^ 2) +
    (exceptionalPolynomial U C D Z theta + D ^ 2 * U * Z) * Ball ^ 2

/-- Restoring `(D/C)^2` costs `R^2` in the ordinary part and only
`R^(2-2 theta)` in the improved part. The zero mode is added once, at
its original scale. This comparison presupposes a separate analytic proof
when used to bound the actual spectral return. -/
theorem eq24_to_eq25_components {A U C D V Z theta R : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D) (hV : 0 < V) (hZ : 0 < Z)
    (hθ : 0 ≤ theta) (hθhalf : theta ≤ 1 / 2) (hR : 1 ≤ R) (hv : V ≤ R * C / D)
    (S : Finset ℕ) (hS : ∀ ν ∈ S, 0 < ν) (B : ℕ → ℝ) (Ball : ℝ) :
    (D / C) ^ 2 * eq24Cost A U C V Z theta S B Ball + D ^ 2 * U * Z * Ball ^ 2 ≤
      R ^ 2 * (∑ ν ∈ S, ordinary25 A U C D Z theta ν * (B ν) ^ 2) +
        R ^ (2 - 2 * theta) * exceptionalPolynomial U C D Z theta * Ball ^ 2 +
          D ^ 2 * U * Z * Ball ^ 2 := by
  let T := A * V * U / C ^ 2
  let P := V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z)
  let K := (D / C) ^ 2 * P
  have hreg : K * (∑ ν ∈ S, ordinary24 A U V Z T theta ν * (B ν) ^ 2) ≤
      R ^ 2 * (∑ ν ∈ S, ordinary25 A U C D Z theta ν * (B ν) ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ν hν
    have hνpos : 0 < (ν : ℝ) := by exact_mod_cast hS ν hν
    have hL : 0 ≤ U / (ν : ℝ) := (div_pos hU hνpos).le
    have base := regular_return_le_inflated_cutoff hA hU hC hD hL hV hZ hR hv
    calc
      _ = ((A * (ν : ℝ)) ^ theta * (B ν) ^ 2) *
          (K * (U / (ν : ℝ) + Z + T) * (V + Z + T)) := by
        unfold ordinary24
        ring
      _ ≤ ((A * (ν : ℝ)) ^ theta * (B ν) ^ 2) *
          (R ^ 2 * (C * (U / (ν : ℝ) + Z) * (C + D * Z) + A * U * Z)) :=
        mul_le_mul_of_nonneg_left base (by positivity)
      _ = _ := by unfold ordinary25; ring
  have himproved :
      K * ((C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta) * (V + Z) ^ (1 - 2 * theta) * Ball ^ 2) ≤
        R ^ (2 - 2 * theta) * exceptionalPolynomial U C D Z theta * Ball ^ 2 := by
    have base := exceptional_return_le_sharp_inflated_cutoff hA hU hC hD hV hZ hθ hθhalf hR hv
    calc
      _ = ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalReturn A U C D V Z theta *
            Ball ^ 2 := by
          unfold ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalReturn K P
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right base (sq_nonneg Ball)
  change (D / C) ^ 2 * (P * ((∑ ν ∈ S, ordinary24 A U V Z T theta ν * (B ν) ^ 2) +
    (C ^ 2 * Z) ^ theta * (U + Z) ^ (1 - theta) * (V + Z) ^ (1 - 2 * theta) * Ball ^ 2)) + _ ≤ _
  rw [← mul_assoc]
  change K * (_ + _) + _ ≤ _
  rw [mul_add]
  exact add_le_add (add_le_add hreg himproved) le_rfl

/-- The square cutoff factor advertised after (25) applies also when
`C/D < 1/2`. `V` is the actual positive scale of an occupied block. -/
theorem eq24_to_eq25_inflated_cutoff {A U C D V Z theta R : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D) (hV : 0 < V) (hZ : 0 < Z)
    (hθ : 0 ≤ theta) (hθhalf : theta ≤ 1 / 2) (hR : 1 ≤ R) (hv : V ≤ R * C / D)
    (S : Finset ℕ) (hS : ∀ ν ∈ S, 0 < ν) (B : ℕ → ℝ) (Ball : ℝ) :
    (D / C) ^ 2 * eq24Cost A U C V Z theta S B Ball + D ^ 2 * U * Z * Ball ^ 2 ≤
      R ^ 2 * eq25Cost A U C D Z theta S B Ball := by
  refine (eq24_to_eq25_components hA hU hC hD hV hZ hθ hθhalf hR hv S hS B Ball).trans ?_
  have hdeg : R ^ (2 - 2 * theta) ≤ R ^ (2 : ℕ) := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hRsq : 1 ≤ R ^ (2 : ℕ) := one_le_pow₀ hR
  have hImproved := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdeg (exceptionalPolynomial_nonneg (theta := theta) hU hC hD hZ))
    (sq_nonneg Ball)
  have hzero : D ^ 2 * U * Z * Ball ^ 2 ≤ R ^ 2 * (D ^ 2 * U * Z * Ball ^ 2) :=
    le_mul_of_one_le_left (by positivity) hRsq
  calc
    _ ≤ R ^ 2 * (∑ ν ∈ S, ordinary25 A U C D Z theta ν * (B ν) ^ 2) +
      R ^ 2 * exceptionalPolynomial U C D Z theta * Ball ^ 2 + R ^ 2 * (D ^ 2 * U * Z * Ball ^ 2) :=
        add_le_add (add_le_add le_rfl hImproved) hzero
    _ = _ := by unfold eq25Cost; ring

/-- On the full actual global cutoff the squared price is `x^(2ε)`, at
exactly the manuscript's exponent `theta=7/32`. -/
theorem eq24_to_eq25_seven_thirtyseconds {A U C D V Z x epsilon : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D) (hV : 0 < V) (hZ : 0 < Z)
    (hx : 1 ≤ x) (hε : 0 ≤ epsilon) (hv : V ≤ x ^ epsilon * C / D)
    (S : Finset ℕ) (hS : ∀ ν ∈ S, 0 < ν) (B : ℕ → ℝ) (Ball : ℝ) :
    (D / C) ^ 2 * eq24Cost A U C V Z (7 / 32) S B Ball + D ^ 2 * U * Z * Ball ^ 2 ≤
      x ^ (2 * epsilon) * eq25Cost A U C D Z (7 / 32) S B Ball := by
  have h := eq24_to_eq25_inflated_cutoff (theta := (7 : ℝ) / 32) hA hU hC hD hV hZ
    (by norm_num) (by norm_num) (Real.one_le_rpow hx hε) hv S hS B Ball
  have hp : (x ^ epsilon) ^ (2 : ℕ) = x ^ (2 * epsilon) := by
    rw [← Real.rpow_mul_natCast (zero_le_one.trans hx)]
    congr 1
    ring
  rw [hp] at h
  exact h

open Filter
open scoped Topology

/-- The archived common interval with its actual integer ceil cutoff and
left dyadic endpoint. The interval depends on the original scales but on
no level, row, residue, or Poisson sign. -/
def commonPoissonBlock (b c x eta : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (Nat.ceil ((c / b) * x ^ (eta / 2)) + 1))

/-- The original six pairs have `D≤2b` and `c≤C`.
A single threshold absorbs their factor two and the ceil factor two. -/
theorem occupied_commonPoissonBlock_scale {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ b c C D : ℝ, 0 < b → b ≤ c → 0 < D → D ≤ 2 * b → c ≤ C →
      ∀ j : ℕ, (commonPoissonBlock b c x eta j).Nonempty →
        ((2 ^ j : ℕ) : ℝ) ≤ x ^ eta * C / D := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < eta / 2 by positivity)).eventually_ge_atTop (4 : ℝ)]
    with x hx hxlarge b c C D hb hbc hD hDb hcC j hj
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hratio : 1 ≤ c / b := (le_div_iff₀ hb).mpr (by simpa only [one_mul] using hbc)
  let T := c / b * x ^ (eta / 2)
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hratio (Real.one_le_rpow hx (by positivity))
  have hceil : ((⌈T⌉₊ : ℕ) : ℝ) ≤ 2 * T := by
    have hh := Nat.ceil_lt_add_one (zero_le_one.trans hT)
    linarith
  obtain ⟨p, hp⟩ := hj
  change p ∈ Finset.Ico (2 ^ j) (min (2 ^ (j + 1)) (⌈T⌉₊ + 1)) at hp
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hp
  have hpJ : p ≤ ⌈T⌉₊ := by
    have hh := (lt_min_iff.mp hhi).2
    omega
  have hjceil : ((2 ^ j : ℕ) : ℝ) ≤ ((⌈T⌉₊ : ℕ) : ℝ) := by exact_mod_cast hlo.trans hpJ
  have hV := hjceil.trans hceil
  have hc : 0 < c := hb.trans_le hbc
  have hMD : ((2 ^ j : ℕ) : ℝ) * D ≤ 4 * x ^ (eta / 2) * c := by
    refine (mul_le_mul hV hDb hD.le (by linarith only [hT])).trans_eq ?_
    dsimp only [T]
    field_simp [hb.ne']
    norm_num
  have hpow : x ^ (eta / 2) * x ^ (eta / 2) = x ^ eta := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  refine (le_div_iff₀ hD).mpr (hMD.trans ?_)
  calc
    _ ≤ (x ^ (eta / 2) * x ^ (eta / 2)) * c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxlarge (by positivity)) hc.le
    _ = x ^ eta * c := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcC (by positivity)

/-- The finite (24)→(25) cost deduction on every occupied common block,
with all six original scale pairs covered by the same threshold. -/
theorem eq24_to_eq25_on_occupied_commonPoissonBlock {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ b c A U C D Z : ℝ,
      0 < b → b ≤ c → 0 < A → 0 < U → 0 < D → D ≤ 2 * b → c ≤ C → 0 < Z →
      ∀ j : ℕ, (commonPoissonBlock b c x eta j).Nonempty →
      ∀ S : Finset ℕ, (∀ ν ∈ S, 0 < ν) → ∀ (B : ℕ → ℝ) (Ball : ℝ),
        (D / C) ^ 2 * eq24Cost A U C ((2 ^ j : ℕ) : ℝ) Z (7 / 32) S B Ball +
          D ^ 2 * U * Z * Ball ^ 2 ≤ x ^ (2 * eta) * eq25Cost A U C D Z (7 / 32) S B Ball := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), occupied_commonPoissonBlock_scale heta]
    with x hx hscale b c A U C D Z hb hbc hA hU hD hDb hcC hZ j hj S hS B Ball
  have hC : 0 < C := hb.trans_le (hbc.trans hcC)
  have hV : 0 < ((2 ^ j : ℕ) : ℝ) := by positivity
  exact eq24_to_eq25_seven_thirtyseconds hA hU hC hD hV hZ hx heta.le
    (hscale b c C D hb hbc hD hDb hcC j hj) S hS B Ball

end
end ImbalancedChen.Part3.SpectralReturn25
