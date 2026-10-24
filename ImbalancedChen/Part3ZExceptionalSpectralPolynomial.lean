import ImbalancedChen.Part3ActualPoissonNormalizedFScalar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# P3 enhanced exceptional Eq24-to-Eq25 power algebra

Source-written, uncompiled. These are inequalities of actual real expressions.
No exceptional spectral mean is an assumption or a conclusion of this file.
-/

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
      _ = D ^ (2 * theta) := by congr 1 <;> ring
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
    (hV : 0 < V) (hZ : 0 < Z) (htheta : 0 ≤ theta) (htheta_upper : theta ≤ 1 / 2)
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
      _ = R * ((C + D * Z) / D) := by field_simp [hD.ne']; ring
  have hlength_pow := Real.rpow_le_rpow (show 0 ≤ V + Z by positivity) hlength hbeta
  have hRpower : R * R ^ (1 - 2 * theta) = R ^ (2 - 2 * theta) := by
    calc
      R * R ^ (1 - 2 * theta) = R ^ (1 : ℝ) * R ^ (1 - 2 * theta) := by
        rw [Real.rpow_one]
      _ = R ^ (1 + (1 - 2 * theta)) := (Real.rpow_add hRpos _ _).symm
      _ = R ^ (2 - 2 * theta) := by congr 1 <;> ring
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
  simpa only [exceptionalReturn,
    show 2 * ((7 : ℝ) / 32) = (7 : ℝ) / 16 by norm_num,
    show 1 - ((7 : ℝ) / 32) = (25 : ℝ) / 32 by norm_num,
    show 1 - 2 * ((7 : ℝ) / 32) = (9 : ℝ) / 16 by norm_num] using h

end

end ImbalancedChen.P3ZExceptionalSpectralPolynomial
