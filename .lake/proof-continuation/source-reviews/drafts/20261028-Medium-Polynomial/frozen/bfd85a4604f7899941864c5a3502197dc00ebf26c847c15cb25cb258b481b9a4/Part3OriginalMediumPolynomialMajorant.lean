import ImbalancedChen.Part3OriginalMediumPhysicalExceptional
import ImbalancedChen.Part3OriginalMediumWeightedReturn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Original equations (23)--(26), in particular the physical inequalities
-- U≤Z and C≤DZ used at lines 392--400 of the completion module.
-- All theorems below are real inequalities, not spectral input assumptions.

namespace ImbalancedChen.Part3OriginalMediumPolynomialMajorant

open Part3OriginalMediumWeightedReturn

noncomputable section

theorem doubled_exceptional_shape {C D Z θ : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z) :
    C * (C * D * Real.sqrt Z) ^ (2 * θ) *
        (2 * Z) ^ (1 - θ) * (2 * D * Z) ^ (1 - 2 * θ) =
      (2 : ℝ) ^ (2 - 3 * θ) * C * D * Z ^ 2 * (C / Z) ^ (2 * θ) := by
  have hz : (Real.sqrt Z) ^ (2 * θ) = Z ^ θ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  have hd : D ^ (2 * θ) * D ^ (1 - 2 * θ) = D := by
    rw [← Real.rpow_add hD]
    have hexp : 2 * θ + (1 - 2 * θ) = 1 := by ring
    rw [hexp, Real.rpow_one]
  have hzz : Z ^ θ * Z ^ (1 - θ) * Z ^ (1 - 2 * θ) = Z ^ (2 - 2 * θ) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ (1 - θ) * (2 : ℝ) ^ (1 - 2 * θ) =
      (2 : ℝ) ^ (2 - 3 * θ) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hzquot : Z ^ (2 - 2 * θ) = Z ^ (2 : ℕ) / Z ^ (2 * θ) := by
    rw [Real.rpow_sub hZ, Real.rpow_two]
  rw [Real.mul_rpow (mul_nonneg hC.le hD.le) (Real.sqrt_nonneg Z),
    Real.mul_rpow hC.le hD.le, hz,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hZ.le,
    Real.mul_rpow (show 0 ≤ 2 * D by positivity) hZ.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hD.le]
  calc
    C * (C ^ (2 * θ) * D ^ (2 * θ) * Z ^ θ) *
        ((2 : ℝ) ^ (1 - θ) * Z ^ (1 - θ)) *
        (((2 : ℝ) ^ (1 - 2 * θ) * D ^ (1 - 2 * θ)) * Z ^ (1 - 2 * θ)) =
      ((2 : ℝ) ^ (1 - θ) * (2 : ℝ) ^ (1 - 2 * θ)) * C * C ^ (2 * θ) *
        (D ^ (2 * θ) * D ^ (1 - 2 * θ)) *
        (Z ^ θ * Z ^ (1 - θ) * Z ^ (1 - 2 * θ)) := by ring
    _ = (2 : ℝ) ^ (2 - 3 * θ) * C * C ^ (2 * θ) * D *
        (Z ^ (2 : ℕ) / Z ^ (2 * θ)) := by rw [htwo, hd, hzz, hzquot]
    _ = (2 : ℝ) ^ (2 - 3 * θ) * C * D * Z ^ 2 * (C / Z) ^ (2 * θ) := by
      rw [Real.div_rpow hC.le hZ.le]
      ring

-- This is the absent positive-scale reduction of the exceptional term;
-- its 4 is a harmless explicit constant, with no lost moving-a factor.
theorem exceptional_le_physical_shape {U C D Z θ : ℝ}
    (hU : 0 ≤ U) (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z)
    (hUZ : U ≤ Z) (hCDZ : C ≤ D * Z)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1 / 2) :
    exceptional U C D Z θ ≤ 4 * C * D * Z ^ 2 * (C / Z) ^ (2 * θ) := by
  have hu : (U + Z) ^ (1 - θ) ≤ (2 * Z) ^ (1 - θ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hc : (C + D * Z) ^ (1 - 2 * θ) ≤ (2 * D * Z) ^ (1 - 2 * θ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have hm := mul_le_mul hu hc (by positivity) (by positivity)
  have hp := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ C * (C * D * Real.sqrt Z) ^ (2 * θ) by positivity)
  have hconst : (2 : ℝ) ^ (2 - 3 * θ) ≤ 4 := by
    calc
      _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hlast := mul_le_mul_of_nonneg_right hconst
    (show 0 ≤ C * D * Z ^ 2 * (C / Z) ^ (2 * θ) by positivity)
  dsimp [exceptional]
  calc
    _ ≤ C * (C * D * Real.sqrt Z) ^ (2 * θ) *
        (2 * Z) ^ (1 - θ) * (2 * D * Z) ^ (1 - 2 * θ) := by
      nlinarith only [hp]
    _ = (2 : ℝ) ^ (2 - 3 * θ) * C * D * Z ^ 2 * (C / Z) ^ (2 * θ) :=
      doubled_exceptional_shape hC hD hZ
    _ ≤ 4 * C * D * Z ^ 2 * (C / Z) ^ (2 * θ) := by nlinarith only [hlast]

theorem zero_poisson_le_ordinary_scale {U C D Z : ℝ}
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hD : 0 ≤ D) (hZ : 0 ≤ Z)
    (hUZ : U ≤ Z) (hDC : D ≤ C) :
    D ^ 2 * U * Z ≤ C * D * Z ^ 2 := by
  have hdu := mul_le_mul hDC hUZ hU hC
  have hm := mul_le_mul_of_nonneg_right hdu (mul_nonneg hD hZ)
  nlinarith only [hm]

end
end ImbalancedChen.Part3OriginalMediumPolynomialMajorant
