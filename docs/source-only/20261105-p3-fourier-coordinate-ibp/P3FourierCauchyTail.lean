import ImbalancedChen.P3FourierCauchyAxis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE_ONLY / UNCOMPILED.

Quantitative one-dimensional physical-frequency Cauchy tail. The previous
axis file computed the exact left/right integrals but did not bound them
by 2/H. The pinned Mathlib release has Real.le_tan and
Real.arctan_inv_of_pos, but not a ready-to-use Real.arctan_le_self.

The scalar comparison is derived from the genuine pinned tangent
inequality. No distribution or arithmetic error estimate is assumed.
The integral tail is not yet a multidimensional H-box / Fubini result.
-/

namespace ImbalancedChen.P3FourierCauchyTail
noncomputable section

open P3FourierCauchyAxis

/-- Pinned Mathlib Bounds.le_tan applied to the true inverse tangent.
This does not require an arctan bound from a newer Mathlib version. -/
theorem arctan_le_self_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x := by
  have harg : 0 ≤ Real.arctan x := Real.arctan_nonneg.mpr hx
  have htan := Real.le_tan harg (Real.arctan_lt_pi_div_two x)
  simpa only [Real.tan_arctan] using htan

/-- Quantitative physical-frequency two-sided tail for H>0:
  ∫_{xi≤-H} 1/(1+xi²) + ∫_{xi>H} 1/(1+xi²) ≤ 2/H.
The exact tail identity is supplied by the previous source candidate. -/
theorem axisPairTail_le_two_div (H : ℝ) (hH : 0 < H) :
    axisPairTail H ≤ 2 / H := by
  rw [axisPairTail_exact]
  have hinv : 0 ≤ H⁻¹ := (inv_pos.mpr hH).le
  have harctan : Real.arctan H⁻¹ ≤ H⁻¹ :=
    arctan_le_self_nonneg hinv
  calc
    2 * (Real.pi / 2 - Real.arctan H)
        = 2 * Real.arctan H⁻¹ := by
            rw [Real.arctan_inv_of_pos hH]
            ring
    _ ≤ 2 * H⁻¹ := mul_le_mul_of_nonneg_left harctan (by norm_num)
    _ = 2 / H := by ring

/-- A nonnegative genuine derivative budget D may be charged AFTER
the one-axis physical-frequency tail integral, without assuming its
multidimensional product formula. -/
theorem axisPairTail_L1_budget (D H : ℝ)
    (hD : 0 ≤ D) (hH : 0 < H) :
    D * axisPairTail H ≤ (2 * D) / H := by
  calc
    D * axisPairTail H ≤ D * (2 / H) :=
      mul_le_mul_of_nonneg_left (axisPairTail_le_two_div H hH) hD
    _ = (2 * D) / H := by ring

/-- Concrete positive cutoff selection for the one-axis analytic tail.
This is a scalar spending rule only, not the full PP estimate. -/
theorem axisPairTail_spend (D H eps : ℝ)
    (hD : 0 ≤ D) (hH : 0 < H)
    (hcut : 2 * D ≤ eps * H) :
    D * axisPairTail H ≤ eps := by
  exact (axisPairTail_L1_budget D H hD hH).trans
    ((div_le_iff₀ hH).mpr hcut)

end
end ImbalancedChen.P3FourierCauchyTail
