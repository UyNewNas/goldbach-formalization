import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson

/-!
Source-only proposed finite arithmetic module.  The unit substitution in the
complete Kloosterman sum moves a multiplier from the linear parameter to the
inverse-residue parameter.  The last theorem applies this equality to the
literal physical frequency, retaining its Fourier-transform argument.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail

open Classical
open scoped BigOperators SchwartzMap FourierTransform

/-- Exact parameter transfer under a unit substitution in the complete sum.
The unit gate and the positive signs of both phase terms are unchanged. -/
theorem kloosterman_unit_scaling {c : ℕ} [NeZero c]
    (m n r : ℤ) (hr : IsUnit (r : ZMod c)) :
    kloosterman c (m * r) n = kloosterman c m (n * r) := by
  rw [Physical.kloosterman_eq_zmod (c := c),
    Physical.kloosterman_eq_zmod (c := c)]
  apply Fintype.sum_bijective (fun u : ZMod c => u * (r : ZMod c))
    ((IsUnit.isUnit_iff_mulRight_bijective (a := (r : ZMod c))).mp hr)
  intro u
  have hgate : IsUnit (u * (r : ZMod c)) ↔ IsUnit u := by
    constructor
    · intro h
      exact isUnit_of_mul_isUnit_left h
    · intro h
      exact h.mul hr
  by_cases hu : IsUnit u
  · have hur : IsUnit (u * (r : ZMod c)) := hgate.mpr hu
    have hinv : (u * (r : ZMod c))⁻¹ = (r : ZMod c)⁻¹ * u⁻¹ :=
      ZMod.inv_eq_of_mul_eq_one c (u * (r : ZMod c))
        ((r : ZMod c)⁻¹ * u⁻¹) (by
          calc
            (u * (r : ZMod c)) * ((r : ZMod c)⁻¹ * u⁻¹) =
                (u * u⁻¹) * ((r : ZMod c) * (r : ZMod c)⁻¹) := by ring
            _ = 1 := by rw [ZMod.mul_inv_of_unit u hu,
              ZMod.mul_inv_of_unit _ hr, one_mul])
    have hcancel :
        (n : ZMod c) * (r : ZMod c) * ((r : ZMod c)⁻¹ * u⁻¹) =
          (n : ZMod c) * u⁻¹ := by
      calc
        _ = (n : ZMod c) * ((r : ZMod c) * (r : ZMod c)⁻¹) * u⁻¹ := by ring
        _ = _ := by rw [ZMod.mul_inv_of_unit _ hr]; ring
    simp only [if_pos hu, if_pos hur]
    congr 1
    simp only [Int.cast_mul, hinv]
    rw [hcancel]
    ring
  · have hur : ¬ IsUnit (u * (r : ZMod c)) := fun h => hu (hgate.mp h)
    simp only [if_neg hu, if_neg hur]

/-- Coprimality is the integer form of the unit licence for scaling. -/
theorem kloosterman_coprime_scaling {c : ℕ} [NeZero c]
    (m n r : ℤ) (hr : Nat.Coprime r.natAbs c) :
    kloosterman c (m * r) n = kloosterman c m (n * r) := by
  exact kloosterman_unit_scaling m n r
    ((Physical.isUnit_intCast_iff_natAbs_coprime (c := c) r).mpr hr)

/-- The original physical frequency may place `inverseResidue c z` in the
inverse-residue parameter instead of the linear parameter.  Its Fourier
argument and scalar factor stay literal. -/
theorem frequency_unit_scaling {c : ℕ} [NeZero c]
    (B : ℝ) (a y z m : ℤ) (hz : IsUnit (z : ZMod c)) :
    frequency B c a y z m =
      (B / (c : ℝ)) •
        (𝓕 CommonSmoothCutoff.dyadicCutoffSchwartz)
          ((B / (c : ℝ)) * (m : ℝ)) *
        kloosterman c m ((a * y) * inverseResidue c z) := by
  have hzinverse : IsUnit ((inverseResidue c z : ℤ) : ZMod c) := by
    simp only [inverseResidue, Int.cast_natCast, ZMod.natCast_zmod_val]
    exact hz.inv
  unfold frequency
  rw [kloosterman_unit_scaling m (a * y) (inverseResidue c z) hzinverse]

end ImbalancedChen.Part3.OriginalSmoothPoissonTail
