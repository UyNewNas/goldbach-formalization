import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3CenteredFourier

/-!
SOURCE ONLY / UNCOMPILED. This adapter uses the positive linear-frequency
sign in `OriginalSmoothPoissonTail.kloosterman_eq_zmod`. Its phase is zero
outside the unit residues. Orthogonality is in the complete linear frequency;
the reciprocal phase remains as an exact multiplier at the selected residue.
-/

namespace ImbalancedChen.Part3.KloostermanPhaseOrthogonalitySourceOnly

noncomputable section
open Classical
open scoped BigOperators

variable {c : ℕ} [NeZero c]

/-- The literal gated summand in `OriginalSmoothPoissonTail.Physical.kloosterman_eq_zmod`,
with its linear frequency represented by a residue. -/
def unitKloostermanPhase (n : ℤ) (m u : ZMod c) : ℂ :=
  if IsUnit u then
    ZMod.stdAddChar (m * u + (n : ZMod c) * u⁻¹)
  else 0

/-- Integer frequencies recover the exact phase appearing in the project. -/
theorem unitKloostermanPhase_int (m n : ℤ) (u : ZMod c) :
    unitKloostermanPhase (c := c) n (m : ZMod c) u =
      (if IsUnit u then
        ZMod.stdAddChar ((m : ZMod c) * u + (n : ZMod c) * u⁻¹)
      else 0) := rfl

/-- Exact size of the gated phase, including the nonunit classes. -/
theorem norm_unitKloostermanPhase (n : ℤ) (m u : ZMod c) :
    ‖unitKloostermanPhase (c := c) n m u‖ =
      if IsUnit u then (1 : ℝ) else 0 := by
  by_cases hu : IsUnit u
  · simp only [unitKloostermanPhase, if_pos hu, ZMod.stdAddChar_apply,
      Circle.norm_coe]
  · simp only [unitKloostermanPhase, if_neg hu, norm_zero]

/-- The complete positive linear-frequency family detects one unit residue.
The reciprocal term is retained, rather than discarded by an absolute-value
bound. This is the Fourier coefficient of the actual Kloosterman phase. -/
theorem sum_unitKloostermanPhase_mul_neg_char (n : ℤ) (u v : ZMod c) :
    (∑ m : ZMod c,
      unitKloostermanPhase (c := c) n m u *
        ZMod.stdAddChar (-(m * v))) =
      if IsUnit u then
        if u = v then
          (c : ℂ) * ZMod.stdAddChar ((n : ZMod c) * u⁻¹)
        else 0
      else 0 := by
  by_cases hu : IsUnit u
  · simp only [unitKloostermanPhase, if_pos hu]
    have hterm (m : ZMod c) :
        ZMod.stdAddChar (m * u + (n : ZMod c) * u⁻¹) *
            ZMod.stdAddChar (-(m * v)) =
          ZMod.stdAddChar ((n : ZMod c) * u⁻¹) *
            ZMod.stdAddChar (m * (u - v)) := by
      calc
        _ = ZMod.stdAddChar
            ((m * u + (n : ZMod c) * u⁻¹) + -(m * v)) := by
              rw [ZMod.stdAddChar.map_add_eq_mul]
        _ = ZMod.stdAddChar (((n : ZMod c) * u⁻¹) + m * (u - v)) := by
              congr 1
              ring
        _ = _ := by rw [ZMod.stdAddChar.map_add_eq_mul]
    simp_rw [hterm]
    rw [← Finset.mul_sum, ImbalancedChen.Part3.sum_stdAddChar_mul_eq]
    by_cases huv : u = v
    · subst v
      simp [mul_comm]
    · have hsub : u - v ≠ 0 := sub_ne_zero.mpr huv
      simp [huv, hsub]
  · simp [unitKloostermanPhase, hu]

end
end ImbalancedChen.Part3.KloostermanPhaseOrthogonalitySourceOnly
