import ImbalancedChen.Part3CompletedReciprocalWeil
import ImbalancedChen.Part3DeterminantGCD

/-!
# The signed reciprocal phase in the E1 Cauchy square

The two original moduli `q*r` and `q*r'` are lifted to `q*r*r'`.
Both original unit conditions therefore become the single unit condition
of the common modulus. This keeps arbitrary overlap of the two outer slots.
-/

namespace ImbalancedChen.Part3

noncomputable section

open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open scoped FourierTransform

private theorem inverse_residue_reduces {d l n : ℕ} [NeZero d] [NeZero l]
    (hd : d ∣ l) (hn : n.Coprime l) :
    ((((n : ZMod l)⁻¹).val : ℕ) : ZMod d) = (n : ZMod d)⁻¹ := by
  let reduce := ZMod.castHom hd (ZMod d)
  have hunit := (ZMod.isUnit_iff_coprime n l).mpr hn
  have hunit' := (ZMod.isUnit_iff_coprime n d).mpr (hn.coprime_dvd_right hd)
  have hred : (n : ZMod d) * reduce ((n : ZMod l)⁻¹) = 1 := by
    simpa only [map_mul, map_natCast, map_one] using
      congrArg reduce (ZMod.mul_inv_of_unit _ hunit)
  have hcast : reduce ((n : ZMod l)⁻¹) = ((((n : ZMod l)⁻¹).val : ℕ) : ZMod d) := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [← hcast]
  calc
    _ = ((n : ZMod d)⁻¹ * n) * reduce ((n : ZMod l)⁻¹) := by
      rw [ZMod.inv_mul_of_unit _ hunit', one_mul]
    _ = (n : ZMod d)⁻¹ * ((n : ZMod d) * reduce ((n : ZMod l)⁻¹)) := mul_assoc _ _ _
    _ = _ := by rw [hred, mul_one]

private theorem reciprocalPhase_eq_shared_inverse {d l n : ℕ} [NeZero d] [NeZero l]
    (hd : d ∣ l) (hn : n.Coprime l) (a : ℤ) :
    reciprocalPhase d a (n : ZMod d) =
      fourier 1 (((a : ℝ) * (((n : ZMod l)⁻¹).val : ℝ) / (d : ℝ)) : UnitAddCircle) := by
  have hunit := (ZMod.isUnit_iff_coprime n d).mpr (hn.coprime_dvd_right hd)
  rw [reciprocalPhase, if_pos hunit, ← inverse_residue_reduces hd hn, ← Int.cast_natCast,
    ← Int.cast_mul, ZMod.stdAddChar_coe, fourier_coe_apply]
  push_cast
  congr 1
  ring

private theorem fourier_one_mul_star (x y : ℝ) :
    fourier 1 (x : UnitAddCircle) * star (fourier 1 (y : UnitAddCircle)) =
      fourier 1 ((x - y : ℝ) : UnitAddCircle) := by
  simp only [Complex.star_def]
  rw [← fourier_neg]
  simp only [fourier_coe_apply]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The two gated E1 phases, one coming from the conjugated Cauchy copy,
combine to the exact reciprocal character consumed by (17). The two
physical modulus weights and the summation indices are left to the caller. -/
theorem e1ReciprocalPhase_mul_conj (q r r' : ℕ) [NeZero q] [NeZero r] [NeZero r']
    (n : ℕ) (a h h' : ℤ) :
    reciprocalPhase (q * r) (a * h) (n : ZMod (q * r)) *
      star (reciprocalPhase (q * r') (a * h') (n : ZMod (q * r'))) =
    reciprocalPhase (q * r * r') (a * e1Determinant h h' r r')
      (n : ZMod (q * r * r')) := by
  have hleft : q * r ∣ q * r * r' := dvd_mul_right _ _
  have hright : q * r' ∣ q * r * r' := ⟨r, by ring⟩
  by_cases hn : n.Coprime (q * r * r')
  · rw [reciprocalPhase_eq_shared_inverse hleft hn,
      reciprocalPhase_eq_shared_inverse hright hn,
      reciprocalPhase_nat_eq_fourier, if_pos hn, fourier_one_mul_star]
    have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
    have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
    have hr' : (r' : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r'
    congr 2
    rw [e1Determinant]
    push_cast
    field_simp
  · have hnot : ¬ (n.Coprime (q * r) ∧ n.Coprime (q * r')) := by
      rintro ⟨h1, h2⟩
      exact hn (h1.mul_right h2.coprime_mul_left_right)
    simp only [reciprocalPhase, ZMod.isUnit_iff_coprime, if_neg hn]
    by_cases h1 : n.Coprime (q * r)
    · simp only [if_neg (fun h2 => hnot ⟨h1, h2⟩), star_zero, mul_zero]
    · simp only [if_neg h1, zero_mul]

end

end ImbalancedChen.Part3
