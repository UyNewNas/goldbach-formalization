import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3CenteredFourier

/-!
# Prime-modulus Fourier inversion of the actual complete Kloosterman sum

This source-only proposed module uses the literal `kloosterman` defined by
`OriginalSmoothPoissonTail`, converted by `Physical.kloosterman_eq_zmod`.
The inverse additive transform in its linear frequency returns the original
unit-gated reciprocal phase. The factor `p⁻¹` is the exact finite Fourier
normalization. The proof uses the existing full-modulus orthogonality theorem
from `Part3CenteredFourier`; it makes no cancellation estimate.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical

noncomputable section

open Classical
open scoped BigOperators

/-- At a prime modulus, inverse Fourier transformation in the positive linear
frequency of the actual complete Kloosterman sum recovers the unit-gated
reciprocal phase, with the exact finite normalization. -/
theorem prime_kloosterman_fourier_inverse (p : ℕ) (hp : p.Prime)
    (n : ℤ) (u : ZMod p) :
    (p : ℂ)⁻¹ *
      ∑ m : ZMod p,
        kloosterman p (m.val : ℤ) n * ZMod.stdAddChar (-m * u) =
      if IsUnit u then ZMod.stdAddChar ((n : ZMod p) * u⁻¹) else 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let phase : ZMod p → ℂ := fun v =>
    if IsUnit v then ZMod.stdAddChar ((n : ZMod p) * v⁻¹) else 0
  have hfrequency (m : ZMod p) :
      kloosterman p (m.val : ℤ) n =
        ∑ v : ZMod p, phase v * ZMod.stdAddChar (m * v) := by
    rw [kloosterman_eq_zmod (c := p)]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : IsUnit v
    · simp only [phase, if_pos hv, Int.cast_natCast,
        ZMod.natCast_zmod_val, AddChar.map_add_eq_mul]
      ring
    · simp [phase, hv]
  have horth :
      (∑ m : ZMod p,
        kloosterman p (m.val : ℤ) n * ZMod.stdAddChar (-m * u)) =
        (p : ℂ) * phase u := by
    calc
      _ = ∑ m : ZMod p, ∑ v : ZMod p,
            phase v *
              (ZMod.stdAddChar (-m * u) * ZMod.stdAddChar (m * v)) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [hfrequency m, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro v _
          ring
      _ = ∑ v : ZMod p, phase v *
            (∑ m : ZMod p,
              ZMod.stdAddChar (-m * u) * ZMod.stdAddChar (m * v)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          ring
      _ = ∑ v : ZMod p, phase v *
            ((p : ℂ) * if v = u then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro v _
          rw [ImbalancedChen.Part3.sum_residueAdditiveCoefficient_mul p u v]
      _ = (p : ℂ) * phase u := by
          rw [Finset.sum_eq_single u]
          · simp [mul_comm]
          · intro v _ hv
            simp [hv]
          · simp
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  calc
    _ = (p : ℂ)⁻¹ * ((p : ℂ) * phase u) := by rw [horth]
    _ = phase u := by rw [← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
    _ = _ := rfl

end

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical
