import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3CenteredFourier

/-!
Source-only, 2026-10-25. UNCOMPILED / NOT_ROOT_ACCEPTED.

Exact prime-modulus Ramanujan evaluation for the literal physical
Kloosterman sum. This is the exponent-one prime-power case; it evaluates
every integer frequency, including nonzero multiples of the prime.
The proof subtracts the zero residue from the complete primitive
additive-character sum. It assumes no Ramanujan or gcd evaluation formula.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.PrimeRamanujanSourceOnly

open scoped BigOperators

/-- At a prime modulus, adding the omitted zero residue to the actual
Ramanujan sum gives the complete additive-character orthogonality sum. -/
theorem prime_ramanujan_add_one (p : ℕ) (hp : p.Prime) (n : ℤ) :
    kloosterman p n 0 + 1 =
      if (n : ZMod p) = 0 then (p : ℂ) else 0 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Fact p.Prime := ⟨hp⟩
  let f : ZMod p → ℂ := fun u => ZMod.stdAddChar ((n : ZMod p) * u)
  have hterm (u : ZMod p) :
      f u = (if IsUnit u then f u else 0) + (if u = 0 then 1 else 0) := by
    by_cases hu : u = 0
    · simp [hu, f]
    · simp only [isUnit_iff_ne_zero, hu, not_false_eq_true, if_true, if_false, add_zero]
  have hsplit : (∑ u : ZMod p, f u) =
      (∑ u : ZMod p, if IsUnit u then f u else 0) + 1 := by
    calc
      _ = ∑ u : ZMod p,
          ((if IsUnit u then f u else 0) + (if u = 0 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hterm u
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  calc
    _ = (∑ u : ZMod p, if IsUnit u then f u else 0) + 1 := by
      rw [Physical.kloosterman_eq_zmod]
      simp only [Int.cast_zero, zero_mul, add_zero, f]
    _ = ∑ u : ZMod p, f u := hsplit.symm
    _ = _ := by
      simpa only [f, mul_comm] using
        ImbalancedChen.Part3.sum_stdAddChar_mul_eq p (n : ZMod p)

/-- Exact Ramanujan formula for a prime (the exponent-one prime-power
case), stated with ordinary integer divisibility. -/
theorem prime_ramanujan_exact (p : ℕ) (hp : p.Prime) (n : ℤ) :
    kloosterman p n 0 =
      if (p : ℤ) ∣ n then (p : ℂ) - 1 else -1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hsum := prime_ramanujan_add_one p hp n
  have hcast : (n : ZMod p) = 0 ↔ (p : ℤ) ∣ n :=
    ZMod.intCast_zmod_eq_zero_iff_dvd n p
  by_cases hn : (p : ℤ) ∣ n
  · rw [if_pos hn]
    rw [if_pos (hcast.mpr hn)] at hsum
    linear_combination hsum
  · rw [if_neg hn]
    rw [if_neg (mt hcast.mp hn)] at hsum
    linear_combination hsum

end ImbalancedChen.Part3.OriginalSmoothPoissonTail.PrimeRamanujanSourceOnly
