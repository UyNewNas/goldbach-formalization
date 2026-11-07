import ImbalancedChen.U9UniformEulerHarmonicLower

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Only a NONNEGATIVE upper-count inclusion drops the original centre mask.
The original moving-factor interval endpoints stay unchanged. The new
ordinary AP model excludes primes dividing d alone and has remainder≤2,
with no tau(N) or Euler factor of N. No signed-error identity is asserted.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def primitiveAPInterval (A B d a : ℕ) : Finset ℕ :=
  (Finset.Ico A B).filter fun r => Nat.ModEq d r a

def primitiveAPPrimes (A B d a : ℕ) : Finset ℕ :=
  (primitiveAPInterval A B d a).filter Nat.Prime

/-- This is an inclusion for positive counting, not an identification of
the original coefficient or its common signed distribution error. -/
theorem originalPrimeRow_subset_unmasked {N p q d : ℕ} {X : ℝ}
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) (hNd : Nat.Coprime N d) :
    actualPrimeRowAP N X p q d ⊆
      primitiveAPPrimes (rowLower N X p q) (rowUpper N p q)
        d (residue N (p * q) d) := by
  intro r hr
  obtain ⟨hraw, hprime⟩ := Finset.mem_filter.mp hr
  obtain ⟨hrow, hAP, _⟩ := Finset.mem_filter.mp hraw
  rw [preprimeRow_eq_interval_coprime hf hX] at hrow
  have hprod : Nat.ModEq d ((p * q) * r) N := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hAP
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hrow).1, ((product_AP_iff hd hNd).mp hprod).2⟩, hprime⟩

/-- The skeleton and explicit weights depend only on d,z,L before the
selected interval, residue, original factors or near-cap mask are given. -/
def primitiveAPRho (d z L : ℕ) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (finiteSelbergWeight (ordinarySkeleton d z) L)

def primitiveAPSieve (d z A B a : ℕ) : BoundingSieve :=
  { ordinarySkeleton d z with
    support := primitiveAPInterval A B d a
    totalMass := ((primitiveAPInterval A B d a).card : ℝ) }

theorem primitiveAP_weight_eq (d z L A B a : ℕ) :
    finiteSelbergWeight (primitiveAPSieve d z A B a) L =
      finiteSelbergWeight (ordinarySkeleton d z) L := rfl

theorem primitiveAP_normalizer (d z L A B a : ℕ) :
    finiteSelbergNormalizer (primitiveAPSieve d z A B a) L = ordinaryG d z L :=
  ordinary_normalizer d z L

theorem primitiveAP_multSum (d z A B a e : ℕ) :
    (primitiveAPSieve d z A B a).multSum e = divisorAPCount A B d a e := by
  change (∑ r ∈ primitiveAPInterval A B d a, if e ∣ r then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  have hset : (primitiveAPInterval A B d a).filter (fun r => e ∣ r) =
      (Finset.Ico A B).filter (fun r => Nat.ModEq d r a ∧ e ∣ r) := by
    ext r
    simp only [primitiveAPInterval, Finset.mem_filter, and_assoc]
  rw [hset]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, divisorAPCount]

theorem primitiveAP_remainder (d z A B a e : ℕ) :
    (primitiveAPSieve d z A B a).rem e =
      divisorAPCount A B d a e - divisorAPCount A B d a 1 / (e : ℝ) := by
  rw [BoundingSieve.rem, primitiveAP_multSum]
  have hmass : ((primitiveAPInterval A B d a).card : ℝ) = divisorAPCount A B d a 1 := by
    simp only [primitiveAPInterval, divisorAPCount, one_dvd, and_true]
  change _ - (1 / (e : ℝ)) * ((primitiveAPInterval A B d a).card : ℝ) = _
  rw [hmass]
  ring

/-- The actual compatible integer CRT error is bounded without any N
centre-divisor loss. Empty and reversed original intervals are covered. -/
theorem primitiveAP_abs_remainder_le_two (d z A B a e : ℕ) (hd : 0 < d)
    (he : e ∣ sieveProduct d z) : |(primitiveAPSieve d z A B a).rem e| ≤ 2 := by
  have hepos : 0 < e := Nat.pos_of_mem_divisors
    (Nat.mem_divisors.mpr ⟨he, (sieveProduct_squarefree d z).ne_zero⟩)
  have heD := coprime_of_dvd_sieveProduct he
  have h := divisorAPCount_dilution_le_two A B d a 1 e hd zero_lt_one hepos
    (Nat.coprime_one_right d) (by simpa only [Nat.mul_one] using heD)
  simpa only [Nat.one_mul, primitiveAP_remainder] using h

end
end ImbalancedChen.U9SemiprimeSwitch
