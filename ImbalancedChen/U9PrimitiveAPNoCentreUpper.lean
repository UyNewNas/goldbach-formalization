import ImbalancedChen.U9UnmaskedPrimitiveAPModel

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
For nonnegative prime counting only, the primitive AP interval model gives
mass/G_d + 2*L² + z, and G_d≥(phi(d)/d)*log(L+1). Thus the original row upper
has no centre-N Euler factor or divisor-count loss. Every old factor-
dependent interval endpoint is retained. No signed-error transport occurs.
-/

namespace ImbalancedChen.U9SemiprimeSwitch
noncomputable section
open Classical
open scoped BigOperators

def primitiveAPSifted (d z A B a : ℕ) : Finset ℕ :=
  (primitiveAPInterval A B d a).filter fun r => Nat.Coprime r (sieveProduct d z)

theorem primitiveAP_siftedSum (d z A B a : ℕ) :
    (primitiveAPSieve d z A B a).siftedSum = ((primitiveAPSifted d z A B a).card : ℝ) := by
  change (∑ r ∈ primitiveAPInterval A B d a,
    if Nat.Coprime (sieveProduct d z) r then (1 : ℝ) else 0) = _
  simp_rw [Nat.coprime_comm]
  rw [← Finset.sum_filter]
  simp only [primitiveAPSifted, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem primitiveAP_primes_le_sifted_add_z (d z A B a : ℕ) :
    ((primitiveAPPrimes A B d a).card : ℝ) ≤ ((primitiveAPSifted d z A B a).card : ℝ) + z := by
  let S := primitiveAPPrimes A B d a
  let small := S.filter fun r => r < z
  let large := S.filter fun r => ¬r < z
  have hs : small.card ≤ z := by
    calc
      _ ≤ (Finset.range z).card := Finset.card_le_card
        (fun r hr => Finset.mem_range.mpr (Finset.mem_filter.mp hr).2)
      _ = _ := Finset.card_range z
  have hl : large ⊆ primitiveAPSifted d z A B a := by
    intro r hr
    obtain ⟨hrS, hrz⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrI, hrPrime⟩ := Finset.mem_filter.mp hrS
    exact Finset.mem_filter.mpr ⟨hrI,
      prime_coprime_sieveProduct_of_cap_le hrPrime (Nat.le_of_not_gt hrz)⟩
  have hlc := Finset.card_le_card hl
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun r => r < z)
  have hnat : S.card ≤ (primitiveAPSifted d z A B a).card + z := by
    change small.card + large.card = S.card at hsplit
    omega
  exact_mod_cast hnat

theorem primitiveAP_errSum_le_two_level_sq (d z L A B a : ℕ) (hd : 0 < d) (hL : 1 ≤ L) :
    (primitiveAPSieve d z A B a).errSum
      (BoundingSieve.lambdaSquared (finiteSelbergWeight (primitiveAPSieve d z A B a) L)) ≤
      2 * (L : ℝ) ^ 2 := by
  have hcoef := lambdaSquared_l1_le_level_sq (sieveProduct d z) L
    (finiteSelbergWeight (ordinarySkeleton d z) L)
    (fun n => abs_finiteSelbergWeight_le_one (ordinarySkeleton d z) hL n)
    (fun n hn => finiteSelbergWeight_eq_zero_of_level (ordinarySkeleton d z) L n hn)
  unfold BoundingSieve.errSum
  rw [primitiveAP_weight_eq]
  change (∑ e ∈ (sieveProduct d z).divisors, |primitiveAPRho d z L e| *
    |(primitiveAPSieve d z A B a).rem e|) ≤ _
  calc
    _ ≤ ∑ e ∈ (sieveProduct d z).divisors, |primitiveAPRho d z L e| * 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact mul_le_mul_of_nonneg_left
        (primitiveAP_abs_remainder_le_two d z A B a e hd (Nat.dvd_of_mem_divisors he))
        (abs_nonneg _)
    _ = 2 * ∑ e ∈ (sieveProduct d z).divisors, |primitiveAPRho d z L e| := by
      rw [Finset.sum_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcoef (by norm_num)

theorem primitiveAPPrimes_le_finite (d z L : ℕ) (hd : 0 < d) (hL : 1 ≤ L) (A B a : ℕ) :
    ((primitiveAPPrimes A B d a).card : ℝ) ≤
      ((primitiveAPInterval A B d a).card : ℝ) / ordinaryG d z L + 2 * (L : ℝ) ^ 2 + z := by
  have hs := siftedSum_le_finiteSelbergNormalizer_add_errSum (primitiveAPSieve d z A B a) hL
  rw [primitiveAP_siftedSum, primitiveAP_normalizer] at hs
  change ((primitiveAPSifted d z A B a).card : ℝ) ≤
    ((primitiveAPInterval A B d a).card : ℝ) / ordinaryG d z L +
      (primitiveAPSieve d z A B a).errSum
        (BoundingSieve.lambdaSquared (finiteSelbergWeight (primitiveAPSieve d z A B a) L)) at hs
  have he := primitiveAP_errSum_le_two_level_sq d z L A B a hd hL
  have hp := primitiveAP_primes_le_sifted_add_z d z A B a
  linarith

theorem primitiveAP_mass_eq_endpoint (A B d a : ℕ) (hd : 0 < d) :
    ((primitiveAPInterval A B d a).card : ℝ) = (endpointCount A B d a : ℝ) := by
  have h := congrArg (fun x : ℤ => (x : ℝ)) (Nat.Ico_filter_modEq_card A B hd a)
  simpa only [primitiveAPInterval, endpointCount, Int.cast_natCast] using h

theorem primitiveAPPrimes_le_euler_log (d z L : ℕ) (hd : 0 < d)
    (hL : 1 ≤ L) (hLz : L < z) (A B a : ℕ) :
    ((primitiveAPPrimes A B d a).card : ℝ) ≤
      ((d : ℝ) / (Nat.totient d : ℝ)) * ((primitiveAPInterval A B d a).card : ℝ) /
        Real.log (L + 1 : ℕ) + 2 * (L : ℝ) ^ 2 + z := by
  have hphi : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog : 0 < Real.log (L + 1 : ℕ) := Real.log_pos
    (by exact_mod_cast (show 1 < L + 1 by omega))
  have hG := (ordinaryG_lower_harmonic_log d L z hd hLz).2
  have hdiv := div_le_div_of_nonneg_left
    (Nat.cast_nonneg (primitiveAPInterval A B d a).card)
    (mul_pos (div_pos hphi hdR) hlog) hG
  have hmain : ((primitiveAPInterval A B d a).card : ℝ) /
      (((Nat.totient d : ℝ) / (d : ℝ)) * Real.log (L + 1 : ℕ)) =
      ((d : ℝ) / (Nat.totient d : ℝ)) * ((primitiveAPInterval A B d a).card : ℝ) /
        Real.log (L + 1 : ℕ) := by field_simp [hphi.ne', hdR.ne', hlog.ne'] <;> ring
  rw [hmain] at hdiv
  have hp := primitiveAPPrimes_le_finite d z L hd hL A B a
  linarith

/-- The actual original factor-row upper keeps its literal endpoints and
uses only d's Euler factor. The old centre gate is dropped by inclusion. -/
theorem originalPrimeRow_le_noCentre_euler_log
    (N d z L : ℕ) (hd : 0 < d) (hL : 1 ≤ L) (hLz : L < z)
    (X : ℝ) (p q : ℕ) (hf : factorAllowed N p q) (hX : 0 ≤ X) (hNd : Nat.Coprime N d) :
    ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      ((d : ℝ) / (Nat.totient d : ℝ)) *
        (endpointCount (rowLower N X p q) (rowUpper N p q) d (residue N (p * q) d) : ℝ) /
        Real.log (L + 1 : ℕ) + 2 * (L : ℝ) ^ 2 + z := by
  have hsub : ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      ((primitiveAPPrimes (rowLower N X p q) (rowUpper N p q) d
        (residue N (p * q) d)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (originalPrimeRow_subset_unmasked hf hX hd hNd)
  have h := primitiveAPPrimes_le_euler_log d z L hd hL hLz
    (rowLower N X p q) (rowUpper N p q) (residue N (p * q) d)
  rw [primitiveAP_mass_eq_endpoint _ _ d _ hd] at h
  exact hsub.trans h

end
end ImbalancedChen.U9SemiprimeSwitch
