import ImbalancedChen.U9OrdinaryRowExactRemainder

/-!
# A matching finite ordinary-row Selberg upper bound for actual U9 primes

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This sieves the original SECOND factor, not the receiver N-product. The
prime row is exactly the old labelled source with its primitive product
AP condition. The coefficients depend on N,d,z,L BEFORE X,p,q are supplied.
All original row mass and divisor remainders are the explicit CRT/endpoint
expressions. Primes below the strict sieve cap cost at most z per labelled
complementary-factor row. No analytic remainder bound or currentK density
is a premise, and no prime-square or swapped-factor label is discarded.
-/

namespace ImbalancedChen.U9SemiprimeSwitch

noncomputable section
open Classical
open scoped BigOperators

def actualPrimeRowAP (N : ℕ) (X : ℝ) (p q d : ℕ) : Finset ℕ :=
  (rowAPDiv N X p q d 1).filter Nat.Prime

theorem actualPrimeRowAP_iff {N p q d r : ℕ} {X : ℝ} :
    r ∈ actualPrimeRowAP N X p q d ↔
      (⟨(p, r), q⟩ : P5zU9Triple) ∈ labels N X ∧ Nat.ModEq d (p * r * q) N := by
  simp only [actualPrimeRowAP, rowAPDiv, Finset.mem_filter, one_dvd, and_true]
  constructor
  · rintro ⟨⟨hr, hAP⟩, hprime⟩
    exact ⟨preprimeRow_prime_iff.mp ⟨hr, hprime⟩, hAP⟩
  · rintro ⟨ht, hAP⟩
    obtain ⟨hr, hprime⟩ := preprimeRow_prime_iff.mpr ht
    exact ⟨⟨hr, hAP⟩, hprime⟩

/-- An actual prime at least z survives the ordinary sieve. All primes
dividing d*N are excluded from that sieve, and two requires no exception. -/
private theorem large_prime_coprime_product {N d z r : ℕ}
    (hr : Nat.Prime r) (hrz : z ≤ r) : Nat.Coprime r (sieveProduct (d * N) z) := by
  rw [sieveProduct, Nat.coprime_prod_right_iff]
  intro ell hell
  have hd := mem_sievePrimes.mp hell
  apply (Nat.coprime_primes hr hd.2.1).mpr
  intro heq
  have hbad : r < z := by simpa only [heq] using hd.1
  omega

/-- Only the explicit small-prime receiver of this ORDINARY row is paid.
There is no use of a prime-receiver switching bound for this step. -/
theorem actualPrimeRowAP_card_le_sifted_add_cap (N d z : ℕ) (X : ℝ) (p q : ℕ) :
    ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      ((siftedPreprimeRow N d z X p q).card : ℝ) + (z : ℝ) := by
  let S := actualPrimeRowAP N X p q d
  let small := S.filter fun r => r < z
  let large := S.filter fun r => ¬r < z
  have hsmall : small.card ≤ z := by
    calc
      _ ≤ (Finset.range z).card := by
        apply Finset.card_le_card
        intro r hr
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hr).2
      _ = _ := Finset.card_range z
  have hlarge : large ⊆ siftedPreprimeRow N d z X p q := by
    intro r hr
    obtain ⟨hrS, hrz⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrow, hprime⟩ := Finset.mem_filter.mp hrS
    exact Finset.mem_filter.mpr
      ⟨hrow, large_prime_coprime_product hprime (Nat.le_of_not_gt hrz)⟩
  have hcard := Finset.card_le_card hlarge
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun r => r < z)
  have hnat : S.card ≤ (siftedPreprimeRow N d z X p q).card + z := by
    change small.card + large.card = S.card at hsplit
    omega
  exact_mod_cast hnat

/-- Exact generic-Selberg joining at the ordinary local density, with
the actual full-lcm endpoint remainder visible in every divisor term. -/
theorem siftedRow_le_endpointSelberg
    (N d z L : ℕ) (hL : 1 ≤ L) (X : ℝ) (p q : ℕ)
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) :
    ((siftedPreprimeRow N d z X p q).card : ℝ) ≤
      endpointMass N X p q d 1 / ordinaryG (d * N) z L +
      ∑ e ∈ (sieveProduct (d * N) z).divisors,
        |ordinaryRho N d z L e| *
          |endpointMass N X p q d e - endpointMass N X p q d 1 / (e : ℝ)| := by
  let s := ordinaryRowSieve N d z X p q
  have h := siftedSum_le_finiteSelbergNormalizer_add_errSum s hL
  have herr : s.errSum (BoundingSieve.lambdaSquared (finiteSelbergWeight s L)) =
      ∑ e ∈ (sieveProduct (d * N) z).divisors,
        |ordinaryRho N d z L e| *
          |endpointMass N X p q d e - endpointMass N X p q d 1 / (e : ℝ)| := by
    unfold BoundingSieve.errSum
    change (∑ e ∈ (sieveProduct (d * N) z).divisors,
      |BoundingSieve.lambdaSquared (finiteSelbergWeight s L) e| * |s.rem e|) = _
    rw [ordinaryRow_weight_eq]
    apply Finset.sum_congr rfl
    intro e he
    rw [ordinaryRow_remainder_endpoints hf hX hd (Nat.pos_of_mem_divisors he)]
    rfl
  rw [ordinaryRow_siftedSum, ordinaryRow_normalizer] at h
  change ((siftedPreprimeRow N d z X p q).card : ℝ) ≤
    ((rowAPDiv N X p q d 1).card : ℝ) / ordinaryG (d * N) z L +
      s.errSum (BoundingSieve.lambdaSquared (finiteSelbergWeight s L)) at h
  rw [rowAPDiv_card_real_eq_endpointMass hf hX hd zero_lt_one, herr] at h
  exact h

/-- A concrete finite upper bound for the original p₂-prime AP row.
The matching coefficients precede the selected ORIGINAL factor row.
Every remainder is explicit, and the ordinary-row analytical saving is
still a separate OPEN obligation. -/
theorem actualPrimeRowAP_le_endpointSelberg
    (N d z L : ℕ) (hL : 1 ≤ L) (X : ℝ) (p q : ℕ)
    (hf : factorAllowed N p q) (hX : 0 ≤ X) (hd : 0 < d) :
    ((actualPrimeRowAP N X p q d).card : ℝ) ≤
      endpointMass N X p q d 1 / ordinaryG (d * N) z L +
      (∑ e ∈ (sieveProduct (d * N) z).divisors,
        |ordinaryRho N d z L e| *
          |endpointMass N X p q d e - endpointMass N X p q d 1 / (e : ℝ)|) +
      (z : ℝ) := by
  exact (actualPrimeRowAP_card_le_sifted_add_cap N d z X p q).trans
    (add_le_add_right (siftedRow_le_endpointSelberg N d z L hL X p q hf hX hd) _)

end
end ImbalancedChen.U9SemiprimeSwitch
