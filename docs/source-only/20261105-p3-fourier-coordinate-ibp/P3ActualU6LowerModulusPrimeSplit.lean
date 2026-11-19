import ImbalancedChen.P3ActualU6LowerActualPrimeCarrier
import ImbalancedChen.P3ActualEvenLowerPrefixedPrimitiveMean
import Mathlib.Tactic

/-!
P3.6: exact split of the indispensable modulus-prime correction for the
ORIGINAL U6 even-first-exit LOWER integer source.

Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
paper/source/modules/distribution-prime-product-completion-20261010.txt
§1 PP and §4 F; manuscript-body.tex eq:current-PP.

The actual AP modulus is b*q, with b=t.1*t.2 and q a genuine retained
small/rough quotient. Production already proves Coprime b q. Therefore
prime divisors of b*q split DISJOINTLY into primes of b and primes of q.
The former correction is exactly a scalar multiple of the SAME signed
physical primitive mean; the latter remains a signed quotient-prime
correction. Neither is silently deleted or bounded by a PP hypothesis.

This is only a finite-algebra candidate. No arithmetic saving or complete
causal rho_N identity follows. SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualU6LowerModulusPrimeSplit

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualU6LowerActualPrimeCarrier
open ImbalancedChen.P3ActualEvenLowerPrefixedPrimitiveMean

/-- Actual inclusive prime-divisor count is additive under a genuine
coprime factorization, including the exact prime-prefix cutoff N.
Without coprimality, the common-prime intersection is nonempty and this
formula is generally false. -/
theorem prime_divisor_count_coprime_mul
    (N b q : ℕ) (hcop : Nat.Coprime b q) :
    chenPrimeDivisorCount N (b * q) =
      chenPrimeDivisorCount N b + chenPrimeDivisorCount N q := by
  classical
  let P := chenPrimePrefix N
  let S := P.filter (fun p => p ∣ b)
  let T := P.filter (fun p => p ∣ q)
  have hdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    have hpb : p ∣ b := (Finset.mem_filter.mp hpS).2
    have hpq : p ∣ q := (Finset.mem_filter.mp hpT).2
    have hpgcd : p ∣ Nat.gcd b q := Nat.dvd_gcd hpb hpq
    have hpone : p ∣ 1 := by
      simpa only [hcop.gcd_eq_one] using hpgcd
    have hpprime : Nat.Prime p :=
      (mem_chenPrimePrefix.mp (Finset.mem_filter.mp hpS).1).2
    have hp_eq_one : p = 1 := Nat.dvd_one.mp hpone
    omega
  have hfilter :
      P.filter (fun p => p ∣ b * q) = S ∪ T := by
    ext p
    simp only [P, S, T, Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hp, hpdiv⟩
      rcases ((mem_chenPrimePrefix.mp hp).2.dvd_mul).mp hpdiv with hb | hq
      · exact Or.inl ⟨hp, hb⟩
      · exact Or.inr ⟨hp, hq⟩
    · rintro (⟨hp, hb⟩ | ⟨hp, hq⟩)
      · exact ⟨hp, dvd_mul_of_dvd_left hb q⟩
      · exact ⟨hp, dvd_mul_of_dvd_right hq b⟩
  unfold chenPrimeDivisorCount
  change ((P.filter (fun p => p ∣ b * q)).card : ℝ) =
    (S.card : ℝ) + (T.card : ℝ)
  rw [hfilter, Finset.card_union_of_disjoint hdisj, Nat.cast_add]

/-- Separates the full-modulus prime correction into (i) a prefix-prime
scalar times its ORIGINAL signed full-modulus mean, plus (ii) primes of
the actual quotient q. It preserves all negative rho coefficients. -/
theorem signed_modulus_prime_correction_split
    (N b : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hcop : ∀ q ∈ Q, Nat.Coprime b q) :
    (∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N (b * q) / (Nat.totient (b * q) : ℝ))) =
      chenPrimeDivisorCount N b *
        (∑ q ∈ Q, (rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
      (∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))) := by
  calc
    _ = ∑ q ∈ Q,
      chenPrimeDivisorCount N b *
        ((rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
      (rho q : ℝ) *
        (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [prime_divisor_count_coprime_mul N b q (hcop q hq)]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- This split uses the ORIGINAL sixthSupport row, original retention
policy and original even-exit lower integer rho. Coprimality is obtained
from production; it is NOT added as a row hypothesis. -/
theorem actual_U6_lower_modulus_prime_correction_split
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    (∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N (b * q) / (Nat.totient (b * q) : ℝ))) =
      chenPrimeDivisorCount N b *
        (∑ q ∈ Q, (rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
      (∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))) := by
  dsimp
  apply signed_modulus_prime_correction_split
  intro q hq
  exact actual_u6_lower_moduli_coprime_prefix N t ht policy w hwz hq

/-- The original labelled U6 AP sum is now centred at the carrier size
MINUS the prefix-prime correction. The remaining quotient-prime term is
explicit and must still be paid in the final signed PP estimate. No
fibrewise relative Theta estimate or arithmetic cancellation is assumed. -/
theorem actual_U6_lower_labelled_recenter_split
    (N : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    (∑ x ∈ P5CausalRhoFactorization.pairs (policy t) N cap (w t) z,
      (actualEvenLowerPairInt (policy t) N cap (w t) z (L t) x : ℝ) *
        (chenPrimeAPCount N N ((b * x.1) * x.2) -
         chenCentrePrimeAPCount N N ((b * x.1) * x.2))) =
      (((chenAdditivePrimeCarrier N).card : ℝ) -
         chenPrimeDivisorCount N b) *
        (∑ q ∈ Q, (rho q : ℝ) / (Nat.totient (b * q) : ℝ)) +
      (∑ q ∈ Q, (rho q : ℝ) *
        finitePrimitiveDiscrepancy
          (chenAdditivePrimeCarrier N) (fun _ => 1) N (b * q)) -
      (∑ q ∈ Q, (rho q : ℝ) *
        (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))) := by
  have hbase := original_U6_lower_labelled_additive_source_recenter
    N t ht policy w L hwz
  have hsplit := actual_U6_lower_modulus_prime_correction_split
    N t ht policy w L hwz
  dsimp at hbase hsplit ⊢
  rw [hbase, hsplit]
  ring

end
end ImbalancedChen.P3ActualU6LowerModulusPrimeSplit
