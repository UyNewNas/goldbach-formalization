import ImbalancedChen.CurrentChenUpsilon10OverlapFiniteMean
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Divisors

/-!
# Exact signed divisor split at the first selected prime

For the literal current U10 four-prefix b, set P=P_N(p₂), R=P/p₁.
Then gcd(b,P)=p₁ and Coprime b R. The exact full-modulus density is

  sum_(d|P) rho(d)/phi(b*d)
    = 1/phi(b) * sum_(e|R) (rho(e)+rho(p₁*e)/p₁)/phi(e).

The coefficient rho is arbitrary and signed. In the actual Rosser
specialization its two original level-zero tests remain untouched.
SOURCE-WRITTEN, UNCOMPILED. No analytic limit is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

namespace P5U10OriginalMean

/-- Divisors of pR have exactly the two displayed shapes. Coprimality
is needed for disjointness below, but not for this finite union identity. -/
theorem divisors_prime_mul_eq_union {p R : ℕ} (hp : Nat.Prime p) (hR : R ≠ 0) :
    (p * R).divisors = R.divisors ∪ R.divisors.image (fun e => p * e) := by
  ext d
  constructor
  · intro hd
    obtain ⟨a, e, hap, heR, hae⟩ := Nat.dvd_mul.mp (Nat.mem_divisors.mp hd).1
    rcases (Nat.dvd_prime hp).mp hap with ha | ha
    · subst a
      simp only [one_mul] at hae
      subst d
      exact Finset.mem_union_left _ (Nat.mem_divisors.mpr ⟨heR, hR⟩)
    · subst a
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨e, Nat.mem_divisors.mpr ⟨heR, hR⟩, hae⟩)
  · intro hd
    have hprod : p * R ≠ 0 := mul_ne_zero hp.ne_zero hR
    rcases Finset.mem_union.mp hd with hd | hd
    · exact Nat.mem_divisors.mpr
        ⟨dvd_mul_of_dvd_right (Nat.mem_divisors.mp hd).1 p, hprod⟩
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact Nat.mem_divisors.mpr
        ⟨mul_dvd_mul (dvd_refl p) (Nat.mem_divisors.mp he).1, hprod⟩

theorem divisors_prime_mul_split_disjoint {p R : ℕ} (hp : Nat.Prime p)
    (hcop : Nat.Coprime p R) :
    Disjoint R.divisors (R.divisors.image (fun e => p * e)) := by
  apply Finset.disjoint_left.mpr
  intro d hd himage
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp himage
  have hpd : p ∣ d := by rw [← he]; exact dvd_mul_right p e
  exact hp.coprime_iff_not_dvd.mp hcop (hpd.trans (Nat.mem_divisors.mp hd).1)

/-- This sum identity applies to every signed function; no Euler-product
or multiplicativity premise is present. -/
theorem sum_divisors_prime_mul_split {p R : ℕ} (hp : Nat.Prime p)
    (hR : R ≠ 0) (hcop : Nat.Coprime p R) (f : ℕ → ℝ) :
    (∑ d ∈ (p * R).divisors, f d) =
      (∑ e ∈ R.divisors, f e) + ∑ e ∈ R.divisors, f (p * e) := by
  rw [divisors_prime_mul_eq_union hp hR,
    Finset.sum_union (divisors_prime_mul_split_disjoint hp hcop)]
  congr 1
  apply Finset.sum_image
  intro e _ e' _ he
  exact Nat.eq_of_mul_eq_mul_left hp.pos he

/-- The generic overlapping-totient dictionary. The entire dependence
of rho on its argument is retained in rho(e) and rho(p*e). -/
theorem signed_overlap_divisor_sum {p b R : ℕ} (hp : Nat.Prime p)
    (hR : R ≠ 0) (hcop : Nat.Coprime b R) (hpb : p ∣ b) (rho : ℕ → ℝ) :
    (∑ d ∈ (p * R).divisors, rho d / (Nat.totient (b * d) : ℝ)) =
      1 / (Nat.totient b : ℝ) *
        ∑ e ∈ R.divisors, (rho e + rho (p * e) / (p : ℝ)) /
          (Nat.totient e : ℝ) := by
  rw [sum_divisors_prime_mul_split hp hR (hcop.of_dvd_left hpb),
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hbe := hcop.of_dvd_right (Nat.mem_divisors.mp he).1
  have htot : Nat.totient (b * (p * e)) = p * Nat.totient (b * e) := by
    rw [show b * (p * e) = p * (b * e) by ring,
      Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_left hpb e)]
  rw [htot, Nat.totient_mul hbe]
  simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

def residualProduct (N : ℕ) (t : Label) : ℕ := sieveProduct N t.1.2 / t.1.1

theorem first_dvd_sieveProduct {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    t.1.1 ∣ sieveProduct N t.1.2 := by
  unfold sieveProduct
  exact Finset.dvd_prod_of_mem id (first_mem_sievePrimes ht)

theorem first_mul_residualProduct {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    t.1.1 * residualProduct N t = sieveProduct N t.1.2 :=
  Nat.mul_div_cancel' (first_dvd_sieveProduct ht)

theorem residualProduct_ne_zero {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    residualProduct N t ≠ 0 := by
  intro hzero
  have hmul := first_mul_residualProduct ht
  rw [hzero, mul_zero] at hmul
  exact (sieveProduct_squarefree N t.1.2).ne_zero hmul.symm

private theorem prime_coprime_sieveProduct_of_ge {N p z : ℕ}
    (hp : Nat.Prime p) (hzp : z ≤ p) : Nat.Coprime p (sieveProduct N z) := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hlt := (mem_sievePrimes.mp (prime_mem_sievePrimes_of_dvd hp hd)).1
  omega

/-- Only the first prime of the literal increasing four-prefix can
divide the strict sieve product at p₂. -/
theorem remainingMultiplier_coprime_sieveProduct {N : ℕ} {t : Label}
    (ht : t ∈ selector N) :
    Nat.Coprime (t.1.2 * t.2.1 * t.2.2) (sieveProduct N t.1.2) := by
  obtain ⟨hc, _, h12, h23, h34, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hfirst, hlast⟩ := Finset.mem_product.mp hc
  have h2 := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hfirst).2).2.1
  have h3 := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hlast).1).2.1
  have h4 := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hlast).2).2.1
  exact Nat.coprime_mul_iff_left.mpr ⟨Nat.coprime_mul_iff_left.mpr
    ⟨prime_coprime_sieveProduct_of_ge h2 le_rfl,
      prime_coprime_sieveProduct_of_ge h3 h23.le⟩,
    prime_coprime_sieveProduct_of_ge h4 (h23.trans h34).le⟩

theorem gcd_multiplier_sieveProduct {N : ℕ} {t : Label} (ht : t ∈ selector N) :
    Nat.gcd (multiplier t) (sieveProduct N t.1.2) = t.1.1 := by
  have hmul : multiplier t = (t.1.2 * t.2.1 * t.2.2) * t.1.1 := by
    unfold multiplier
    ring
  rw [hmul]
  exact Nat.gcd_mul_of_coprime_of_dvd (remainingMultiplier_coprime_sieveProduct ht)
    (first_dvd_sieveProduct ht)

/-- The residual product P/p₁ is genuinely coprime to the complete
four-prime multiplier, proved from the actual selector and squarefree P. -/
theorem multiplier_coprime_residualProduct {N : ℕ} {t : Label}
    (ht : t ∈ selector N) : Nat.Coprime (multiplier t) (residualProduct N t) := by
  have h := Nat.coprime_div_gcd_of_squarefree (sieveProduct_squarefree N t.1.2)
    (Nat.ne_of_gt (multiplier_pos ht))
  rw [Nat.gcd_comm (sieveProduct N t.1.2) (multiplier t),
    gcd_multiplier_sieveProduct ht] at h
  exact h.symm

theorem residual_divisor_coprime_multiplier {N : ℕ} {t : Label}
    (ht : t ∈ selector N) {e : ℕ} (he : e ∈ (residualProduct N t).divisors) :
    Nat.Coprime (multiplier t) e :=
  (multiplier_coprime_residualProduct ht).of_dvd_right (Nat.mem_divisors.mp he).1

/-- Actual current-selector specialization for an arbitrary signed rho,
with no local-coprimality hypothesis left for the caller to supply. -/
theorem current_signed_overlap_divisor_sum {N : ℕ} {t : Label}
    (ht : t ∈ selector N) (rho : ℕ → ℝ) :
    (∑ d ∈ (sieveProduct N t.1.2).divisors,
      rho d / (Nat.totient (multiplier t * d) : ℝ)) =
      1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          (rho e + rho (t.1.1 * e) / (t.1.1 : ℝ)) / (Nat.totient e : ℝ) := by
  have hp := (mem_sievePrimes.mp (first_mem_sievePrimes ht)).2.1
  have hpb : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  calc
    _ = ∑ d ∈ (t.1.1 * residualProduct N t).divisors,
        rho d / (Nat.totient (multiplier t * d) : ℝ) := by
      rw [first_mul_residualProduct ht]
    _ = _ := signed_overlap_divisor_sum hp (residualProduct_ne_zero ht)
      (multiplier_coprime_residualProduct ht) hpb rho

theorem support_eq_sieveProduct_divisors (N : ℕ) (t : Label) :
    support N t = (sieveProduct N t.1.2).divisors := by
  unfold support actualSmallRosserSupport
  congr 1
  simpa using currentChen_actualSmallPrimeProduct_eq_sieveProduct
    N t.1.2 (t.1.2 : ℝ) le_rfl

/-- The effective coefficient keeps both original Rosser evaluations at
their original arguments. In particular no multiplicativity is asserted. -/
def effectiveCoefficient (N : ℕ) (t : Label) (L : ℝ) (e : ℕ) : ℝ :=
  coefficient N t L e + coefficient N t L (t.1.1 * e) / (t.1.1 : ℝ)

/-- Exact effective-weight dictionary for the actual U10 overlap density. -/
theorem overlapDensity_eq_effectiveCoefficient_sum {N : ℕ} {t : Label}
    (ht : t ∈ selector N) (L : ℝ) :
    overlapDensity N t L =
      1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t L e / (Nat.totient e : ℝ) := by
  unfold overlapDensity effectiveCoefficient
  rw [support_eq_sieveProduct_divisors]
  exact current_signed_overlap_divisor_sum ht (coefficient N t L)

/-- Signed coefficient cancellation is preserved. Only a safe absolute
bound is inferred; the transformed coefficient need not have unit bound. -/
theorem effectiveCoefficient_abs_le (N : ℕ) (t : Label) (L : ℝ) (e : ℕ) :
    |effectiveCoefficient N t L e| ≤ 1 + 1 / (t.1.1 : ℝ) := by
  unfold effectiveCoefficient
  apply (abs_add_le _ _).trans
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
  exact add_le_add (coefficient_abs_le_one N t L e)
    (div_le_div_of_nonneg_right (coefficient_abs_le_one N t L (t.1.1 * e))
      (Nat.cast_nonneg _))

/-- At and beyond its original strict level the overlapping branch
vanishes. Its test is on p₁*e, not on e alone. -/
theorem effectiveCoefficient_eq_first_of_level_le (N : ℕ) (t : Label) (L : ℝ)
    (e : ℕ) (hlevel : L ≤ ((t.1.1 * e : ℕ) : ℝ)) :
    effectiveCoefficient N t L e = coefficient N t L e := by
  have hz : coefficient N t L (t.1.1 * e) = 0 := by
    by_contra hnonzero
    exact (not_lt_of_ge hlevel) (actualSmallRosserPlus_active hnonzero).2.1
  simp only [effectiveCoefficient, hz, zero_div, add_zero]

/-- The exact effective-weight dictionary now feeds the original U10
finite mean, with no coprime-multiplier assumption on b against P. -/
theorem currentChenUpsilon10_upper_effective (N : ℕ) (M : ℝ) (L : Label → ℝ)
    (hL : ∀ t ∈ selector N, 1 < L t)
    (hpL : ∀ t ∈ selector N, (t.1.2 : ℝ) ≤ L t) :
    currentChenUpsilon10 N ≤
      M * (∑ t ∈ selector N, 1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t (L t) e / (Nat.totient e : ℝ)) +
        (∑ t ∈ selector N, signedAPError N M t (L t)) -
        ∑ t ∈ selector N, signedCentre N t (L t) := by
  have h := currentChenUpsilon10_upper N M L hL hpL
  have hmain : (∑ t ∈ selector N, overlapDensity N t (L t)) =
      ∑ t ∈ selector N, 1 / (Nat.totient (multiplier t) : ℝ) *
        ∑ e ∈ (residualProduct N t).divisors,
          effectiveCoefficient N t (L t) e / (Nat.totient e : ℝ) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact overlapDensity_eq_effectiveCoefficient_sum ht (L t)
  rwa [hmain] at h

/-- The full physical coefficient level is retained on each branch.
The first-overlap branch has the stronger p₁*e product modulus. -/
theorem effective_branches_physical_caps {N Q : ℕ} {t : Label}
    (ht : t ∈ selector N) {e : ℕ} :
    (coefficient N t (chenQuotientRowLevel Q (multiplier t) : ℝ) e ≠ 0 →
      multiplier t * e ≤ Q) ∧
    (coefficient N t (chenQuotientRowLevel Q (multiplier t) : ℝ) (t.1.1 * e) ≠ 0 →
      multiplier t * (t.1.1 * e) ≤ Q) := by
  exact ⟨fun he => active_physical_cap ht he, fun he => active_physical_cap ht he⟩

end P5U10OriginalMean

end

end ImbalancedChen
