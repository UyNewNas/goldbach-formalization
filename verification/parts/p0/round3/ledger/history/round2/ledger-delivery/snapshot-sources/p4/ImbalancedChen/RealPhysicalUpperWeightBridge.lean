import ImbalancedChen.PhysicalUpperWeightBridge
import ImbalancedChen.RealHalfProductSource
import ImbalancedChen.CurvedRegionDiscrepancy
import ImbalancedChen.ActualSmallRoughAttachment

/-!
# One physical upper weight on the arbitrary-real ordered source

This module extends the finite physical-weight bridge to the literal real
exponent in the current theorem. The same coefficient occurs in its divisor
sum, reciprocal-totient density, coprime correction and signed distribution
error. The source retains its inclusive product endpoint; the counted prime
partner filter retains its strict endpoint. Prime squares and ordered-factor
uniqueness are inherited from RealHalfProductSource.

The only finite losses in the count bridge are the displayed small-prime
partner cap and the real lower-cutoff loss. Under the existing rough-factor
gate the coprime correction vanishes exactly, also for signed coefficients.
No density constant, distribution estimate or asymptotic upper count is
asserted in this file.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The actual congruence mass of the arbitrary-real ordered source. -/
def realHalfProductCongruenceMass (b : ℝ) (N : ℕ) (T : ℝ) (d : ℕ) : ℝ :=
  (((realHalfProductSource b N T).filter
    (fun m : ℕ => Nat.ModEq d m N)).card : ℝ)

/-- The same source restricted by the literal coprimality mask. -/
def realHalfProductCoprimeMass (b : ℝ) (N : ℕ) (T : ℝ) (d : ℕ) : ℝ :=
  (((realHalfProductSource b N T).filter
    (fun m : ℕ => Nat.Coprime m d)).card : ℝ)

/-- The exact price of replacing the coprime mass by the total real source. -/
def realPhysicalCoprimeCorrection
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Q, rho d *
    ((realHalfProductCoprimeMass b N T d -
      ((realHalfProductSource b N T).card : ℝ)) / (Nat.totient d : ℝ))

/-- The signed primitive-residue error for exactly the displayed coefficient. -/
def realPhysicalDistributionError
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Q, rho d *
    (realHalfProductCongruenceMass b N T d -
      realHalfProductCoprimeMass b N T d / (Nat.totient d : ℝ))

/-- Natural subtraction agrees with the moving residue on the full source,
including the endpoint with shifted value zero. -/
theorem realHalfProductSource_filter_dvd_eq_filter_modEq
    (b : ℝ) (N d : ℕ) (T : ℝ) :
    (realHalfProductSource b N T).filter (fun m : ℕ => d ∣ N - m) =
      (realHalfProductSource b N T).filter (fun m : ℕ => Nat.ModEq d m N) := by
  classical
  apply Finset.filter_congr
  intro m hm
  exact dvd_sub_iff_modEq_of_le (mem_realHalfProductSource.mp hm).1

/-- Exact finite Fubini with the real imbalance parameter unchanged. -/
theorem sum_physicalDivisorSum_realHalfProductSource
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ realHalfProductSource b N T,
      physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d := by
  classical
  unfold physicalDivisorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [realHalfProductSource_filter_dvd_eq_filter_modEq]
  unfold realHalfProductCongruenceMass
  ring

/-- Density, exact coprime correction and signed distribution error are
three terms of one identity for one coefficient. -/
theorem sum_rho_mul_realHalfProductCongruenceMass_eq
    (b : ℝ) (N : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d) =
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho := by
  unfold physicalDensitySum realPhysicalCoprimeCorrection realPhysicalDistributionError
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The literal sifted real source, with the original inclusive product cap. -/
def realSiftedHalfProductSource (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) : Finset ℕ := by
  classical
  exact (realHalfProductSource b N T).filter
    (fun m : ℕ => Nat.Coprime (N - m) (sieveProduct N z))

@[simp] theorem mem_realSiftedHalfProductSource {b T : ℝ} {N m z : ℕ} :
    m ∈ realSiftedHalfProductSource b N T z ↔
      m ∈ realHalfProductSource b N T ∧
        Nat.Coprime (N - m) (sieveProduct N z) := by
  classical
  simp only [realSiftedHalfProductSource, Finset.mem_filter]

/-- A pointwise upper divisor sum bounds the real sifted source. Its
nonnegativity on composite shifted arguments is included in the premise. -/
theorem realSiftedHalfProductSource_card_le_sum_physicalDivisorSum
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m) := by
  classical
  calc
    ((realSiftedHalfProductSource b N T z).card : ℝ) =
        ∑ m ∈ realHalfProductSource b N T,
          if Nat.Coprime (N - m) (sieveProduct N z) then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]
      simp [realSiftedHalfProductSource]
    _ ≤ _ := Finset.sum_le_sum fun m hm => hmajor (N - m)

/-- Finite same-weight upper bound before the two localization losses. -/
theorem realSiftedHalfProductSource_card_le_same_rho_main_add_errors
    (b : ℝ) (N z : ℕ) (T : ℝ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho := by
  calc
    ((realSiftedHalfProductSource b N T z).card : ℝ) ≤
        ∑ m ∈ realHalfProductSource b N T, physicalDivisorSum Q rho (N - m) :=
      realSiftedHalfProductSource_card_le_sum_physicalDivisorSum b N z T Q rho hmajor
    _ = ∑ d ∈ Q, rho d * realHalfProductCongruenceMass b N T d :=
      sum_physicalDivisorSum_realHalfProductSource b N T Q rho
    _ = _ := sum_rho_mul_realHalfProductCongruenceMass_eq b N T Q rho

/-- Prime partners at least the strict sieve cap survive. Smaller prime
partners have at most z distinct receivers, by injective complementation. -/
theorem realHalfProductSource_primePartner_card_le_realSifted_add_cap
    (b : ℝ) (N z : ℕ) (T : ℝ) :
    ((realHalfProductSource b N T).filter
      (fun m => m < N ∧ Nat.Prime (N - m))).card ≤
      (realSiftedHalfProductSource b N T z).card + z := by
  classical
  let A := (realHalfProductSource b N T).filter
    (fun m => m < N ∧ Nat.Prime (N - m))
  have hlarge : A.filter (fun m => z ≤ N - m) ⊆
      realSiftedHalfProductSource b N T z := by
    intro m hm
    obtain ⟨hmA, hz⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmSource, hmN, hp⟩ := Finset.mem_filter.mp hmA
    exact mem_realSiftedHalfProductSource.mpr
      ⟨hmSource, prime_coprime_sieveProduct_of_cap_le hp hz⟩
  have hsmall : (A.filter (fun m => ¬z ≤ N - m)).card ≤ z := by
    calc
      (A.filter (fun m => ¬z ≤ N - m)).card ≤ (Finset.range z).card := by
        apply Finset.card_le_card_of_injOn (fun m : ℕ => N - m)
        · intro m hm
          exact Finset.mem_range.mpr (lt_of_not_ge (Finset.mem_filter.mp hm).2)
        · intro m hm n hn hmn
          have hmA := (Finset.mem_filter.mp hm).1
          have hnA := (Finset.mem_filter.mp hn).1
          have hmN := (Finset.mem_filter.mp hmA).2.1
          have hnN := (Finset.mem_filter.mp hnA).2.1
          change N - m = N - n at hmn
          omega
      _ = z := Finset.card_range z
  calc
    A.card = (A.filter (fun m => z ≤ N - m)).card +
        (A.filter (fun m => ¬z ≤ N - m)).card :=
      (Finset.card_filter_add_card_filter_not A (fun m => z ≤ N - m)).symm
    _ ≤ _ := Nat.add_le_add (Finset.card_le_card hlarge) hsmall

/-- RealB enters the finite sieve without rationalizing b. Both endpoint
losses remain displayed, and no estimate for the density is substituted. -/
theorem RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (hb : b < 1) (hT : 0 ≤ T) :
    (RealB b N : ℝ) ≤
      ((realSiftedHalfProductSource b N T z).card : ℝ) + (z : ℝ) + (T + 1) := by
  rw [RealB_eq_realHalfProductSource_filter_card_add_small hb N T]
  push_cast
  have hprime :
      (((realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card : ℝ) ≤
        ((realSiftedHalfProductSource b N T z).card : ℝ) + (z : ℝ) := by
    exact_mod_cast realHalfProductSource_primePartner_card_le_realSifted_add_cap b N z T
  exact add_le_add hprime (smallRealBadReceivers_cast_card_lt hT).le

/-- The complete finite bad count is bounded by one actual divisor sum. -/
theorem RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      (∑ m ∈ realHalfProductSource b N T,
        physicalDivisorSum Q rho (N - m)) + (z : ℝ) + (T + 1) := by
  exact (RealB_cast_le_realSiftedHalfProductSource_card_add_cap_cutoff N z hb hT).trans
    (add_le_add_right (add_le_add_right
      (realSiftedHalfProductSource_card_le_sum_physicalDivisorSum b N z T Q rho hmajor)
      (z : ℝ)) (T + 1))

/-- Exact assembly interface for the upper analytic estimate. Every term
uses this one rho, and no lower-count hypothesis appears. -/
theorem RealB_cast_le_same_rho_main_add_errors
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalCoprimeCorrection b N T Q rho +
        realPhysicalDistributionError b N T Q rho + (z : ℝ) + (T + 1) := by
  have h := RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff N z Q rho hb hT hmajor
  rw [sum_physicalDivisorSum_realHalfProductSource,
    sum_rho_mul_realHalfProductCongruenceMass_eq] at h
  exact h

/-- The existing elementary real-power geometry applies to every prime
divisor of the source, with no rational exponent or distinctness premise. -/
theorem realHalfProductSource_prime_divisor_rough
    {b T : ℝ} {N m ell : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hm : m ∈ realHalfProductSource b N T)
    (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    T ^ (b / (1 + b)) < (ell : ℝ) := by
  obtain ⟨hmN, hcut, r, q, hr, hq, hmul, hrq, hbad⟩ :=
    mem_realHalfProductSource.mp hm
  have hcut' : T ≤ (r * q : ℕ) := by simpa only [hmul] using hcut
  obtain ⟨hroughR, hroughQ⟩ :=
    prime_halfProduct_rpow_lt_factors hb hT hr hq hbad hrq hcut'
  rw [hmul] at hdvd
  rcases (prime_dvd_halfProduct_iff hell hr hq).mp hdvd with h | h
  · simpa only [h] using hroughR
  · simpa only [h] using hroughQ

/-- Under the genuine roughness gate, every source member is coprime to
every divisor of the actual sieve product. -/
theorem realHalfProductSource_coprime_of_dvd_sieveProduct
    {b T : ℝ} {N m z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hm : m ∈ realHalfProductSource b N T) (hd : d ∣ sieveProduct N z) :
    Nat.Coprime m d := by
  have hproduct : Nat.Coprime m (sieveProduct N z) := by
    classical
    unfold sieveProduct
    apply Nat.coprime_prod_right_iff.mpr
    intro ell hell
    obtain ⟨hellz, hp, hnot⟩ := mem_sievePrimes.mp hell
    apply (hp.coprime_iff_not_dvd.mpr ?_).symm
    intro hdvd
    have hrough := realHalfProductSource_prime_divisor_rough hb hT hm hp hdvd
    have hellzR : (ell : ℝ) < (z : ℝ) := Nat.cast_lt.mpr hellz
    exact (not_lt_of_ge (hellzR.le.trans hcap)) hrough
  exact hproduct.of_dvd_right hd

/-- Here the coprime mass is literally the total source mass. -/
theorem realHalfProductCoprimeMass_eq_card_of_gate
    {b T : ℝ} {N z d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b))) (hd : d ∣ sieveProduct N z) :
    realHalfProductCoprimeMass b N T d =
      ((realHalfProductSource b N T).card : ℝ) := by
  classical
  have hfilter : (realHalfProductSource b N T).filter
      (fun m : ℕ => Nat.Coprime m d) = realHalfProductSource b N T := by
    apply Finset.filter_eq_self.mpr
    intro m hm
    exact realHalfProductSource_coprime_of_dvd_sieveProduct hb hT hcap hm hd
  rw [realHalfProductCoprimeMass, hfilter]

/-- Only active coefficients must satisfy the modulus support gate. Signed
coefficients and displayed zero terms introduce no further correction. -/
theorem realPhysicalCoprimeCorrection_eq_zero_of_gate
    {b T : ℝ} {N z : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hT : 0 < T) (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z) :
    realPhysicalCoprimeCorrection b N T Q rho = 0 := by
  unfold realPhysicalCoprimeCorrection
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hrho : rho d = 0
  · simp only [hrho, zero_mul]
  · rw [realHalfProductCoprimeMass_eq_card_of_gate hb hT hcap (hsupport d hd hrho)]
    simp

/-- The finite same-weight bound with the proved zero coprime correction.
This still leaves the density and signed distribution error explicit. -/
theorem RealB_cast_le_same_rho_main_add_distribution_of_gate
    {b T : ℝ} (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hb1 : b < 1) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (b / (1 + b)))
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N z)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) * physicalDensitySum Q rho +
        realPhysicalDistributionError b N T Q rho + (z : ℝ) + (T + 1) := by
  have h := RealB_cast_le_same_rho_main_add_errors N z Q rho hb1 hT.le hmajor
  rw [realPhysicalCoprimeCorrection_eq_zero_of_gate Q rho hb hT hcap hsupport,
    add_zero] at h
  exact h

/-- Weighted Fubini on a common carrier below the target. The explicit
carrier bound is essential when the shift is natural subtraction. -/
theorem sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      ∑ d ∈ Q, rho d * finiteCongruenceMass S weight N d := by
  classical
  unfold physicalDivisorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  unfold finiteCongruenceMass
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [dvd_sub_iff_modEq_of_le (hSN m hm)]
  by_cases hmod : Nat.ModEq d m N
  · simp only [hmod, if_pos, mul_comm]
  · simp only [hmod, if_neg, mul_zero]

/-- The weighted outer-source decomposition keeps the sign of rho until
after the complete physical modulus sum. No absolute discrepancy sum is
introduced by the outer comparison. -/
theorem sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors
    (N : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hSN : ∀ m ∈ S, m ≤ N) :
    (∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m)) =
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        ∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d := by
  rw [sum_weight_mul_physicalDivisorSum_eq_rho_mul_finiteCongruenceMass
    N S Q weight rho hSN]
  unfold physicalDensitySum finitePrimitiveDiscrepancy
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Positive outer approximation is performed before the signed
distribution decomposition. This finite implication does not assert that
an arbitrary outer weight is admissible in an analytic supplier. The
carrier here stays below N; an extension beyond N needs an integer shift. -/
theorem RealB_cast_le_same_rho_outer_main_add_errors
    {b T : ℝ} (N z : ℕ) (S Q : Finset ℕ) (weight rho : ℕ → ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hSN : ∀ m ∈ S, m ≤ N)
    (hsource : realHalfProductSource b N T ⊆ S)
    (houter : ∀ m ∈ S,
      (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤ weight m)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    (RealB b N : ℝ) ≤
      finiteSourceMass S weight * physicalDensitySum Q rho +
        (∑ d ∈ Q, rho d *
          ((finiteCoprimeMass S weight d - finiteSourceMass S weight) /
            (Nat.totient d : ℝ))) +
        (∑ d ∈ Q, rho d * finitePrimitiveDiscrepancy S weight N d) +
        (z : ℝ) + (T + 1) := by
  classical
  have hnonneg : ∀ n : ℕ, 0 ≤ physicalDivisorSum Q rho n := by
    intro n
    have h := hmajor n
    split_ifs at h with hcop
    · exact zero_le_one.trans h
    · exact h
  have hsum :
      (∑ m ∈ realHalfProductSource b N T,
        physicalDivisorSum Q rho (N - m)) ≤
      ∑ m ∈ S, weight m * physicalDivisorSum Q rho (N - m) := by
    calc
      (∑ m ∈ realHalfProductSource b N T,
          physicalDivisorSum Q rho (N - m)) =
          ∑ m ∈ realHalfProductSource b N T,
            (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) *
              physicalDivisorSum Q rho (N - m) := by
        apply Finset.sum_congr rfl
        intro m hm
        simp only [hm, if_pos, one_mul]
      _ = ∑ m ∈ S,
          (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) *
            physicalDivisorSum Q rho (N - m) := by
        apply Finset.sum_subset hsource
        intro m hmS hmSource
        simp only [hmSource, if_neg, zero_mul]
      _ ≤ _ := Finset.sum_le_sum fun m hm =>
        mul_le_mul_of_nonneg_right (houter m hm) (hnonneg (N - m))
  have h := (RealB_cast_le_sum_physicalDivisorSum_add_cap_cutoff
    N z Q rho hb hT hmajor).trans
      (add_le_add_right (add_le_add_right hsum (z : ℝ)) (T + 1))
  rw [sum_weight_mul_physicalDivisorSum_eq_same_rho_main_add_errors
    N S Q weight rho hSN] at h
  exact h

/-- A covering enumeration cap can be removed exactly. The strict real
prime cutoff is the strict natural cutoff at its ceiling, also for
integral, zero and negative real cutoffs. No primality-at-endpoint atom
is added or removed. -/
theorem actualSmallPrimeFinset_eq_sievePrimes_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeFinset N cap z = sievePrimes N (Nat.ceil z) := by
  ext p
  rw [mem_actualSmallPrimeFinset_iff_of_cutoff_le_cap hzcap,
    mem_sievePrimes, Nat.lt_ceil]
  constructor
  · rintro ⟨hp, hpN, hpz⟩
    exact ⟨hpz, hp, hpN⟩
  · rintro ⟨hpz, hp, hpN⟩
    exact ⟨hp, hpN, hpz⟩

/-- The two actual finite products have exactly the same prime carrier. -/
theorem actualSmallPrimeProduct_eq_sieveProduct_ceil
    (N cap : ℕ) (z : ℝ) (hzcap : z ≤ (cap : ℝ)) :
    actualSmallPrimeProduct N cap z = sieveProduct N (Nat.ceil z) := by
  simp only [actualSmallPrimeProduct, sieveProduct,
    actualSmallPrimeFinset_eq_sievePrimes_ceil N cap z hzcap, id_eq]

/-- The actual all-integer roughness indicator is the literal finite
sieve-product indicator. This includes zero and negative test integers
and every target, without an evenness or target-positivity restriction. -/
theorem actualSmallRoughIndicator_eq_sieveProduct_natAbs
    (N : ℕ) (z : ℝ) (n : ℤ) :
    actualSmallRoughIndicator N z n =
      if Nat.Coprime n.natAbs (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
  classical
  have hiff := actualSmallPrimeProduct_coprime_natAbs_iff
    N (Nat.ceil z) z (Nat.le_ceil z) n
  rw [actualSmallPrimeProduct_eq_sieveProduct_ceil N (Nat.ceil z) z
    (Nat.le_ceil z)] at hiff
  rw [actualSmallRoughIndicator, ← hiff]
  simp only [Nat.coprime_comm]

/-- The proved majorant of the literal small/rough coefficient supplies
the exact premise of the real-source finite bridge. The natural sieve cap
is the ceiling of the same real z used by this coefficient. -/
theorem actualSmallRoughRho_sieveProduct_majorant
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z)
    (hzcap : z ≤ (cap : ℝ)) (n : ℕ) :
    (if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0) ≤
      physicalDivisorSum (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) n := by
  have h := actualSmallRoughRho_majorant retainOdd N cap w z L
    hL hwL hwz hzcap (n : ℤ)
  rw [actualSmallRoughIndicator_eq_sieveProduct_natAbs] at h
  simpa only [Int.natAbs_natCast] using h

/-- Every displayed small modulus divides the complete real-cap sieve
product. Only w ≤ z is needed for support inclusion; the enumeration cap
need not cover z for this one-way statement. -/
theorem actualSmallRosserSupport_dvd_sieveProduct_ceil
    (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRosserSupport N cap w) :
    d ∣ sieveProduct N (Nat.ceil z) := by
  apply (squarefree_dvd_iff_primeFactors_dvd
    (actualSmallRosserSupport_squarefree N cap w hd)).mpr
  intro p hp
  have hprime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hpz : (p : ℝ) < z :=
    ((actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd).2 p hp).trans_le hwz
  have hcop : Nat.Coprime p N :=
    (actualSmallRosserSupport_coprime_target N cap w hd).of_dvd_left
      (Nat.dvd_of_mem_primeFactors hp)
  have hmem : p ∈ sievePrimes N (Nat.ceil z) :=
    mem_sievePrimes.mpr
      ⟨Nat.lt_ceil.mpr hpz, hprime, hprime.coprime_iff_not_dvd.mp hcop⟩
  exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem

/-- Each rough modulus is squarefree and every prime factor comes from
the same actual rough carrier, so it divides the same complete sieve
product. No policy-specific support exponent is inferred. -/
theorem fixedRoughSupport_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z) := by
  apply (squarefree_dvd_iff_primeFactors_dvd
    (fixedRoughSupport_squarefree retainOdd N cap w z hd)).mpr
  intro p hp
  have hcarrier := fixedRoughSupport_primeFactors_mem retainOdd N cap w z hd hp
  have hmem : p ∈ sievePrimes N (Nat.ceil z) :=
    mem_sievePrimes.mpr
      ⟨Nat.lt_ceil.mpr (mem_roughPrimeUniverse_upper hcarrier),
        mem_roughPrimeUniverse_prime hcarrier, mem_roughPrimeUniverse_not_dvd hcarrier⟩
  exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem

/-- The displayed physical support divides the actual sieve product.
Small and rough factors are coprime at their strict/inclusive dividing
wall, so their product introduces no squared prime. Displayed zero
coefficients and modulus one are both included. -/
theorem actualSmallRoughModuli_dvd_sieveProduct_ceil
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (hwz : w ≤ z) {d : ℕ}
    (hd : d ∈ actualSmallRoughModuli retainOdd N cap w z) :
    d ∣ sieveProduct N (Nat.ceil z) := by
  rcases Finset.mem_image.mp hd with ⟨⟨a, c⟩, hac, rfl⟩
  have ha := (Finset.mem_product.mp hac).1
  have hc := (Finset.mem_product.mp hac).2
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hc)
  exact hcop.mul_dvd_of_dvd_of_dvd
    (actualSmallRosserSupport_dvd_sieveProduct_ceil N cap w z hwz ha)
    (fixedRoughSupport_dvd_sieveProduct_ceil retainOdd N cap w z hc)

/-- Specialization to the literal raw actual coefficient. The majorant
is supplied by its proved construction; all three analytic quantities
still use this identical function. No compiler or density certificate
for the complete manuscript policy is supplied by this specialization. -/
theorem RealB_cast_le_actualSmallRoughRho_main_add_errors
    {b T : ℝ} (N cap : ℕ) (retainOdd : List ℕ → Bool) (w z L : ℝ)
    (hb : b < 1) (hT : 0 ≤ T)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (RealB b N : ℝ) ≤
      ((realHalfProductSource b N T).card : ℝ) *
        physicalDensitySum (actualSmallRoughModuli retainOdd N cap w z)
          (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalCoprimeCorrection b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) +
      realPhysicalDistributionError b N T (actualSmallRoughModuli retainOdd N cap w z)
        (actualSmallRoughRho retainOdd N cap w z L) + (Nat.ceil z : ℝ) + (T + 1) := by
  exact RealB_cast_le_same_rho_main_add_errors N (Nat.ceil z)
    (actualSmallRoughModuli retainOdd N cap w z)
    (actualSmallRoughRho retainOdd N cap w z L) hb hT
    (actualSmallRoughRho_sieveProduct_majorant retainOdd N cap w z L hL hwL hwz hzcap)

end

end ImbalancedChen
