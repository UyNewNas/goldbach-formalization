import ImbalancedChen.ActualUpperCountingInputs
import ImbalancedChen.RealHalfProductSieveBridge

/-!
# Exact real-cutoff rounding and a finite manuscript buffer gate

SOURCE ONLY / YELLOW / UNCOMPILED. No numerical or analytic input.

The strict real prime cap is represented by `ceil z`, including at integral
endpoints. In contrast, a closed real upper bound on a natural is represented
by the strict natural cap `floor R + 1`. These two different endpoint rules
give a buffer gate weaker than `(ceil z : ℝ) ≤ R`.

The new manuscript corollary works at the weak exponent wall, for every
`N ≥ 1`; it does not invoke `eventually_manuscript_sieve_gate` or an exponent
gap. The universal buffer equivalence is about all naturals, so no claim of
necessity for the smaller target-excluded prime carrier is intended.
-/

namespace ImbalancedChen.P4BCutoffRounding

noncomputable section
open Filter Topology

/-- Strict real upper endpoints have the exact natural ceiling semantics.
No positivity or nonintegrality assumption is needed. -/
theorem strict_real_iff_lt_ceil (p : ℕ) (z : ℝ) :
    (p : ℝ) < z ↔ p < Nat.ceil z := by
  exact Nat.lt_ceil.symm

/-- The same dictionary holds simultaneously for all actual prime factors,
including the empty prime-factor sets of zero and one. -/
theorem primeFactors_strict_real_iff_lt_ceil (d : ℕ) (z : ℝ) :
    (∀ p ∈ d.primeFactors, (p : ℝ) < z) ↔
      ∀ p ∈ d.primeFactors, p < Nat.ceil z := by
  constructor
  · intro h p hp
    exact Nat.lt_ceil.mpr (h p hp)
  · intro h p hp
    exact Nat.lt_ceil.mp (h p hp)

/-- Exact membership in the actual sieve product carrier. -/
theorem mem_sievePrimes_ceil_iff (N p : ℕ) (z : ℝ) :
    p ∈ sievePrimes N (Nat.ceil z) ↔
      (p : ℝ) < z ∧ Nat.Prime p ∧ ¬p ∣ N := by
  rw [mem_sievePrimes, Nat.lt_ceil]

/-- For a prime, the actual product has precisely the strict real cutoff
and the target-prime exclusion. -/
theorem prime_dvd_sieveProduct_ceil_iff {N p : ℕ} {z : ℝ}
    (hp : Nat.Prime p) :
    p ∣ sieveProduct N (Nat.ceil z) ↔ (p : ℝ) < z ∧ ¬p ∣ N := by
  constructor
  · intro hd
    have hmem := (mem_sievePrimes_ceil_iff N p z).mp
      (prime_mem_sievePrimes_of_dvd hp hd)
    exact ⟨hmem.1, hmem.2.2⟩
  · rintro ⟨hpz, hpN⟩
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q)
      ((mem_sievePrimes_ceil_iff N p z).mpr ⟨hpz, hp, hpN⟩)

/-- At an integral prime wall, the endpoint prime is excluded. -/
theorem prime_not_dvd_sieveProduct_integral_endpoint {N p : ℕ}
    (hp : Nat.Prime p) :
    ¬p ∣ sieveProduct N (Nat.ceil (p : ℝ)) := by
  intro hd
  exact (lt_irrefl (p : ℝ)) ((prime_dvd_sieveProduct_ceil_iff hp).mp hd).1

/-- Replacing an integral ceiling by floor-plus-one would add the endpoint
prime whenever it does not divide the target. -/
theorem prime_dvd_sieveProduct_floor_successor_endpoint {N p : ℕ}
    (hp : Nat.Prime p) (hpN : ¬p ∣ N) :
    p ∣ sieveProduct N (Nat.floor (p : ℝ) + 1) := by
  have hmem : p ∈ sievePrimes N (Nat.floor (p : ℝ) + 1) := by
    apply mem_sievePrimes.mpr
    exact ⟨by simp, hp, hpN⟩
  exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem

/-- At a genuinely nonintegral nonnegative cutoff, the two natural caps
coincide. The preceding endpoint theorems explain why this needs a premise. -/
theorem ceil_eq_floor_add_one_of_nonintegral {z : ℝ} (hz : 0 ≤ z)
    (hwall : z ≠ (Nat.floor z : ℝ)) :
    Nat.ceil z = Nat.floor z + 1 := by
  have hstrict : (Nat.floor z : ℝ) < z := by
    by_contra h
    exact hwall (le_antisymm (le_of_not_gt h) (Nat.floor_le hz))
  have hlow : Nat.floor z < Nat.ceil z := Nat.lt_ceil.mpr hstrict
  have hhigh := Nat.ceil_le_floor_add_one z
  omega

/-- A closed real upper bound is the strict natural floor-successor cap. -/
theorem closed_real_iff_lt_floor_add_one (p : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (p : ℝ) ≤ R ↔ p < Nat.floor R + 1 := by
  constructor
  · intro hp
    have h := Nat.le_floor hp
    omega
  · intro hp
    have h : p ≤ Nat.floor R := by omega
    exact (Nat.le_floor_iff hR).mp h

/-- Strict real lower endpoints use the inclusive natural floor-successor
bound. In particular an integral lower wall excludes its endpoint. -/
theorem strict_lower_real_iff_floor_add_one_le (p : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    R < (p : ℝ) ↔ Nat.floor R + 1 ≤ p := by
  constructor
  · intro hp
    have hnot : ¬p < Nat.floor R + 1 := by
      intro h
      exact (not_lt_of_ge ((closed_real_iff_lt_floor_add_one p hR).mpr h)) hp
    omega
  · intro hp
    by_contra h
    have hclosed : (p : ℝ) ≤ R := le_of_not_gt h
    have hlt := (closed_real_iff_lt_floor_add_one p hR).mp hclosed
    omega

/-- The actual arbitrary-real bad source supplies the natural lower buffer
for each prime factor, including repeated factors of a prime square. -/
theorem source_primeFactors_floor_buffer
    {b T : ℝ} {N m : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hm : m ∈ realHalfProductSource b N T) :
    ∀ p ∈ m.primeFactors, Nat.floor (T ^ (b / (1 + b))) + 1 ≤ p := by
  intro p hp
  apply (strict_lower_real_iff_floor_add_one_le p
    (Real.rpow_nonneg hT.le (b / (1 + b)))).mp
  exact realHalfProductSource_prime_divisor_rough hb hT hm
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- Exact universal natural buffer dictionary. This is weaker than asking
the real cast of `ceil z` to lie below `R`: its last possible natural prime
is `ceil z - 1`, and source prime factors will be strictly above `R`. -/
theorem ceil_le_floor_add_one_iff {z R : ℝ} (hR : 0 ≤ R) :
    Nat.ceil z ≤ Nat.floor R + 1 ↔
      ∀ p : ℕ, p < Nat.ceil z → (p : ℝ) ≤ R := by
  constructor
  · intro hcap p hp
    apply (closed_real_iff_lt_floor_add_one p hR).mpr
    omega
  · intro h
    by_contra hcap
    have hp : Nat.floor R + 1 < Nat.ceil z := by omega
    have hbad : Nat.floor R + 1 ≤ Nat.floor R := Nat.le_floor (h _ hp)
    omega

/-- A weak real cutoff inequality already pays the exact natural buffer;
there is no rounding-unit loss to absorb. -/
theorem ceil_le_floor_add_one_of_le {z R : ℝ}
    (hR : 0 ≤ R) (hzR : z ≤ R) :
    Nat.ceil z ≤ Nat.floor R + 1 := by
  apply (ceil_le_floor_add_one_iff hR).mpr
  intro p hp
  exact (Nat.lt_ceil.mp hp).le.trans hzR

/-- Source coprimality under the exact natural buffer. Prime squares in the
source are included by the existing prime-divisor roughness theorem. -/
theorem source_coprime_of_buffer
    {b T z : ℝ} {N m d : ℕ} (hb : 0 < b) (hT : 0 < T)
    (hbuffer : Nat.ceil z ≤ Nat.floor (T ^ (b / (1 + b))) + 1)
    (hm : m ∈ realHalfProductSource b N T)
    (hd : d ∣ sieveProduct N (Nat.ceil z)) :
    Nat.Coprime m d := by
  have hproduct : Nat.Coprime m (sieveProduct N (Nat.ceil z)) := by
    classical
    unfold sieveProduct
    apply Nat.coprime_prod_right_iff.mpr
    intro p hp
    obtain ⟨hpcap, hprime, _hpN⟩ := mem_sievePrimes.mp hp
    apply (hprime.coprime_iff_not_dvd.mpr ?_).symm
    intro hpm
    have hrough := realHalfProductSource_prime_divisor_rough hb hT hm hprime hpm
    have hpupper := (ceil_le_floor_add_one_iff
      (Real.rpow_nonneg hT.le (b / (1 + b)))).mp hbuffer p hpcap
    exact (not_lt_of_ge hpupper) hrough
  exact hproduct.of_dvd_right hd

/-- The same physical correction vanishes for any signed coefficients whose
active moduli divide the actual product, under the exact buffer. -/
theorem physicalCoprimeCorrection_eq_zero_of_buffer
    {b T z : ℝ} {N : ℕ} (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hb : 0 < b) (hT : 0 < T)
    (hbuffer : Nat.ceil z ≤ Nat.floor (T ^ (b / (1 + b))) + 1)
    (hsupport : ∀ d ∈ Q, rho d ≠ 0 → d ∣ sieveProduct N (Nat.ceil z)) :
    realPhysicalCoprimeCorrection b N T Q rho = 0 := by
  classical
  unfold realPhysicalCoprimeCorrection
  apply Finset.sum_eq_zero
  intro d hd
  by_cases hrho : rho d = 0
  · simp only [hrho, zero_mul]
  · have hfilter : (realHalfProductSource b N T).filter
        (fun m : ℕ => Nat.Coprime m d) = realHalfProductSource b N T := by
      apply Finset.filter_eq_self.mpr
      intro m hm
      exact source_coprime_of_buffer hb hT hbuffer hm (hsupport d hd hrho)
    rw [realHalfProductCoprimeMass, hfilter]
    simp

/-- The literal manuscript cutoff clears the exact buffer at the weak
exponent wall, including equality, already for every `N ≥ 1`. -/
theorem manuscript_buffer_gate
    {b kappa theta : ℝ} (hb : 0 < b)
    (hwall : theta ≤ (1 - kappa) * (b / (1 + b)))
    {N : ℕ} (hN : 1 ≤ N) :
    0 < manuscriptHalfProductCutoff kappa N ∧
      Nat.ceil ((N : ℝ) ^ theta) ≤
        Nat.floor ((manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b))) + 1 := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have hpow : 0 < (N : ℝ) ^ (1 - kappa) := Real.rpow_pos_of_pos hNpos _
  have hT : 0 < manuscriptHalfProductCutoff kappa N := by
    change 0 < 2 * (N : ℝ) ^ (1 - kappa)
    positivity
  have halpha : 0 ≤ b / (1 + b) := div_nonneg hb.le (by linarith)
  refine ⟨hT, ceil_le_floor_add_one_of_le (Real.rpow_nonneg hT.le _) ?_⟩
  calc
    (N : ℝ) ^ theta ≤ (N : ℝ) ^ ((1 - kappa) * (b / (1 + b))) :=
      Real.rpow_le_rpow_of_exponent_le hNreal hwall
    _ = ((N : ℝ) ^ (1 - kappa)) ^ (b / (1 + b)) :=
      Real.rpow_mul hNpos.le _ _
    _ ≤ (manuscriptHalfProductCutoff kappa N) ^ (b / (1 + b)) := by
      apply Real.rpow_le_rpow hpow.le _ halpha
      change (N : ℝ) ^ (1 - kappa) ≤ 2 * (N : ℝ) ^ (1 - kappa)
      linarith

/-- Finite zero correction for the literal attached coefficient, even at
the weak wall. Policy and enumeration cap are arbitrary; no cap-coverage,
density, distribution or nonzero-coefficient assertion is assumed. -/
theorem attached_coprimeCorrection_eq_zero_of_weak_wall
    {b kappa nu r epsilon : ℝ} (hb : 0 < b) (hnu : 0 ≤ nu)
    (hepsilonR : epsilon ^ 2 ≤ r)
    (hwall : nu * r ≤ (1 - kappa) * (b / (1 + b)))
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    {N : ℕ} (hN : 1 ≤ N) :
    realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
      (attachedUpperModuli nu r epsilon retain cap N)
      (attachedUpperCoefficient nu r epsilon retain cap N) = 0 := by
  obtain ⟨hT, hbuffer⟩ := manuscript_buffer_gate hb hwall hN
  apply physicalCoprimeCorrection_eq_zero_of_buffer _ _ hb hT hbuffer
  intro d hd _hactive
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact actualSmallRoughModuli_dvd_sieveProduct_ceil (retain N) N (cap N) _ _
    (Real.rpow_le_rpow_of_exponent_le hNreal
      (mul_le_mul_of_nonneg_left hepsilonR hnu)) hd

/-- Eventual form for the existing assembly API, with the weak wall kept. -/
theorem eventually_attached_coprimeCorrection_eq_zero_of_weak_wall
    {b kappa nu r epsilon : ℝ} (hb : 0 < b) (hnu : 0 ≤ nu)
    (hepsilonR : epsilon ^ 2 ≤ r)
    (hwall : nu * r ≤ (1 - kappa) * (b / (1 + b)))
    (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ) :
    ∀ᶠ N : ℕ in atTop,
      realPhysicalCoprimeCorrection b N (manuscriptHalfProductCutoff kappa N)
        (attachedUpperModuli nu r epsilon retain cap N)
        (attachedUpperCoefficient nu r epsilon retain cap N) = 0 := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact attached_coprimeCorrection_eq_zero_of_weak_wall
    hb hnu hepsilonR hwall retain cap hN

end
end ImbalancedChen.P4BCutoffRounding
