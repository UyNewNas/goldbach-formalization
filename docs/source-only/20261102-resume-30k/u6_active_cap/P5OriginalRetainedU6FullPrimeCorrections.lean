import ImbalancedChen.P5OriginalRetainedU6RawSourcePayment
import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.ChenQuotientCentreBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original J coefficient has every prime factor below N^(59/250),
although its full modulus need not yet have a proved power cap. Its
squarefree support therefore lies in the actual sieve primorial. The
existing logarithmic primorial divisor mass pays the modulus-prime term.
For the centre-prime term, incidence pooling uses divisors of the positive
receiver N-P; the proved divisor subpower bound pays every rank.

Thus BOTH prime corrections of J's full same-E17572 raw count are paid
without an active-modulus cap, a policy adoption premise or an h6 bound.
The independent full support/class licence needed for PP remains OPEN.
-/

namespace ImbalancedChen.P5OriginalRetainedU6FullPrimeCorrections

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5OriginalRetainedU6RawSourcePayment
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

abbrev d : ℝ := 59 / 250

/-- Every prime of the full physical modulus is below the original
larger-prime band ceiling, including both marked primes and beta primes. -/
theorem physical_prime_upper {N : ℕ} (hN : (1 : ℝ) < N) {eta epsilon : ℝ}
    (policy : Policy) (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ} (hq : q ∈ support N eta epsilon policy) {ell : ℕ} (hell : ell ∈ q.primeFactors) :
    (ell : ℝ) < (N : ℝ) ^ d := by
  obtain ⟨⟨p, k⟩, hmark, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨hp, hk⟩ := Finset.mem_sigma.mp hmark
  have hbase := source_subset_sixth N eta hp
  obtain ⟨hcarrier, hbands⟩ := Finset.mem_filter.mp hbase
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hcarrier
  have hprime := (Nat.mem_primeFactors.mp hell).1
  have hdvd : ell ∣ (p.1 * p.2) * k := (Nat.mem_primeFactors.mp hell).2.1
  rcases hprime.dvd_mul.mp hdvd with hb | hkdiv
  · rcases hprime.dvd_mul.mp hb with h1 | h2
    · have heq : ell = p.1 :=
        (Nat.prime_dvd_prime_iff_eq hprime (mem_chenAdditivePrimeCarrier.mp hp1).2.1).mp h1
      rw [heq]
      exact hbands.2.1.trans_le (Real.rpow_le_rpow_of_exponent_le hN.le
        (show (19 / 125 : ℝ) ≤ d by norm_num [d]))
    · have heq : ell = p.2 :=
        (Nat.prime_dvd_prime_iff_eq hprime (mem_chenAdditivePrimeCarrier.mp hp2).2.1).mp h2
      rw [heq]
      exact hbands.2.2.2
  · have hsmall := divisors_strict_small policy hwz p hk
    exact (hsmall.2 ell (Nat.mem_primeFactors.mpr ⟨hprime, hkdiv, hsmall.1⟩)).trans_le
      (Real.rpow_le_rpow_of_exponent_le hN.le (show a ≤ d by norm_num [a, d]))

/-- This is actual prime support, not a polynomial bound on q. -/
theorem support_subset_sievePrimorial {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N) :
    support N eta epsilon policy ⊆ (sieveProduct N N).divisors := by
  intro q hq
  have hdata := support_primitive_squarefree policy hwz hq
  have hsub : q.primeFactors ⊆ sievePrimes N N := by
    intro ell hell
    have hp := (Nat.mem_primeFactors.mp hell).1
    have hdiv := (Nat.mem_primeFactors.mp hell).2.1
    have hpow : (N : ℝ) ^ d ≤ N := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN.le
        (show d ≤ 1 by norm_num [d])
    have hellN : ell < N := by
      exact_mod_cast (physical_prime_upper hN policy hwz hq hell).trans_le hpow
    exact mem_sievePrimes.mpr ⟨hellN, hp, hp.coprime_iff_not_dvd.mp (hdata.2.2.of_dvd_left hdiv)⟩
  have hdiv : q ∣ sieveProduct N N := by
    rw [← Nat.prod_primeFactors_of_squarefree hdata.2.1]
    exact Finset.prod_dvd_prod_of_subset _ _ id hsub
  exact Nat.mem_divisors.mpr ⟨hdiv, (sieveProduct_squarefree N N).ne_zero⟩

/-- A coarse count of the available prime labels is already sublinear;
it is independent of the number or size of retained rough divisors. -/
theorem modulusPrimeCount_le_power {N : ℕ} (hN : (1 : ℝ) < N)
    {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N)
    {q : ℕ} (hq : q ∈ support N eta epsilon policy) :
    chenPrimeDivisorCount N q ≤ 2 * (N : ℝ) ^ d := by
  have hpos := (support_primitive_squarefree policy hwz hq).1
  have hsub : q.primeFactors ⊆ Finset.range (Nat.ceil ((N : ℝ) ^ d)) := by
    intro ell hell
    apply Finset.mem_range.mpr
    exact_mod_cast (physical_prime_upper hN policy hwz hq hell).trans_le (Nat.le_ceil _)
  have hcard : (q.primeFactors.card : ℝ) ≤ (Nat.ceil ((N : ℝ) ^ d) : ℝ) := by
    exact_mod_cast (show q.primeFactors.card ≤ Nat.ceil ((N : ℝ) ^ d) by
      simpa only [Finset.card_range] using Finset.card_le_card hsub)
  have hpow : 1 ≤ (N : ℝ) ^ d :=
    Real.one_le_rpow hN.le (by norm_num [d])
  have hceil : (Nat.ceil ((N : ℝ) ^ d) : ℝ) ≤ 2 * (N : ℝ) ^ d := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg N) d)
    linarith
  exact (chenPrimeDivisorCount_le_primeFactors_card N hpos).trans (hcard.trans hceil)

def modulusCorrection (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  ∑ q ∈ support N eta epsilon policy,
    sigma N eta epsilon policy q * (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))

def centreCorrection (N : ℕ) (eta epsilon : ℝ) (policy : Policy) : ℝ :=
  ∑ q ∈ support N eta epsilon policy,
    sigma N eta epsilon policy q * chenCentrePrimeAPCount N N q

theorem primeCorrections_eq (N : ℕ) (eta epsilon : ℝ) (policy : Policy) :
    primeCorrections N eta epsilon policy =
      modulusCorrection N eta epsilon policy + centreCorrection N eta epsilon policy := rfl

/-- The entire modulus-prime correction, including arbitrary rough
ranks, has a uniform sublinear bound with no full-modulus cap input. -/
theorem exists_modulusCorrection_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (1 : ℝ) < N → Even N →
      ∀ eta epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 → ∀ policy : Policy,
        |modulusCorrection N eta epsilon policy| ≤
          (2 * C) * (N : ℝ) ^ d * Real.log (N : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := P4BPrimorialDivisorEnvelope.exists_sievePrimorial_divisor_mass_le_log
  refine ⟨C, hC, ?_⟩
  intro N hN hEven eta epsilon heps heps8 policy
  have hwz := (attachment_gates hN heps heps8).2.2
  have hmass' : (∑ q ∈ support N eta epsilon policy, 1 / (Nat.totient q : ℝ)) ≤
      C * Real.log (N : ℝ) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (support_subset_sievePrimorial hN policy hwz)
      (fun _ _ _ => by positivity)).trans
    have hNnat : 2 ≤ N := by exact_mod_cast hN
    exact hmass N N hEven (by exact_mod_cast hNnat)
  calc
    |modulusCorrection N eta epsilon policy| ≤
        ∑ q ∈ support N eta epsilon policy,
          |sigma N eta epsilon policy q * (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ support N eta epsilon policy,
        (2 * (N : ℝ) ^ d) * (1 / (Nat.totient q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul, abs_of_nonneg (div_nonneg (chenPrimeDivisorCount_nonneg N q) (Nat.cast_nonneg _))]
      have h := mul_le_mul_of_nonneg_right (sigma_abs_le_one policy hwz q)
        (div_nonneg (chenPrimeDivisorCount_nonneg N q) (Nat.cast_nonneg (Nat.totient q)))
      simp only [one_mul] at h
      exact h.trans (by
        simpa only [mul_one_div] using div_le_div_of_nonneg_right
          (modulusPrimeCount_le_power hN policy hwz hq) (Nat.cast_nonneg (Nat.totient q)))
    _ = (2 * (N : ℝ) ^ d) *
        (∑ q ∈ support N eta epsilon policy, 1 / (Nat.totient q : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * (N : ℝ) ^ d) * (C * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ = _ := by ring

/-- At a nonprime centre, every prime-centre incidence has a positive
receiver. Arbitrary physical moduli are then bounded by its divisors,
so no active-support exponent is necessary for this correction. -/
theorem centreCorrection_le_divisors {N : ℕ} (hNP : ¬Nat.Prime N)
    {eta epsilon : ℝ} (policy : Policy)
    (hwz : smallCutoff N epsilon ≤ P5CausalRhoQuotientBridge.cutoff N) :
    |centreCorrection N eta epsilon policy| ≤
      ∑ P ∈ chenCentrePrimeCarrier N, ((N - P).divisors.card : ℝ) := by
  have habs : |centreCorrection N eta epsilon policy| ≤
      chenSelectedCentreMass N (support N eta epsilon policy) id := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro q hq
    rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N q)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (sigma_abs_le_one policy hwz q)
      (chenCentrePrimeAPCount_nonneg N N q)
  apply habs.trans
  rw [chenSelectedCentreMass_eq_incidence]
  apply Finset.sum_le_sum
  intro P hP
  have hpos := chenCentrePrimeCarrier_sub_pos hNP hP
  have hsub : (support N eta epsilon policy).filter (fun q => id q ∣ N - P) ⊆
      (N - P).divisors := by
    intro q hq
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hq).2, hpos.ne'⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Existing proved divisor subpower estimates are applied to the
actual N-P receiver. The centre P=N is excluded by even N>=4. -/
theorem exists_centreCorrection_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 4 ≤ N → Even N →
      ∀ eta epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 → ∀ policy : Policy,
        |centreCorrection N eta epsilon policy| ≤
          (C / Real.log 2) * (N : ℝ) ^ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
  obtain ⟨C, hC, htau⟩ := Part3.PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
    (k := 2) (by norm_num) (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨C, hC, ?_⟩
  intro N hN hEven eta epsilon heps heps8 policy
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hwz := (attachment_gates hNr heps heps8).2.2
  have hNP := chen_not_prime_of_even_four_le hEven hN
  have hdiv (P : ℕ) (hP : P ∈ chenCentrePrimeCarrier N) :
      ((N - P).divisors.card : ℝ) ≤ C * (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hpos := chenCentrePrimeCarrier_sub_pos hNP hP
    have h := htau (N - P) hpos
    rw [fouvryTau_two] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg (N - P))
        (by exact_mod_cast Nat.sub_le N P) (by norm_num : (0 : ℝ) ≤ 1 / 2)) hC.le)
  calc
    |centreCorrection N eta epsilon policy| ≤
        ∑ P ∈ chenCentrePrimeCarrier N, ((N - P).divisors.card : ℝ) :=
      centreCorrection_le_divisors hNP policy hwz
    _ ≤ ∑ _P ∈ chenCentrePrimeCarrier N, C * (N : ℝ) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum hdiv
    _ = chenPrimeDivisorCount N N * (C * (N : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      rfl
    _ ≤ (Real.log (N : ℝ) / Real.log 2) * (C * (N : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N (by omega)) (by positivity)
    _ = _ := by ring

/-- One threshold pays both literal corrections for the full original
coefficient, preceding every eta, precision and pair-dependent policy. -/
theorem eventually_full_primeCorrections_paid (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ eta epsilon : ℝ, 0 < epsilon → epsilon < 1 / 8 →
      ∀ policy : Policy, |primeCorrections N eta epsilon policy| ≤ delta * singularNormalization N := by
  obtain ⟨C, hC, hmod⟩ := exists_modulusCorrection_bound
  obtain ⟨D, hD, hcentre⟩ := exists_centreCorrection_bound
  filter_upwards [eventually_powerLog_le_singularNormalization (2 * C) d 1
      (by norm_num [d]) (delta / 2) (half_pos hdelta),
    eventually_powerLog_le_singularNormalization (D / Real.log 2) (1 / 2) 1
      (by norm_num) (delta / 2) (half_pos hdelta),
    eventually_ge_atTop (4 : ℕ)] with N hmodPaid hcentrePaid hN
  intro hEven eta epsilon heps heps8 policy
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hm := (hmod N hNr hEven eta epsilon heps heps8 policy).trans
    (by simpa only [pow_one] using hmodPaid)
  have hc := (hcentre N hN hEven eta epsilon heps heps8 policy).trans
    (by simpa only [pow_one] using hcentrePaid)
  rw [primeCorrections_eq]
  exact (abs_add _ _).trans (by linarith only [hm, hc])

/-- Full same-E17572 raw count after the two prime corrections are
paid. The exact raw density and signed physical PP are unchanged.
No support cap, H248, raw-main endpoint or h6 estimate is a premise. -/
theorem exists_uniform_raw_count_primeCorrections_paid
    (delta kappa epsilonMax : ℝ) (hdelta : 0 < delta) (hkappa : 0 < kappa)
    (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧ epsilon < epsilonMax ∧
      ∃ N0 : ℕ, 4 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        ∀ eta : ℝ, 0 ≤ eta → ∀ policy : Policy,
          rawMain N eta policy - delta * primeScale N + signedPP N eta epsilon policy -
            kappa * singularNormalization N ≤ currentChenUpsilon6 N (actualMask N) := by
  obtain ⟨epsilon, heps, heps8, hepsMax, N1, _hN1, hraw⟩ :=
    exists_uniform_full_raw_count delta epsilonMax hdelta hepsilonMax
  obtain ⟨N2, hN2⟩ := eventually_atTop.mp (eventually_full_primeCorrections_paid kappa hkappa)
  refine ⟨epsilon, heps, heps8, hepsMax, max 4 (max N1 N2), le_max_left _ _, ?_⟩
  intro N hN hEven eta heta policy
  have hlarge : max N1 N2 ≤ N := (le_max_right _ _).trans hN
  have hcount := hraw N ((le_max_left _ _).trans hlarge) hEven eta heta policy
  have hpaid := hN2 N ((le_max_right _ _).trans hlarge) hEven eta epsilon heps heps8 policy
  have hupper := (le_abs_self (primeCorrections N eta epsilon policy)).trans hpaid
  linarith only [hcount, hupper]

end
end ImbalancedChen.P5OriginalRetainedU6FullPrimeCorrections
