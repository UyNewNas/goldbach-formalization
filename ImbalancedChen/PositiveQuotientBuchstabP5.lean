import ImbalancedChen.ChenQuotientPrimeSource
import ImbalancedChen.QuotientChenInitialCounts
import MathlibNt.SieveTheory.LiLiuGoldbachBuchstab
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabCount

/-! Source-only, uncompiled. Positive finite Buchstab transitions for the
actual additive-prime quotient source. The pinned exact literalH identity
is reused, then adapted to the genuine quotient-source cardinalities.
Repeated prime factors are retained; no squarefree or Coprime b p premise
occurs. Analytic defect normalization and renewal soundness remain open. -/

namespace ImbalancedChen.P5PositiveQuotientBuchstab

noncomputable section

open Classical
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

def transitionPrimes (N : ℕ) (z0 z1 : ℝ) : Finset ℕ :=
  goldbachHalfOpenPrimes N z0 z1

theorem mem_transitionPrimes {N p : ℕ} {z0 z1 : ℝ} :
    p ∈ transitionPrimes N z0 z1 ↔
      Nat.Prime p ∧ ¬p ∣ N ∧ z0 ≤ (p : ℝ) ∧ (p : ℝ) < z1 := by
  simp only [transitionPrimes, goldbachHalfOpenPrimes, Finset.mem_filter,
    mem_siftingPrimes]
  tauto

/-- On actual quotient receivers the excluded-centre-prime mask is exact. -/
theorem survives_iff_rough {N b q : ℕ} (hq : q ∈ chenQuotientPrimeSource N b)
    (z : ℝ) : SurvivesSieve N z q ↔ ChenPrimeRough z q := by
  have hcop := (chenQuotientPrimeSource_data hq).2.2
  constructor
  · intro hs p hp hpd
    exact hs p hp hpd (hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hpd))
  · intro hr p hp hpd _
    exact hr p hp hpd

/-- Root literalH is precisely the actual sifted quotient count. -/
theorem literalH_root_eq_card (N b : ℕ) (z : ℝ) :
    literalH (chenQuotientPrimeSource N b) N 1 z =
      ((chenSiftedQuotientPrimeSource N b z).card : ℤ) := by
  have hs : (chenQuotientPrimeSource N b).filter (literalHPoint N 1 z) =
      chenSiftedQuotientPrimeSource N b z := by
    ext q
    simp only [chenSiftedQuotientPrimeSource, Finset.mem_filter,
      literalHPoint, one_dvd, true_and]
    constructor
    · rintro ⟨hq, hr⟩
      exact ⟨hq, (survives_iff_rough hq z).mp hr⟩
    · rintro ⟨hq, hr⟩
      exact ⟨hq, (survives_iff_rough hq z).mpr hr⟩
  unfold literalH
  rw [hs]

/-- Division by a new prime changes the physical multiplier by product,
even if that prime already divides b or its remaining cofactor. -/
theorem prime_quotient_step_iff (n b p : ℕ) (hp : Nat.Prime p) :
    (b ∣ n ∧ p ∣ n / b ∧ ChenPrimeRough (p : ℝ) (n / b)) ↔
      ChenQuotient (b * p) (p : ℝ) n := by
  constructor
  · rintro ⟨hbn, hpq, hr⟩
    refine ⟨(chen_quotient_divisibility_iff n b p).mp ⟨hbn, hpq⟩, ?_⟩
    have hdiv : (n / b) / p ∣ n / b := Nat.div_dvd_of_dvd hpq
    have hrough := hr.of_dvd hdiv
    simpa only [Nat.div_div_eq_div_mul] using hrough
  · rintro ⟨hbpn, hr⟩
    obtain ⟨hbn, hpq⟩ := (chen_quotient_divisibility_iff n b p).mpr hbpn
    have heq : n / b = p * (n / (b * p)) := by
      rw [← Nat.div_div_eq_div_mul n b p]
      exact (Nat.mul_div_cancel' hpq).symm
    refine ⟨hbn, hpq, ?_⟩
    rw [heq]
    exact LiLiuPrereqBuchstab.rough_mul_prime hp hr

/-- A child at cutoff p excludes primes STRICTLY BELOW p. It may retain p
again, exactly as required for prime squares and repeated factors of b. -/
theorem literalH_child_eq_card (N b p : ℕ) (hp : Nat.Prime p) :
    literalH (chenQuotientPrimeSource N b) N p (p : ℝ) =
      ((chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card : ℤ) := by
  have hs : (chenQuotientPrimeSource N b).filter (literalHPoint N p (p : ℝ)) =
      (chenQuotientPrimeSource N b).filter
        (fun q => p ∣ q ∧ ChenPrimeRough (p : ℝ) q) := by
    ext q
    simp only [Finset.mem_filter, literalHPoint]
    constructor
    · rintro ⟨hq, hpq, hr⟩
      exact ⟨hq, hpq, (survives_iff_rough hq p).mp hr⟩
    · rintro ⟨hq, hpq, hr⟩
      exact ⟨hq, hpq, (survives_iff_rough hq p).mpr hr⟩
  have hcard : ((chenQuotientPrimeSource N b).filter
      (fun q => p ∣ q ∧ ChenPrimeRough (p : ℝ) q)).card =
      (chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card := by
    rw [chenQuotientPrimeSource_filter_card, chenSiftedQuotientPrimeSource_card]
    apply congrArg Finset.card
    ext P
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP, hbn, hpq, hr⟩
      exact ⟨hP, (prime_quotient_step_iff (N - P) b p hp).mp ⟨hbn, hpq, hr⟩⟩
    · rintro ⟨hP, hchild⟩
      obtain ⟨hbn, hpq, hr⟩ := (prime_quotient_step_iff (N - P) b p hp).mpr hchild
      exact ⟨hP, hbn, hpq, hr⟩
  unfold literalH
  rw [hs]
  exact_mod_cast hcard

theorem conditioned_quotient_count_eq (N b p : ℕ) (hp : Nat.Prime p) :
    ((chenQuotientPrimeSource N b).filter
      (fun q => p ∣ q ∧ ChenPrimeRough (p : ℝ) q)).card =
      (chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card := by
  have h := literalH_child_eq_card N b p hp
  have hs : (chenQuotientPrimeSource N b).filter (literalHPoint N p (p : ℝ)) =
      (chenQuotientPrimeSource N b).filter (fun q => p ∣ q ∧ ChenPrimeRough (p : ℝ) q) := by
    ext q
    simp only [Finset.mem_filter, literalHPoint]
    constructor
    · rintro ⟨hq, hpq, hr⟩
      exact ⟨hq, hpq, (survives_iff_rough hq p).mp hr⟩
    · rintro ⟨hq, hpq, hr⟩
      exact ⟨hq, hpq, (survives_iff_rough hq p).mpr hr⟩
  unfold literalH at h
  rw [hs] at h
  exact_mod_cast h

/-- Explicit least-prime semantics of the child condition. -/
theorem prime_dvd_rough_iff_minFac (q p : ℕ) (hp : Nat.Prime p) :
    (p ∣ q ∧ ChenPrimeRough (p : ℝ) q) ↔ q.minFac = p := by
  constructor
  · rintro ⟨hpd, hr⟩
    have hq1 : q ≠ 1 := by
      intro hq
      exact hp.ne_one (Nat.dvd_one.mp (hq ▸ hpd))
    have hmin := (LiLiuPrereqBuchstab.rough_iff_minFac hq1).mp hr
    apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le hpd)
    exact_mod_cast hmin
  · intro hmin
    have hq1 : q ≠ 1 := by
      intro hq
      have hp1 : p = 1 := by simpa [hq] using hmin.symm
      exact hp.ne_one hp1
    refine ⟨?_, ?_⟩
    · rw [← hmin]
      exact Nat.minFac_dvd q
    · exact (LiLiuPrereqBuchstab.rough_iff_minFac hq1).mpr (by rw [hmin])

/-- The removed source is partitioned by its actual least prime, not by
arbitrary selected divisors; each receiver therefore occurs once. -/
theorem leastFactor_fibre_eq (N b p : ℕ) (z0 z1 : ℝ) (hp : Nat.Prime p)
    (hzp : z0 ≤ (p : ℝ)) (hpz : (p : ℝ) < z1) :
    ((chenSiftedQuotientPrimeSource N b z0 \ chenSiftedQuotientPrimeSource N b z1).filter
      (fun q => q.minFac = p)) =
      (chenQuotientPrimeSource N b).filter (fun q => p ∣ q ∧ ChenPrimeRough (p : ℝ) q) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hremoved, hmin⟩ := Finset.mem_filter.mp hq
    have hsource := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hremoved).1).1
    exact Finset.mem_filter.mpr
      ⟨hsource, (prime_dvd_rough_iff_minFac q p hp).mpr hmin⟩
  · intro hq
    obtain ⟨hsource, hpd, hr⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩,
      (prime_dvd_rough_iff_minFac q p hp).mp ⟨hpd, hr⟩⟩
    · exact Finset.mem_filter.mpr ⟨hsource, fun l hl hld => hzp.trans (hr l hl hld)⟩
    · intro hhigh
      have hcut := (Finset.mem_filter.mp hhigh).2 p hp hpd
      exact (not_le_of_gt hpz) hcut

theorem leastFactor_fibre_card (N b p : ℕ) (z0 z1 : ℝ) (hp : Nat.Prime p)
    (hzp : z0 ≤ (p : ℝ)) (hpz : (p : ℝ) < z1) :
    ((chenSiftedQuotientPrimeSource N b z0 \ chenSiftedQuotientPrimeSource N b z1).filter
      (fun q => q.minFac = p)).card =
        (chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card := by
  rw [leastFactor_fibre_eq N b p z0 z1 hp hzp hpz]
  exact conditioned_quotient_count_eq N b p hp

/-- Finite positive Buchstab difference for the genuine quotient source.
The proof reuses the pinned exact sifted identity, with full source adapters. -/
theorem sifted_count_difference (N b : ℕ) (z0 z1 : ℝ) (hzz : z0 ≤ z1) :
    ((chenSiftedQuotientPrimeSource N b z0).card : ℝ) -
        ((chenSiftedQuotientPrimeSource N b z1).card : ℝ) =
      ∑ p ∈ transitionPrimes N z0 z1,
        ((chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card : ℝ) := by
  have hbase := literalH_buchstab_interval (chenQuotientPrimeSource N b) N 1 hzz
  rw [literalH_root_eq_card, literalH_root_eq_card] at hbase
  have hsum :
      (∑ p ∈ (siftingPrimes N z1).filter (fun p : ℕ => z0 ≤ (p : ℝ)),
        literalH ((chenQuotientPrimeSource N b).filter (fun q => 1 ∣ q)) N p (p : ℝ)) =
      ∑ p ∈ (siftingPrimes N z1).filter (fun p : ℕ => z0 ≤ (p : ℝ)),
        ((chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card : ℤ) := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpPrime := (mem_siftingPrimes.mp (Finset.mem_filter.mp hp).1).1
    rw [literalH_filter_trivialCarrier, literalH_child_eq_card N b p hpPrime]
  rw [hsum] at hbase
  unfold transitionPrimes goldbachHalfOpenPrimes
  exact_mod_cast hbase

theorem sifted_count_buchstab (N b : ℕ) (z0 z1 : ℝ) (hzz : z0 ≤ z1) :
    ((chenSiftedQuotientPrimeSource N b z0).card : ℝ) =
      ((chenSiftedQuotientPrimeSource N b z1).card : ℝ) +
        ∑ p ∈ transitionPrimes N z0 z1,
          ((chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card : ℝ) := by
  have h := sifted_count_difference N b z0 z1 hzz
  linarith only [h]

theorem sifted_count_buchstab_nat (N b : ℕ) (z0 z1 : ℝ) (hzz : z0 ≤ z1) :
    (chenSiftedQuotientPrimeSource N b z0).card =
      (chenSiftedQuotientPrimeSource N b z1).card +
        ∑ p ∈ transitionPrimes N z0 z1,
          (chenSiftedQuotientPrimeSource N (b * p) (p : ℝ)).card := by
  exact_mod_cast sifted_count_buchstab N b z0 z1 hzz

/-- The marked family remains labelled: different B or tuple marks that
lead to the same child receiver remain distinct summands. -/
theorem marked_buchstab_identity {ι : Type*} (T : Finset ι) (sigma : ι → ℝ)
    (B : ι → ℕ) (N : ℕ) (z0 z1 : ℝ) (hzz : z0 ≤ z1) :
    (∑ t ∈ T, sigma t * ((chenSiftedQuotientPrimeSource N (B t) z0).card : ℝ)) =
      (∑ t ∈ T, sigma t * ((chenSiftedQuotientPrimeSource N (B t) z1).card : ℝ)) +
        ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T,
          sigma t * ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ) := by
  calc
    _ = ∑ t ∈ T, sigma t *
        (((chenSiftedQuotientPrimeSource N (B t) z1).card : ℝ) +
          ∑ p ∈ transitionPrimes N z0 z1,
            ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [sifted_count_buchstab N (B t) z0 z1 hzz]
    _ = (∑ t ∈ T, sigma t * ((chenSiftedQuotientPrimeSource N (B t) z1).card : ℝ)) +
        ∑ t ∈ T, ∑ p ∈ transitionPrimes N z0 z1,
          sigma t * ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ) := by
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ = _ := by rw [Finset.sum_comm]

theorem marked_child_mass_nonneg {ι : Type*} (T : Finset ι) (sigma : ι → ℝ)
    (B : ι → ℕ) (N : ℕ) (z0 z1 : ℝ) (hsigma : ∀ t ∈ T, 0 ≤ sigma t) :
    0 ≤ ∑ p ∈ transitionPrimes N z0 z1, ∑ t ∈ T,
      sigma t * ((chenSiftedQuotientPrimeSource N (B t * p) (p : ℝ)).card : ℝ) := by
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro t ht
  exact mul_nonneg (hsigma t ht) (Nat.cast_nonneg _)

theorem marked_count_antitone {ι : Type*} (T : Finset ι) (sigma : ι → ℝ)
    (B : ι → ℕ) (N : ℕ) (z0 z1 : ℝ) (hzz : z0 ≤ z1)
    (hsigma : ∀ t ∈ T, 0 ≤ sigma t) :
    (∑ t ∈ T, sigma t * ((chenSiftedQuotientPrimeSource N (B t) z1).card : ℝ)) ≤
      ∑ t ∈ T, sigma t * ((chenSiftedQuotientPrimeSource N (B t) z0).card : ℝ) := by
  have hid := marked_buchstab_identity T sigma B N z0 z1 hzz
  have hpos := marked_child_mass_nonneg T sigma B N z0 z1 hsigma
  linarith only [hid, hpos]

/-- The same total Q is retained on a child. The physical modulus is the
product b*p*d, including repeated prime factors, never an lcm. -/
theorem child_physical_level_iff (b p d : ℕ) (Q : ℝ) (hb : 0 < b) (hp : 0 < p) :
    (d : ℝ) ≤ Q / ((b * p : ℕ) : ℝ) ↔ ((b * p * d : ℕ) : ℝ) ≤ Q := by
  have hbp : (0 : ℝ) < (b * p : ℕ) := by exact_mod_cast Nat.mul_pos hb hp
  rw [le_div_iff₀ hbp]
  simp only [Nat.cast_mul]
  constructor <;> intro h <;> nlinarith only [h]

theorem child_divisibility_iff (n b p d : ℕ) :
    (b * p ∣ n ∧ d ∣ n / (b * p)) ↔ b * p * d ∣ n :=
  chen_quotient_divisibility_iff n (b * p) d

/-- Actual prime-AP/centre fibre for this same physical product. No gcd
between b,p,d and no squarefree receiver assumption is required. -/
theorem child_physical_fibre_card (N b p d : ℕ) :
    (((chenQuotientPrimeSource N (b * p)).filter (fun q => d ∣ q)).card : ℝ) =
      chenPrimeAPCount N N (b * p * d) - chenCentrePrimeAPCount N N (b * p * d) :=
  chenQuotientPrimeSource_divisibility_fibre_card N (b * p) d

/-- One Q is fixed before all family marks, selected primes and residual
moduli. This packages the actual child AP fibre with its complete physical
product cap, without changing the level on a descendant. -/
theorem marked_child_fibre_common_level {ι : Type*} (T : Finset ι) (B : ι → ℕ)
    (N : ℕ) (z0 z1 Q : ℝ) (hB : ∀ t ∈ T, 0 < B t) :
    ∀ t ∈ T, ∀ p ∈ transitionPrimes N z0 z1, ∀ d : ℕ,
      (d : ℝ) ≤ Q / ((B t * p : ℕ) : ℝ) →
      (((chenQuotientPrimeSource N (B t * p)).filter (fun q => d ∣ q)).card : ℝ) =
        chenPrimeAPCount N N (B t * p * d) - chenCentrePrimeAPCount N N (B t * p * d) ∧
      ((B t * p * d : ℕ) : ℝ) ≤ Q := by
  intro t ht p hp d hd
  have hpPrime := (mem_transitionPrimes.mp hp).1
  exact ⟨child_physical_fibre_card N (B t) p d,
    (child_physical_level_iff (B t) p d Q (hB t ht) hpPrime.pos).mp hd⟩

end

end ImbalancedChen.P5PositiveQuotientBuchstab
