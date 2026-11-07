import ImbalancedChen.ActualOptimizedSieveBound
import ImbalancedChen.RealHalfProductSource

/-!
# Rational minorants for the arbitrary-real bad source

The finite upper-sieve implementation is parameterized by a rational exponent
`num / den`, while the current manuscript theorem is stated for every real
`b`.  This file gives the exact monotonic bridge between the two interfaces.

If `num / den ≤ b`, then the strict bad region at exponent `b` is contained in
the rational bad region: for a prime `q`, monotonicity of `q ^ x` gives
`q ^ (num / den) ≤ q ^ b < r`.  Consequently the literal prime-partner filter
for the real source is bounded by the already constructed rational sifted
source, with the same explicit small-partner correction `z`.

These are finite statements.  They neither assume a distribution theorem nor
replace the finite Selberg normalizer by an asymptotic constant.
-/

namespace ImbalancedChen

noncomputable section

/-- The ordered bad region is antitone in the exponent. -/
theorem realOrderedBadReceiver_antitone {a b : ℝ} {m : ℕ} (hab : a ≤ b) :
    RealOrderedBadReceiver b m → RealOrderedBadReceiver a m := by
  rintro ⟨r, q, hr, hq, hm, hrq, hpow⟩
  refine ⟨r, q, hr, hq, hm, hrq, ?_⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_le
  exact (Real.rpow_le_rpow_of_exponent_le hq1 hab).trans_lt hpow

/-- The arbitrary-real half-product source is antitone in its exponent. -/
theorem realHalfProductSource_antitone {a b T : ℝ} {N : ℕ} (hab : a ≤ b) :
    realHalfProductSource b N T ⊆ realHalfProductSource a N T := by
  intro m hm
  rcases mem_realHalfProductSource.mp hm with ⟨hmN, hT, hbad⟩
  exact mem_realHalfProductSource.mpr
    ⟨hmN, hT, realOrderedBadReceiver_antitone hab hbad⟩

/-- At a positive-denominator rational exponent, the real source is literally
the existing natural-power source.  Strict endpoints and prime squares are
unchanged. -/
theorem realHalfProductSource_rat (num den N : ℕ) (T : ℝ) (hden : 0 < den) :
    realHalfProductSource ((num : ℝ) / (den : ℝ)) N T =
      halfProductSource num den N T := by
  classical
  ext m
  rw [mem_realHalfProductSource,
    mem_halfProductSource_iff_ordered_real_factors hden]
  rfl

/-- A rational minorant contains the real source even after imposing the
literal strict additive endpoint and prime-partner condition. -/
theorem realHalfProductSource_primePartner_filter_subset_rat
    {b T : ℝ} {num den N : ℕ} (hden : 0 < den)
    (hrat : (num : ℝ) / (den : ℝ) ≤ b) :
    (realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m)) ⊆
      (halfProductSource num den N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m)) := by
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hsource, hp⟩
  refine Finset.mem_filter.mpr ⟨?_, hp⟩
  rw [← realHalfProductSource_rat num den N T hden]
  exact realHalfProductSource_antitone hrat hsource

/-- Exact finite prime-partner bridge to the rational sifted source.  The
small prime partner is retained as the explicit correction `z`. -/
theorem realHalfProductSource_primePartner_card_le_sifted_rat_add_cap
    {b T : ℝ} {num den N z : ℕ} (hden : 0 < den)
    (hrat : (num : ℝ) / (den : ℝ) ≤ b) :
    ((realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card ≤
      (siftedHalfProductSource num den N T z).card + z := by
  calc
    ((realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card ≤
        ((halfProductSource num den N T).filter
          (fun m => m < N ∧ Nat.Prime (N - m))).card :=
      Finset.card_le_card
        (realHalfProductSource_primePartner_filter_subset_rat hden hrat)
    _ = (retainedBadReceiversReal num den N T).card := by
      rw [retainedBadReceiversReal_eq_halfProductSource_filter]
    _ ≤ (siftedHalfProductSource num den N T z).card + z :=
      retainedBadReceiversReal_card_le_sifted_add_cap num den N z T

/-- Composition with the proved optimized finite Selberg inequality.  Its
only analytic premise remains visible as the unweighted primitive-residue
discrepancy estimate; no final sieve coefficient is assumed here. -/
theorem realHalfProductSource_primePartner_cast_le_optimized_of_rat_minorant
    {b T : ℝ} (num den N z : ℕ) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hrat : (num : ℝ) / (den : ℝ) ≤ b)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (L A : ℕ) (hL : 1 ≤ L) (hlevel : L * L ≤ N)
    (hN1 : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hdistribution :
      (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ (2 * A + 16)) :
    (((realHalfProductSource b N T).filter
        (fun m => m < N ∧ Nat.Prime (N - m))).card : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) /
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L,
          ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)) +
      Real.sqrt (3 * (8 : ℝ) ^ 16 * C * (N : ℝ) ^ 2 /
        (Real.log (N : ℝ)) ^ (2 * A)) + (z : ℝ) := by
  have hfinite :
      (((realHalfProductSource b N T).filter
          (fun m => m < N ∧ Nat.Prime (N - m))).card : ℝ) ≤
        ((siftedHalfProductSource num den N T z).card : ℝ) + (z : ℝ) := by
    exact_mod_cast
      realHalfProductSource_primePartner_card_le_sifted_rat_add_cap hden hrat
  have hsieve := siftedHalfProductSource_card_le_optimized_of_unweighted_logBound
    num den N T z hN hnum hden hT hcap L A hL hlevel hN1 hlog C hC hdistribution
  exact hfinite.trans (add_le_add hsieve le_rfl)

/-- The same composition for the complete arbitrary-real bad count.  Besides
the sieve's explicit `z` correction, this keeps the exact real cutoff loss
`T + 1`; neither term is absorbed into asymptotic notation. -/
theorem RealB_cast_le_optimized_of_rat_minorant
    {b T : ℝ} (num den N z : ℕ) (hb : b < 1) (hN : Even N)
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hrat : (num : ℝ) / (den : ℝ) ≤ b)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (L A : ℕ) (hL : 1 ≤ L) (hlevel : L * L ≤ N)
    (hN1 : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hdistribution :
      (∑ d ∈ Finset.Icc 1 (L * L) with Nat.Coprime d N,
        |halfProductCongruenceMass num den N T d -
          halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
        C * (N : ℝ) / (Real.log (N : ℝ)) ^ (2 * A + 16)) :
    (RealB b N : ℝ) ≤
      ((halfProductSource num den N T).card : ℝ) /
        (∑ d ∈ (sieveProduct N z).divisors with d ≤ L,
          ∏ p ∈ d.primeFactors, 1 / ((p : ℝ) - 2)) +
      Real.sqrt (3 * (8 : ℝ) ^ 16 * C * (N : ℝ) ^ 2 /
        (Real.log (N : ℝ)) ^ (2 * A)) + (z : ℝ) + (T + 1) := by
  rw [RealB_eq_realHalfProductSource_filter_card_add_small hb N T]
  push_cast
  exact add_le_add
    (realHalfProductSource_primePartner_cast_le_optimized_of_rat_minorant
      num den N z hN hnum hden hT hrat hcap L A hL hlevel hN1 hlog C hC
        hdistribution)
    (smallRealBadReceivers_cast_card_lt hT.le).le

/-- The current real bad count is antitone in the exponent, below the endpoint
where it agrees with the ordered bad region. -/
theorem RealB_antitone {a b : ℝ} (ha : a < 1) (hb : b < 1)
    (hab : a ≤ b) (N : ℕ) : RealB b N ≤ RealB a N := by
  rw [RealB_eq_realOrderedBadPrimes_card hb,
    RealB_eq_realOrderedBadPrimes_card ha]
  apply Finset.card_le_card
  intro p hp
  rcases mem_realOrderedBadPrimes.mp hp with ⟨hpN, hpprime, hbad⟩
  exact mem_realOrderedBadPrimes.mpr
    ⟨hpN, hpprime, realOrderedBadReceiver_antitone hab hbad⟩

/-- Any rational exponent below `b` gives an upper bound for the arbitrary-real
bad count by the already formalized rational count. -/
theorem RealB_le_B_of_rat_minorant {b : ℝ} {num den N : ℕ}
    (hb : b < 1) (hden : 0 < den) (hnumden : num < den)
    (hrat : (num : ℝ) / (den : ℝ) ≤ b) :
    RealB b N ≤ B num den N := by
  have hdenR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have hnumdenR : (num : ℝ) < (den : ℝ) := by exact_mod_cast hnumden
  have hrat1 : (num : ℝ) / (den : ℝ) < 1 :=
    (div_lt_one hdenR).2 hnumdenR
  rw [B_eq_RealB hden]
  exact RealB_antitone hrat1 hb hrat N

end

end ImbalancedChen
