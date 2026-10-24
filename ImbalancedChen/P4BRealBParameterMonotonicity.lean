import ImbalancedChen.RealHalfProductSieveBridge

/-!
# P4B: exact parameter bands and strict power endpoints

SOURCE ONLY / YELLOW / UNCOMPILED.

The imported bridge already supplies `realOrderedBadReceiver_antitone`,
`realHalfProductSource_antitone`, and `RealB_antitone`.  We do not duplicate
those declarations.  This extension identifies exactly what is removed when
the exponent increases: the ordered band `q ^ b < r <= q ^ c`.
In particular equality at the larger exponent is removed, while equality at
the literal product cutoff is retained.  Factor uniqueness prevents another
ordered factor witness from reintroducing an excluded endpoint.

All assertions are finite identities.  No analytic estimate, numerical replay,
or final-count comparison is assumed.
-/

namespace ImbalancedChen
namespace P4BRealBParameterMonotonicity

noncomputable section

/-- A fixed ordered prime factorization determines the strict bad condition,
including repeated factors. -/
theorem orderedBad_iff_fixedFactors {b : ℝ} {m r q : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hm : m = r * q)
    (hrq : r ≤ q) :
    RealOrderedBadReceiver b m ↔ (q : ℝ) ^ b < (r : ℝ) := by
  constructor
  · rintro ⟨s, t, hs, ht, hmst, hst, hpow⟩
    obtain ⟨hrs, hqt⟩ := realOrderedBadReceiver_factors_unique
      hr hq hs ht hm hmst hrq hst
    simpa only [← hrs, ← hqt] using hpow
  · intro hpow
    exact ⟨r, q, hr, hq, hm, hrq, hpow⟩

/-- The actual finite source at fixed factors has the original inclusive
product cutoff and strict power boundary. -/
theorem mem_source_iff_fixedFactors {b T : ℝ} {N m r q : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hm : m = r * q)
    (hrq : r ≤ q) :
    m ∈ realHalfProductSource b N T ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧ (q : ℝ) ^ b < (r : ℝ) := by
  rw [mem_realHalfProductSource, orderedBad_iff_fixedFactors hr hq hm hrq]

/-- The exact source difference is open at the smaller power boundary and
closed at the larger one.  This identity needs no ordering hypothesis on the
exponents; if `c ≤ b`, its right side is automatically empty. -/
theorem mem_source_sdiff_iff {b c T : ℝ} {N m : ℕ} :
    m ∈ realHalfProductSource b N T \ realHalfProductSource c N T ↔
      m ≤ N ∧ T ≤ (m : ℝ) ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ m = r * q ∧ r ≤ q ∧
          (q : ℝ) ^ b < (r : ℝ) ∧ (r : ℝ) ≤ (q : ℝ) ^ c := by
  classical
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hmb, hmc⟩
    rcases mem_realHalfProductSource.mp hmb with
      ⟨hN, hT, r, q, hr, hq, hm, hrq, hb⟩
    refine ⟨hN, hT, r, q, hr, hq, hm, hrq, hb, ?_⟩
    apply le_of_not_gt
    intro hc
    exact hmc (mem_realHalfProductSource.mpr
      ⟨hN, hT, r, q, hr, hq, hm, hrq, hc⟩)
  · rintro ⟨hN, hT, r, q, hr, hq, hm, hrq, hb, hc⟩
    refine ⟨mem_realHalfProductSource.mpr
      ⟨hN, hT, r, q, hr, hq, hm, hrq, hb⟩, ?_⟩
    intro hmc
    have hpow := (orderedBad_iff_fixedFactors hr hq hm hrq).mp
      (mem_realHalfProductSource.mp hmc).2.2
    exact (not_lt_of_ge hc) hpow

/-- Equality in the strict power condition excludes the receiver from the
actual source, independently of the product cutoff. -/
theorem power_endpoint_not_mem_source {c T : ℝ} {N m r q : ℕ}
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hm : m = r * q)
    (hrq : r ≤ q) (heq : (q : ℝ) ^ c = (r : ℝ)) :
    m ∉ realHalfProductSource c N T := by
  intro hmem
  have hpow := (mem_source_iff_fixedFactors hr hq hm hrq).mp hmem
  have hirr : (r : ℝ) < (r : ℝ) := by
    simpa only [heq] using hpow.2.2
  exact (lt_irrefl (r : ℝ)) hirr

/-- A point on the larger-exponent boundary is still present at every smaller
exponent, provided its original product bounds hold. -/
theorem power_endpoint_mem_source_sdiff {b c T : ℝ} {N m r q : ℕ}
    (hbc : b < c) (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hm : m = r * q) (hrq : r ≤ q) (hN : m ≤ N) (hT : T ≤ (m : ℝ))
    (heq : (q : ℝ) ^ c = (r : ℝ)) :
    m ∈ realHalfProductSource b N T \ realHalfProductSource c N T := by
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hb : (q : ℝ) ^ b < (r : ℝ) :=
    (Real.rpow_lt_rpow_of_exponent_lt hqR hbc).trans_eq heq
  exact mem_source_sdiff_iff.mpr
    ⟨hN, hT, r, q, hr, hq, hm, hrq, hb, le_of_eq heq.symm⟩

/-- At the literal cutoff `T = m`, the receiver is retained at `b` but removed
at `c` when its power equals the larger-exponent boundary. -/
theorem power_endpoint_at_equal_product_cutoff {b c : ℝ} {N m r q : ℕ}
    (hbc : b < c) (hr : Nat.Prime r) (hq : Nat.Prime q)
    (hm : m = r * q) (hrq : r ≤ q) (hN : m ≤ N)
    (heq : (q : ℝ) ^ c = (r : ℝ)) :
    m ∈ realHalfProductSource b N (m : ℝ) \
      realHalfProductSource c N (m : ℝ) := by
  exact power_endpoint_mem_source_sdiff hbc hr hq hm hrq hN le_rfl heq

/-- Additive primes lost from the actual ordered bad set when the parameter
changes from `b` to `c`; the additive prime remains the sole count index. -/
def parameterBandRealBadPrimes (b c : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (realOrderedBadPrimes b N).filter
    (fun p => ¬ RealOrderedBadReceiver c (N - p))

/-- The exact lost additive-prime set has the same open/closed factor band as
the half-product source and preserves the strict additive endpoint. -/
theorem mem_parameterBandRealBadPrimes {b c : ℝ} {N p : ℕ} :
    p ∈ parameterBandRealBadPrimes b c N ↔
      p < N ∧ Nat.Prime p ∧
        ∃ r q : ℕ, Nat.Prime r ∧ Nat.Prime q ∧ N - p = r * q ∧ r ≤ q ∧
          (q : ℝ) ^ b < (r : ℝ) ∧ (r : ℝ) ≤ (q : ℝ) ^ c := by
  classical
  simp only [parameterBandRealBadPrimes, Finset.mem_filter,
    mem_realOrderedBadPrimes]
  constructor
  · rintro ⟨⟨hpN, hp, r, q, hr, hq, hm, hrq, hb⟩, hc⟩
    refine ⟨hpN, hp, r, q, hr, hq, hm, hrq, hb, ?_⟩
    apply le_of_not_gt
    intro hpow
    exact hc ⟨r, q, hr, hq, hm, hrq, hpow⟩
  · rintro ⟨hpN, hp, r, q, hr, hq, hm, hrq, hb, hc⟩
    refine ⟨⟨hpN, hp, r, q, hr, hq, hm, hrq, hb⟩, ?_⟩
    intro hbad
    exact (not_lt_of_ge hc)
      ((orderedBad_iff_fixedFactors hr hq hm hrq).mp hbad)

/-- Exact strengthening of the already-proved antitonicity: below exponent
one the difference of the actual counts is exactly the lost-band count.
The positive-exponent manuscript range is a special case. -/
theorem realB_eq_add_parameterBand {b c : ℝ}
    (hbc : b ≤ c) (hc : c < 1) (N : ℕ) :
    RealB b N = RealB c N + (parameterBandRealBadPrimes b c N).card := by
  classical
  rw [RealB_eq_realOrderedBadPrimes_card (hbc.trans_lt hc),
    RealB_eq_realOrderedBadPrimes_card hc]
  have hfilter :
      (realOrderedBadPrimes b N).filter
          (fun p => RealOrderedBadReceiver c (N - p)) =
        realOrderedBadPrimes c N := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hb, hbad⟩
      rcases mem_realOrderedBadPrimes.mp hb with ⟨hpN, hpprime, _⟩
      exact mem_realOrderedBadPrimes.mpr ⟨hpN, hpprime, hbad⟩
    · intro hp
      rcases mem_realOrderedBadPrimes.mp hp with ⟨hpN, hpprime, hbad⟩
      exact Finset.mem_filter.mpr
        ⟨mem_realOrderedBadPrimes.mpr
          ⟨hpN, hpprime, realOrderedBadReceiver_antitone hbc hbad⟩, hbad⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := realOrderedBadPrimes b N)
    (fun p => RealOrderedBadReceiver c (N - p))
  rw [hfilter] at hsplit
  exact hsplit.symm

/-- This is an exact natural-number subtraction, with no truncation loss. -/
theorem realB_sub_eq_parameterBand_card {b c : ℝ}
    (hbc : b ≤ c) (hc : c < 1) (N : ℕ) :
    RealB b N - RealB c N = (parameterBandRealBadPrimes b c N).card := by
  have hsplit := realB_eq_add_parameterBand hbc hc N
  omega

/-- Equality in parameter antitonicity occurs exactly when the explicit
open/closed factor band has no actual additive-prime partners. -/
theorem realB_eq_iff_parameterBand_empty {b c : ℝ}
    (hbc : b ≤ c) (hc : c < 1) (N : ℕ) :
    RealB b N = RealB c N ↔ parameterBandRealBadPrimes b c N = ∅ := by
  classical
  have hsplit := realB_eq_add_parameterBand hbc hc N
  constructor
  · intro heq
    apply Finset.card_eq_zero.mp
    omega
  · intro hempty
    have hzero : (parameterBandRealBadPrimes b c N).card = 0 := by
      rw [hempty, Finset.card_empty]
    omega

/-- A literal power-endpoint equality gives a strict decrease of the actual
count whenever that receiver has an additive-prime partner. -/
theorem realB_lt_of_power_endpoint {b c : ℝ} {N p r q : ℕ}
    (hbc : b < c) (hc : c < 1) (hpN : p < N) (hp : Nat.Prime p)
    (hr : Nat.Prime r) (hq : Nat.Prime q) (hm : N - p = r * q)
    (hrq : r ≤ q) (heq : (q : ℝ) ^ c = (r : ℝ)) :
    RealB c N < RealB b N := by
  classical
  have hqR : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq.one_lt
  have hb : (q : ℝ) ^ b < (r : ℝ) :=
    (Real.rpow_lt_rpow_of_exponent_lt hqR hbc).trans_eq heq
  have hband : p ∈ parameterBandRealBadPrimes b c N :=
    mem_parameterBandRealBadPrimes.mpr
      ⟨hpN, hp, r, q, hr, hq, hm, hrq, hb, le_of_eq heq.symm⟩
  have hpos : 0 < (parameterBandRealBadPrimes b c N).card :=
    Finset.card_pos.mpr ⟨p, hband⟩
  have hsplit := realB_eq_add_parameterBand hbc.le hc N
  omega

end

end P4BRealBParameterMonotonicity
end ImbalancedChen
