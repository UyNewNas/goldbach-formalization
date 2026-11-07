import ImbalancedChen.RealHalfProductSource
import ImbalancedChen.RealHalfProductSieveBridge
import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.FiniteSieveModel

/-!
# Exact actual bad-receiver partition (P4B, source-only)

YELLOW / UNCOMPILED. No analytic estimate is claimed. The exceptional
contribution is an exact pointwise-filtered set of sieve primes, rather
than every integer below the cap. The three pieces index receivers, so
ordered equal factors and prime squares contribute once.
-/

namespace ImbalancedChen.P4BBadReceiverPartition

noncomputable section

/-- Actual retained receivers whose additive prime survives the sieve. -/
def survivingReceivers (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) : Finset ℕ := by
  classical
  exact (retainedRealBadReceivers b N T).filter
    (fun m => Nat.Coprime (N - m) (sieveProduct N z))

/-- Only actual additive primes appearing in the sieve product are lost. -/
def exceptionalReceivers (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) : Finset ℕ := by
  classical
  exact (retainedRealBadReceivers b N T).filter
    (fun m => N - m ∈ sievePrimes N z)

/-- The exception written pointwise at its prime, including the original
strict endpoint and the literal product cutoff. -/
def exceptionalPrimes (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) : Finset ℕ := by
  classical
  exact (sievePrimes N z).filter
    (fun p => p < N ∧ T ≤ (N - p : ℕ) ∧
      RealOrderedBadReceiver b (N - p))

@[simp] theorem mem_survivingReceivers {b T : ℝ} {N z m : ℕ} :
    m ∈ survivingReceivers b N T z ↔
      m ∈ retainedRealBadReceivers b N T ∧
        Nat.Coprime (N - m) (sieveProduct N z) := by
  classical
  simp only [survivingReceivers, Finset.mem_filter]

@[simp] theorem mem_exceptionalReceivers {b T : ℝ} {N z m : ℕ} :
    m ∈ exceptionalReceivers b N T z ↔
      m ∈ retainedRealBadReceivers b N T ∧ N - m ∈ sievePrimes N z := by
  classical
  simp only [exceptionalReceivers, Finset.mem_filter]

@[simp] theorem mem_exceptionalPrimes {b T : ℝ} {N z p : ℕ} :
    p ∈ exceptionalPrimes b N T z ↔
      p ∈ sievePrimes N z ∧ p < N ∧ T ≤ (N - p : ℕ) ∧
        RealOrderedBadReceiver b (N - p) := by
  classical
  simp only [exceptionalPrimes, Finset.mem_filter]

/-- Primes dividing the target are correctly absent from the exception,
even when they lie below the sieve cap. -/
theorem prime_coprime_iff_not_mem {N z p : ℕ} (hp : Nat.Prime p) :
    Nat.Coprime p (sieveProduct N z) ↔ p ∉ sievePrimes N z := by
  classical
  rw [hp.coprime_iff_not_dvd]
  constructor
  · intro hnot hmem
    exact hnot (Finset.dvd_prod_of_mem (fun q : ℕ => q) hmem)
  · intro hnot hdvd
    exact hnot (prime_mem_sievePrimes_of_dvd hp hdvd)

theorem not_coprime_iff_mem {N z p : ℕ} (hp : Nat.Prime p) :
    ¬Nat.Coprime p (sieveProduct N z) ↔ p ∈ sievePrimes N z := by
  classical
  simpa only [not_not] using not_congr (prime_coprime_iff_not_mem hp)

theorem retained_partition (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    retainedRealBadReceivers b N T =
      survivingReceivers b N T z ∪ exceptionalReceivers b N T z := by
  classical
  ext m
  rw [Finset.mem_union, mem_survivingReceivers, mem_exceptionalReceivers]
  constructor
  · intro hm
    have hp := (mem_realBadReceivers.mp
      (mem_retainedRealBadReceivers.mp hm).1).2.2.1
    by_cases hcop : Nat.Coprime (N - m) (sieveProduct N z)
    · exact Or.inl ⟨hm, hcop⟩
    · exact Or.inr ⟨hm, (not_coprime_iff_mem hp).mp hcop⟩
  · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm

theorem surviving_disjoint_exceptional (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    Disjoint (survivingReceivers b N T z) (exceptionalReceivers b N T z) := by
  classical
  apply Finset.disjoint_left.mpr
  intro m hsurv hexc
  obtain ⟨hm, hcop⟩ := mem_survivingReceivers.mp hsurv
  have hp := (mem_realBadReceivers.mp
    (mem_retainedRealBadReceivers.mp hm).1).2.2.1
  exact (prime_coprime_iff_not_mem hp).mp hcop
    (mem_exceptionalReceivers.mp hexc).2

/-- The cutoff is inclusive in each retained piece, strict in the small
piece. Thus equality at the cutoff has exactly one destination. -/
theorem small_disjoint_retained (b : ℝ) (N : ℕ) (T : ℝ) :
    Disjoint (smallRealBadReceivers b N T) (retainedRealBadReceivers b N T) := by
  classical
  apply Finset.disjoint_left.mpr
  intro m hsmall hret
  exact (not_lt_of_ge (mem_retainedRealBadReceivers.mp hret).2)
    (mem_smallRealBadReceivers.mp hsmall).2

theorem actual_partition (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    realBadReceivers b N =
      (survivingReceivers b N T z ∪ exceptionalReceivers b N T z) ∪
        smallRealBadReceivers b N T := by
  classical
  rw [← retained_partition b N T z]
  ext m
  simp only [Finset.mem_union, mem_retainedRealBadReceivers,
    mem_smallRealBadReceivers]
  constructor
  · intro hm
    by_cases hT : T ≤ (m : ℝ)
    · exact Or.inl ⟨hm, hT⟩
    · exact Or.inr ⟨hm, lt_of_not_ge hT⟩
  · rintro (⟨hm, _⟩ | ⟨hm, _⟩) <;> exact hm

theorem retained_union_disjoint_small (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    Disjoint (survivingReceivers b N T z ∪ exceptionalReceivers b N T z)
      (smallRealBadReceivers b N T) := by
  rw [← retained_partition b N T z]
  exact (small_disjoint_retained b N T).symm

theorem retained_card_eq (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    (retainedRealBadReceivers b N T).card =
      (survivingReceivers b N T z).card + (exceptionalReceivers b N T z).card := by
  rw [retained_partition b N T z,
    Finset.card_union_of_disjoint (surviving_disjoint_exceptional b N T z)]

/-- Exact prime reindexing of the exceptional piece; no all-small-prime
count and no factorization-witness count occurs in this identity. -/
theorem exceptional_card_eq (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    (exceptionalReceivers b N T z).card = (exceptionalPrimes b N T z).card := by
  classical
  refine Finset.card_bij' (fun m _ => N - m) (fun p _ => N - p) ?_ ?_ ?_ ?_
  · intro m hm
    obtain ⟨hret, hprimeSet⟩ := mem_exceptionalReceivers.mp hm
    obtain ⟨hactual, hcut⟩ := mem_retainedRealBadReceivers.mp hret
    obtain ⟨hmN, hm0, _, hbad⟩ := mem_realBadReceivers.mp hactual
    have hinv : N - (N - m) = m := by omega
    apply mem_exceptionalPrimes.mpr
    refine ⟨hprimeSet, by omega, ?_, ?_⟩
    · simpa only [hinv] using hcut
    · simpa only [hinv] using hbad
  · intro p hp
    obtain ⟨hpSet, hpN, hcut, hbad⟩ := mem_exceptionalPrimes.mp hp
    have hprime := (mem_sievePrimes.mp hpSet).2.1
    have hp0 := hprime.pos
    have hinv : N - (N - p) = p := by omega
    apply mem_exceptionalReceivers.mpr
    refine ⟨mem_retainedRealBadReceivers.mpr ⟨?_, hcut⟩, ?_⟩
    · apply mem_realBadReceivers.mpr
      refine ⟨by omega, by omega, ?_, hbad⟩
      simpa only [hinv] using hprime
    · simpa only [hinv] using hpSet
  · intro m hm
    have hmN := (mem_realBadReceivers.mp
      (mem_retainedRealBadReceivers.mp (mem_exceptionalReceivers.mp hm).1).1).1
    omega
  · intro p hp
    have hpN := (mem_exceptionalPrimes.mp hp).2.1
    omega

/-- Three actual disjoint contributions, with the exceptional contribution
displayed at the prime where it can be estimated pointwise. -/
theorem RealB_eq_three_actual_cards {b : ℝ} (hb : b < 1)
    (N : ℕ) (T : ℝ) (z : ℕ) :
    RealB b N = (survivingReceivers b N T z).card +
      (exceptionalPrimes b N T z).card + (smallRealBadReceivers b N T).card := by
  rw [RealB_eq_retainedRealBadReceivers_card_add_smallRealBadReceivers_card hb N T,
    retained_card_eq b N T z, exceptional_card_eq b N T z]

/-- The retained survivor is the actual prime-partner subfilter of the
existing sifted source, rather than the entire sifted source. -/
theorem surviving_eq_sifted_prime_filter (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    survivingReceivers b N T z =
      (realSiftedHalfProductSource b N T z).filter
        (fun m => m < N ∧ Nat.Prime (N - m)) := by
  classical
  ext m
  simp only [mem_survivingReceivers,
    retainedRealBadReceivers_eq_realHalfProductSource_filter,
    Finset.mem_filter, mem_realSiftedHalfProductSource]
  constructor
  · rintro ⟨⟨hsource, hp⟩, hcop⟩
    exact ⟨⟨hsource, hcop⟩, hp⟩
  · rintro ⟨⟨hsource, hcop⟩, hp⟩
    exact ⟨⟨hsource, hp⟩, hcop⟩

/-- The exact same pointwise correction at the manuscript's real sieve
cutoff; the covering cap does not add an endpoint atom. -/
theorem exceptionalPrimes_real_cutoff (b : ℝ) (N cap : ℕ) (T z : ℝ)
    (hzcap : z ≤ (cap : ℝ)) :
    exceptionalPrimes b N T (Nat.ceil z) =
      (actualSmallPrimeFinset N cap z).filter
        (fun p => p < N ∧ T ≤ (N - p : ℕ) ∧
          RealOrderedBadReceiver b (N - p)) := by
  rw [exceptionalPrimes,
    actualSmallPrimeFinset_eq_sievePrimes_ceil N cap z hzcap]

/-- A sharper finite envelope for the exception: the cap, strict target
endpoint and literal lower product cutoff all remain in the prime set. -/
theorem exceptional_card_le_boundary_primes (b : ℝ) (N : ℕ) (T : ℝ) (z : ℕ) :
    (exceptionalReceivers b N T z).card ≤
      ((sievePrimes N z).filter (fun p => p < N ∧ T ≤ (N - p : ℕ))).card := by
  classical
  rw [exceptional_card_eq]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpSet, hpN, hcut, _⟩ := mem_exceptionalPrimes.mp hp
  exact Finset.mem_filter.mpr ⟨hpSet, hpN, hcut⟩

/-- The integer lower bound is unconditional in b, and squares attain it. -/
theorem four_le_bad_receiver {b : ℝ} {m : ℕ} (hm : RealOrderedBadReceiver b m) :
    4 ≤ m := by
  obtain ⟨r, q, hr, hq, rfl, _, _⟩ := hm
  exact le_trans (by decide : 4 ≤ 2 * 2) (Nat.mul_le_mul hr.two_le hq.two_le)

/-- Both endpoint exclusions improve the earlier ceiling bound. The
subtractions are natural, so the result includes empty and tiny ranges. -/
theorem small_card_le_boundary_width (b : ℝ) (N : ℕ) (T : ℝ) :
    (smallRealBadReceivers b N T).card ≤ min (Nat.ceil T) (N - 1) - 4 := by
  classical
  calc
    (smallRealBadReceivers b N T).card ≤
        (Finset.range (min (Nat.ceil T) (N - 1) - 4)).card := by
      apply Finset.card_le_card_of_injOn (fun m : ℕ => m - 4)
      · intro m hm
        obtain ⟨hactual, hcut⟩ := mem_smallRealBadReceivers.mp hm
        obtain ⟨hmN, _, hp, hbad⟩ := mem_realBadReceivers.mp hactual
        have hm4 := four_le_bad_receiver hbad
        have hp2 := hp.two_le
        have hmceil := Nat.lt_ceil.mpr hcut
        have hmbound : m < min (Nat.ceil T) (N - 1) :=
          lt_min hmceil (by omega)
        exact Finset.mem_range.mpr (by omega)
      · intro m hm n hn hmn
        have hm4 := four_le_bad_receiver
          (mem_realBadReceivers.mp (mem_smallRealBadReceivers.mp hm).1).2.2.2
        have hn4 := four_le_bad_receiver
          (mem_realBadReceivers.mp (mem_smallRealBadReceivers.mp hn).1).2.2.2
        change m - 4 = n - 4 at hmn
        omega
    _ = min (Nat.ceil T) (N - 1) - 4 := Finset.card_range _

/-- Ordered factors are unique in every retained piece, including r=q. -/
theorem retained_existsUnique_ordered_pair {b T : ℝ} {N m : ℕ}
    (hm : m ∈ retainedRealBadReceivers b N T) :
    ∃! a : ℕ × ℕ, a ∈ realHalfProductPairs b N T ∧ a.1 * a.2 = m := by
  rw [retainedRealBadReceivers_eq_realHalfProductSource_filter] at hm
  exact realHalfProductSource_existsUnique_pair (Finset.mem_filter.mp hm).1

/-- Prime squares require no exceptional convention at the diagonal. -/
theorem square_mem_retained_iff {b T : ℝ} {N r : ℕ}
    (hb : b < 1) (hr : Nat.Prime r) :
    r * r ∈ retainedRealBadReceivers b N T ↔
      r * r < N ∧ Nat.Prime (N - r * r) ∧ T ≤ (r * r : ℕ) := by
  constructor
  · intro hm
    obtain ⟨hactual, hcut⟩ := mem_retainedRealBadReceivers.mp hm
    obtain ⟨hmN, _, hp, _⟩ := mem_realBadReceivers.mp hactual
    exact ⟨hmN, hp, hcut⟩
  · rintro ⟨hmN, hp, hcut⟩
    apply mem_retainedRealBadReceivers.mpr
    refine ⟨mem_realBadReceivers.mpr ⟨hmN, Nat.mul_pos hr.pos hr.pos, hp, ?_⟩,
      hcut⟩
    refine ⟨r, r, hr, hr, rfl, le_rfl, ?_⟩
    have hrR : (1 : ℝ) < (r : ℝ) := by exact_mod_cast hr.one_lt
    exact Real.rpow_lt_self_of_one_lt hrR hb

/-- At the strict sieve wall p=z the partner always survives. -/
theorem partner_at_cap_survives {b T : ℝ} {N z m : ℕ}
    (hm : m ∈ retainedRealBadReceivers b N T) (hcap : N - m = z) :
    m ∈ survivingReceivers b N T z := by
  have hp := (mem_realBadReceivers.mp
    (mem_retainedRealBadReceivers.mp hm).1).2.2.1
  exact mem_survivingReceivers.mpr
    ⟨hm, prime_coprime_sieveProduct_of_cap_le hp (by omega)⟩

/-- A prime partner dividing N survives for every cap, even below z.
This is why charging every small additive prime is unnecessarily coarse. -/
theorem partner_dvd_target_survives {b T : ℝ} {N z m : ℕ}
    (hm : m ∈ retainedRealBadReceivers b N T) (hdvd : N - m ∣ N) :
    m ∈ survivingReceivers b N T z := by
  have hp := (mem_realBadReceivers.mp
    (mem_retainedRealBadReceivers.mp hm).1).2.2.1
  apply mem_survivingReceivers.mpr
  refine ⟨hm, (prime_coprime_iff_not_mem hp).mpr ?_⟩
  intro hmem
  exact (mem_sievePrimes.mp hmem).2.2 hdvd

end

end ImbalancedChen.P4BBadReceiverPartition
