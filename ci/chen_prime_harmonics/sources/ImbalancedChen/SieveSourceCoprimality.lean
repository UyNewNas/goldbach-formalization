import ImbalancedChen.HalfProductSource
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# The finite sieve attached to the actual half-product source

For a natural cap `z`, the sieving product is exactly the product of primes
`ell < z` that do not divide `N`. The inequality at the cap is strict.
The already proved rough-factor geometry makes every half-product coprime
to this product when `z ≤ T ^ (b / (1 + b))`, with `b = num / den`.
Prime squares require no exception: every prime divisor of `r * q` is
either `r` or `q`, whether or not these two primes are equal.

The residue-class bridge uses natural subtraction only for `m ≤ N`.
Every divisor of the sieve product is coprime to `N`, so the residue `N`
is primitive. These are exact finite inputs to a possible distribution
theorem, not an assumed distribution estimate.

Prime partners at least `z` survive the sieve. Smaller prime partners are
kept as an explicit correction, bounded by `z` via the injective map
`m ↦ N - m`. Thus the retained actual prime-partner count is bounded by
the sifted cardinality plus a proved small-partner loss. No asymptotic,
sieve upper bound, or prime-counting hypothesis is assumed here.
-/

namespace ImbalancedChen

noncomputable section

/-- Allowed sieving primes, with the literal strict natural cap. -/
def sievePrimes (N z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range z).filter (fun ell : ℕ => Nat.Prime ell ∧ ¬ell ∣ N)

@[simp] theorem mem_sievePrimes {N z ell : ℕ} :
    ell ∈ sievePrimes N z ↔ ell < z ∧ Nat.Prime ell ∧ ¬ell ∣ N := by
  classical
  simp only [sievePrimes, Finset.mem_filter, Finset.mem_range]

/-- The manuscript's finite product `P_N(z)` for a natural cap. -/
def sieveProduct (N z : ℕ) : ℕ :=
  (sievePrimes N z).prod (fun ell : ℕ => ell)

/-- The excluded-divisor condition gives the primitive residue directly. -/
theorem sieveProduct_coprime (N z : ℕ) : Nat.Coprime (sieveProduct N z) N := by
  classical
  unfold sieveProduct
  apply Nat.coprime_prod_left_iff.mpr
  intro ell hell
  rcases mem_sievePrimes.mp hell with ⟨_, hp, hndvd⟩
  exact hp.coprime_iff_not_dvd.mpr hndvd

/-- Every allowed modulus has `N` as a primitive residue. -/
theorem coprime_of_dvd_sieveProduct {N z d : ℕ} (hd : d ∣ sieveProduct N z) :
    Nat.Coprime d N :=
  Nat.Coprime.of_dvd_left hd (sieveProduct_coprime N z)

theorem gcd_eq_one_of_dvd_sieveProduct {N z d : ℕ}
    (hd : d ∣ sieveProduct N z) : Nat.gcd d N = 1 :=
  (coprime_of_dvd_sieveProduct hd).gcd_eq_one

/-- A prime divisor of a prime half-product is one of its two factors.
There is no distinctness assumption and thus no missing square case. -/
theorem prime_dvd_halfProduct_iff {ell r q : ℕ}
    (hell : Nat.Prime ell) (hr : Nat.Prime r) (hq : Nat.Prime q) :
    ell ∣ r * q ↔ ell = r ∨ ell = q := by
  rw [hell.dvd_mul, Nat.prime_dvd_prime_iff_eq hell hr,
    Nat.prime_dvd_prime_iff_eq hell hq]

/-- Every prime divisor of an actual source member exceeds its roughness
threshold, including when the source member is a prime square. -/
theorem halfProductSource_prime_divisor_rough {num den N m ell : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hm : m ∈ halfProductSource num den N T)
    (hell : Nat.Prime ell) (hdvd : ell ∣ m) :
    T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))) < (ell : ℝ) := by
  obtain ⟨_, _, r, q, hr, hq, hmul, _, _, hroughR, hroughQ⟩ :=
    halfProductSource_exists_rough_factors hnum hden hT hm
  rw [hmul] at hdvd
  rcases (prime_dvd_halfProduct_iff hell hr hq).mp hdvd with h | h
  · simpa only [h] using hroughR
  · simpa only [h] using hroughQ

/-- No prime below the cap divides a source member when the cap lies below
the proved roughness threshold. The prime need not be an allowed sieve prime. -/
theorem halfProductSource_not_dvd_of_prime_lt_cap
    {num den N m ell z : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (hm : m ∈ halfProductSource num den N T)
    (hell : Nat.Prime ell) (hellz : ell < z) : ¬ell ∣ m := by
  intro hdvd
  have hrough := halfProductSource_prime_divisor_rough hnum hden hT hm hell hdvd
  have hlt : (ell : ℝ) < (z : ℝ) := Nat.cast_lt.mpr hellz
  exact (not_lt_of_ge (le_trans hlt.le hcap)) hrough

/-- All actual source members are coprime to the entire finite sieve product. -/
theorem halfProductSource_coprime_sieveProduct {num den N m z : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (hm : m ∈ halfProductSource num den N T) :
    Nat.Coprime m (sieveProduct N z) := by
  classical
  unfold sieveProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro ell hell
  rcases mem_sievePrimes.mp hell with ⟨hellz, hp, _⟩
  exact (hp.coprime_iff_not_dvd.mpr
    (halfProductSource_not_dvd_of_prime_lt_cap hnum hden hT hcap hm hp hellz)).symm

/-- The coprimality input holds for every divisor of the sieve product. -/
theorem halfProductSource_coprime_of_dvd_sieveProduct
    {num den N m z d : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ))))
    (hm : m ∈ halfProductSource num den N T) (hd : d ∣ sieveProduct N z) :
    Nat.Coprime m d :=
  Nat.Coprime.of_dvd_right hd
    (halfProductSource_coprime_sieveProduct hnum hden hT hcap hm)

/-- The exact shift-to-residue bridge. The upper bound prevents truncated
natural subtraction from changing the congruence condition. -/
theorem dvd_sub_iff_modEq_of_le {N m d : ℕ} (hmN : m ≤ N) :
    d ∣ N - m ↔ Nat.ModEq d m N :=
  (Nat.modEq_iff_dvd' hmN).symm

/-- Divisibility of the shifted source is exactly the residue-class filter. -/
theorem halfProductSource_filter_dvd_eq_filter_modEq
    (num den N d : ℕ) (T : ℝ) :
    (halfProductSource num den N T).filter (fun m : ℕ => d ∣ N - m) =
      (halfProductSource num den N T).filter (fun m : ℕ => Nat.ModEq d m N) := by
  classical
  ext m
  constructor
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmem, hdvd⟩
    exact Finset.mem_filter.mpr ⟨hmem,
      (dvd_sub_iff_modEq_of_le (mem_halfProductSource.mp hmem).1).mp hdvd⟩
  · intro hm
    rcases Finset.mem_filter.mp hm with ⟨hmem, hmod⟩
    exact Finset.mem_filter.mpr ⟨hmem,
      (dvd_sub_iff_modEq_of_le (mem_halfProductSource.mp hmem).1).mpr hmod⟩

/-- All finite inputs for a primitive residue-class count, without a
distribution or remainder estimate hidden in the hypotheses. -/
theorem halfProductSource_sieve_modulus_data
    {num den N z d : ℕ} {T : ℝ}
    (hnum : 0 < num) (hden : 0 < den) (hT : 0 < T)
    (hcap : (z : ℝ) ≤ T ^ (((num : ℝ) / (den : ℝ)) /
      (1 + (num : ℝ) / (den : ℝ)))) (hd : d ∣ sieveProduct N z) :
    Nat.Coprime d N ∧
      (∀ m ∈ halfProductSource num den N T, Nat.Coprime m d) ∧
      ((halfProductSource num den N T).filter (fun m : ℕ => d ∣ N - m)).card =
        ((halfProductSource num den N T).filter (fun m : ℕ => Nat.ModEq d m N)).card := by
  classical
  refine ⟨coprime_of_dvd_sieveProduct hd, ?_, ?_⟩
  · intro m hm
    exact halfProductSource_coprime_of_dvd_sieveProduct hnum hden hT hcap hm hd
  · rw [halfProductSource_filter_dvd_eq_filter_modEq]

/-- The exact sifted source `S(A;N,z)`, before any upper-sieve estimate. -/
def siftedHalfProductSource (num den N : ℕ) (T : ℝ) (z : ℕ) : Finset ℕ := by
  classical
  exact (halfProductSource num den N T).filter
    (fun m : ℕ => Nat.Coprime (N - m) (sieveProduct N z))

@[simp] theorem mem_siftedHalfProductSource {num den N m z : ℕ} {T : ℝ} :
    m ∈ siftedHalfProductSource num den N T z ↔
      m ∈ halfProductSource num den N T ∧ Nat.Coprime (N - m) (sieveProduct N z) := by
  classical
  simp only [siftedHalfProductSource, Finset.mem_filter]

/-- A prime at least the strict sieve cap survives every allowed sieve prime. -/
theorem prime_coprime_sieveProduct_of_cap_le {N z p : ℕ}
    (hp : Nat.Prime p) (hz : z ≤ p) : Nat.Coprime p (sieveProduct N z) := by
  classical
  unfold sieveProduct
  apply Nat.coprime_prod_right_iff.mpr
  intro ell hell
  rcases mem_sievePrimes.mp hell with ⟨hellz, hellprime, _⟩
  exact (Nat.coprime_primes hp hellprime).mpr (ne_of_gt (lt_of_lt_of_le hellz hz))

/-- The large-prime-partner part of the actual retained count survives. -/
theorem retainedBadReceiversReal_filter_cap_subset_sifted
    (num den N z : ℕ) (T : ℝ) :
    (retainedBadReceiversReal num den N T).filter (fun m : ℕ => z ≤ N - m) ⊆
      siftedHalfProductSource num den N T z := by
  classical
  intro m hm
  rcases Finset.mem_filter.mp hm with ⟨hmem, hcap⟩
  have hp := (mem_badReceivers.mp (mem_retainedBadReceiversReal.mp hmem).1).2.2.1
  exact mem_siftedHalfProductSource.mpr
    ⟨retainedBadReceiversReal_subset_halfProductSource num den N T hmem,
      prime_coprime_sieveProduct_of_cap_le hp hcap⟩

/-- The explicit correction for prime partners smaller than the sieve cap. -/
def smallPrimePartnerReceivers (num den N : ℕ) (T : ℝ) (z : ℕ) : Finset ℕ := by
  classical
  exact (retainedBadReceiversReal num den N T).filter (fun m : ℕ => N - m < z)

@[simp] theorem mem_smallPrimePartnerReceivers {num den N m z : ℕ} {T : ℝ} :
    m ∈ smallPrimePartnerReceivers num den N T z ↔
      m ∈ retainedBadReceiversReal num den N T ∧ N - m < z := by
  classical
  simp only [smallPrimePartnerReceivers, Finset.mem_filter]

/-- Small prime partners cost at most `z` receivers, by the injective
complement map into `[0,z)`. This is a finite bound, not a prime asymptotic. -/
theorem smallPrimePartnerReceivers_card_le (num den N z : ℕ) (T : ℝ) :
    (smallPrimePartnerReceivers num den N T z).card ≤ z := by
  classical
  calc
    (smallPrimePartnerReceivers num den N T z).card ≤ (Finset.range z).card := by
      apply Finset.card_le_card_of_injOn (fun m : ℕ => N - m)
      · intro m hm
        exact Finset.mem_range.mpr (mem_smallPrimePartnerReceivers.mp hm).2
      · intro m hm n hn hmn
        change N - m = N - n at hmn
        have hmN := (mem_badReceivers.mp
          (mem_retainedBadReceiversReal.mp (mem_smallPrimePartnerReceivers.mp hm).1).1).1
        have hnN := (mem_badReceivers.mp
          (mem_retainedBadReceiversReal.mp (mem_smallPrimePartnerReceivers.mp hn).1).1).1
        omega
    _ = z := Finset.card_range z

/-- Exact split of the prime-partner count at the strict sieve cap. -/
theorem retainedBadReceiversReal_card_eq_large_add_smallPrimePartner
    (num den N z : ℕ) (T : ℝ) :
    (retainedBadReceiversReal num den N T).card =
      ((retainedBadReceiversReal num den N T).filter (fun m : ℕ => z ≤ N - m)).card +
        (smallPrimePartnerReceivers num den N T z).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := retainedBadReceiversReal num den N T) (fun m : ℕ => z ≤ N - m)
  simpa only [smallPrimePartnerReceivers, not_le] using h.symm

/-- Prime partners are bounded by the sifted count plus an explicit loss.
No source roughness assumption is needed for this finite comparison. -/
theorem retainedBadReceiversReal_card_le_sifted_add_smallPrimePartner
    (num den N z : ℕ) (T : ℝ) :
    (retainedBadReceiversReal num den N T).card ≤
      (siftedHalfProductSource num den N T z).card +
        (smallPrimePartnerReceivers num den N T z).card := by
  rw [retainedBadReceiversReal_card_eq_large_add_smallPrimePartner num den N z T]
  exact Nat.add_le_add_right (Finset.card_le_card
    (retainedBadReceiversReal_filter_cap_subset_sifted num den N z T)) _

/-- The actual retained prime-partner count is at most the sifted
cardinality plus `z`; the small-prime correction is never silently omitted. -/
theorem retainedBadReceiversReal_card_le_sifted_add_cap
    (num den N z : ℕ) (T : ℝ) :
    (retainedBadReceiversReal num den N T).card ≤
      (siftedHalfProductSource num den N T z).card + z :=
  (retainedBadReceiversReal_card_le_sifted_add_smallPrimePartner num den N z T).trans
    (Nat.add_le_add_left (smallPrimePartnerReceivers_card_le num den N z T) _)

/-- The original bad count is bounded by the genuine sifted half-product
count and its two explicit finite corrections. -/
theorem B_le_siftedHalfProductSource_card_add_errors
    (num den N z : ℕ) (T : ℝ) :
    B num den N ≤ (siftedHalfProductSource num den N T z).card +
      (smallPrimePartnerReceivers num den N T z).card +
        (smallBadReceiversReal num den N T).card := by
  rw [B_eq_retainedBadReceiversReal_card_add_smallBadReceiversReal_card num den N T]
  exact Nat.add_le_add_right
    (retainedBadReceiversReal_card_le_sifted_add_smallPrimePartner num den N z T) _

/-- A ready-to-normalize finite bound with literal real cutoff and natural
sieve cap. The only costs are `z` and the already proved `T + 1`. -/
theorem B_cast_le_siftedHalfProductSource_card_add_cap_cutoff
    (num den N z : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    (B num den N : ℝ) ≤
      (siftedHalfProductSource num den N T z).card + (z : ℝ) + (T + 1) := by
  have hretained : ((retainedBadReceiversReal num den N T).card : ℝ) ≤
      (siftedHalfProductSource num den N T z).card + (z : ℝ) := by
    exact_mod_cast retainedBadReceiversReal_card_le_sifted_add_cap num den N z T
  exact (B_cast_le_retainedBadReceiversReal_card_add_cutoff num den N hT).trans
    (add_le_add hretained le_rfl)

end

end ImbalancedChen
