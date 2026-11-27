import ImbalancedChen.QuotientChenElevenSum
import ImbalancedChen.FiniteSieveModel
import ImbalancedChen.CoprimeRecentering

/-!
# The actual prime source for the first two Chen terms

The single source is the injective image of the original additive primes
`P ≤ N`, `Coprime P N`, under `P ↦ N - P`. Its genuine `BoundingSieve`
uses unit weights, its actual cardinality, and reciprocal-totient density.
The first two literal Upsilon sums are exactly its sifted sums at the
ceiling of their real cutoffs. Primes equal to the cutoff are retained.

Every divisibility fibre is identified with an actual prime AP count,
minus the explicit centre-prime correction. The source is NOT silently
declared coprime to the modulus: primes dividing the modulus occur in its
total mass and require a second explicit correction when recentering.
Receiver one is retained; receiver zero is excluded by source coprimality.
All identities are finite and unconditional, apart from evenness needed
for the strict local-density axiom of `BoundingSieve`. There is no linear
lower-sieve estimate or analytic distribution hypothesis in this module.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- The literal inclusive prime prefix, before excluding centre divisors. -/
def chenPrimePrefix (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

@[simp] theorem mem_chenPrimePrefix {N P : ℕ} :
    P ∈ chenPrimePrefix N ↔ P ≤ N ∧ Nat.Prime P := by
  simp only [chenPrimePrefix, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]

/-- Inclusive prime AP mass, with no primitive-residue mask inserted. -/
def chenPrimeAPCount (N a d : ℕ) : ℝ :=
  (((chenPrimePrefix N).filter (fun P => Nat.ModEq d P a)).card : ℝ)

/-- Prime divisors of `k` in the inclusive prefix. The definition also
handles `k = 0` without using the empty convention for `0.primeFactors`. -/
def chenPrimeDivisorCount (N k : ℕ) : ℝ :=
  (((chenPrimePrefix N).filter (fun P => P ∣ k)).card : ℝ)

/-- The centre-prime correction in the actual selected progression. -/
def chenCentrePrimeAPCount (N a d : ℕ) : ℝ :=
  (((chenPrimePrefix N).filter
    (fun P => Nat.ModEq d P a ∧ P ∣ N)).card : ℝ)

/-- The manuscript source is precisely the prime prefix with the actual
prime divisors of the centre removed, including the prime centre itself. -/
theorem chenAdditivePrimeCarrier_eq_prefix_filter (N : ℕ) :
    chenAdditivePrimeCarrier N =
      (chenPrimePrefix N).filter (fun P => ¬P ∣ N) := by
  classical
  ext P
  rw [mem_chenAdditivePrimeCarrier_iff_le, Finset.mem_filter, mem_chenPrimePrefix]
  constructor
  · rintro ⟨hPN, hp, hcop⟩
    exact ⟨⟨hPN, hp⟩, hp.coprime_iff_not_dvd.mp hcop⟩
  · rintro ⟨⟨hPN, hp⟩, hnot⟩
    exact ⟨hPN, hp, hp.coprime_iff_not_dvd.mpr hnot⟩

private theorem chen_card_filter_not_cast (S : Finset ℕ) (q : ℕ → Prop)
    [DecidablePred q] :
    ((S.filter (fun n => ¬q n)).card : ℝ) =
      (S.card : ℝ) - ((S.filter q).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := S) q
  have hR : ((S.filter q).card : ℝ) +
      ((S.filter (fun n => ¬q n)).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast h
  linarith

/-- Exact total prime-source mass; no PNT or asymptotic replacement. -/
theorem chenAdditivePrimeCarrier_card_cast (N : ℕ) :
    ((chenAdditivePrimeCarrier N).card : ℝ) =
      ((chenPrimePrefix N).card : ℝ) - chenPrimeDivisorCount N N := by
  classical
  rw [chenAdditivePrimeCarrier_eq_prefix_filter]
  exact chen_card_filter_not_cast (chenPrimePrefix N) (fun P => P ∣ N)

/-- At a prime centre the excluded endpoint is the entire centre-divisor
set. In particular the source does not acquire receiver zero. -/
theorem chenPrimePrefix_filter_dvd_prime_center {N : ℕ} (hN : Nat.Prime N) :
    (chenPrimePrefix N).filter (fun P => P ∣ N) = {N} := by
  classical
  ext P
  rw [Finset.mem_filter, mem_chenPrimePrefix, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨_, hP⟩, hd⟩
    exact (Nat.prime_dvd_prime_iff_eq hP hN).mp hd
  · rintro rfl
    exact ⟨⟨le_rfl, hN⟩, dvd_rfl⟩

theorem chenCentrePrimeAPCount_prime_center {N : ℕ} (hN : Nat.Prime N) (d : ℕ) :
    chenCentrePrimeAPCount N N d = 1 := by
  classical
  have hf : (chenPrimePrefix N).filter (fun P => Nat.ModEq d P N ∧ P ∣ N) =
      ((chenPrimePrefix N).filter (fun P => P ∣ N)).filter
        (fun P => Nat.ModEq d P N) := by
    ext P
    simp only [Finset.mem_filter]
    tauto
  unfold chenCentrePrimeAPCount
  rw [hf, chenPrimePrefix_filter_dvd_prime_center hN]
  have hfilter : ({N} : Finset ℕ).filter (fun P => Nat.ModEq d P N) = {N} := by
    apply Finset.filter_eq_self.mpr
    intro P hP
    have hPN : P = N := Finset.mem_singleton.mp hP
    subst P
    exact Nat.ModEq.refl N
  rw [hfilter]
  norm_num

/-- The actual source in receiver coordinates. -/
def chenPrimeReceiverSource (N : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).image (fun P : ℕ => N - P)

theorem chenPrimeReceiverSource_shift_injective {N P Q : ℕ}
    (hP : P ∈ chenAdditivePrimeCarrier N)
    (hQ : Q ∈ chenAdditivePrimeCarrier N)
    (heq : N - P = N - Q) : P = Q := by
  have hPN := (mem_chenAdditivePrimeCarrier.mp hP).1
  have hQN := (mem_chenAdditivePrimeCarrier.mp hQ).1
  omega

theorem chenPrimeReceiverSource_card (N : ℕ) :
    (chenPrimeReceiverSource N).card = (chenAdditivePrimeCarrier N).card := by
  classical
  apply Finset.card_image_of_injOn
  intro P hP Q hQ heq
  exact chenPrimeReceiverSource_shift_injective hP hQ heq

theorem sum_chenPrimeReceiverSource (N : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ chenPrimeReceiverSource N, f n) =
      ∑ P ∈ chenAdditivePrimeCarrier N, f (N - P) := by
  classical
  unfold chenPrimeReceiverSource
  apply Finset.sum_image
  intro P hP Q hQ heq
  exact chenPrimeReceiverSource_shift_injective hP hQ heq

/-- Every receiver is positive, and centre-prime divisors cannot divide it. -/
theorem chenPrimeReceiverSource_data {N n : ℕ}
    (hn : n ∈ chenPrimeReceiverSource N) :
    0 < n ∧ n ≤ N ∧ Nat.Coprime n N := by
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hPN, _, hcop⟩ := mem_chenAdditivePrimeCarrier.mp hP
  exact ⟨by omega, Nat.sub_le N P,
    (Nat.coprime_self_sub_left hPN.le).mpr hcop⟩

@[simp] theorem zero_not_mem_chenPrimeReceiverSource (N : ℕ) :
    0 ∉ chenPrimeReceiverSource N := by
  intro h
  exact (Nat.lt_irrefl 0) (chenPrimeReceiverSource_data h).1

/-- Receiver one occurs exactly for the prime predecessor of the centre. -/
theorem one_mem_chenPrimeReceiverSource_iff (N : ℕ) :
    1 ∈ chenPrimeReceiverSource N ↔ 1 < N ∧ Nat.Prime (N - 1) := by
  constructor
  · intro h
    obtain ⟨P, hP, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hPN, hp, _⟩ := mem_chenAdditivePrimeCarrier.mp hP
    have hP2 := hp.two_le
    have hPval : P = N - 1 := by omega
    exact ⟨by omega, hPval ▸ hp⟩
  · rintro ⟨hN, hp⟩
    apply Finset.mem_image.mpr
    refine ⟨N - 1, mem_chenAdditivePrimeCarrier.mpr ⟨by omega, hp, ?_⟩, by omega⟩
    exact (Nat.coprime_self_sub_left (by omega : 1 ≤ N)).mpr
      (Nat.coprime_one_left N)

/-- Exact real strict cap, including negative and integral cutoffs. -/
theorem mem_sievePrimes_chen_real_cap {N q : ℕ} {z : ℝ} :
    q ∈ sievePrimes N (Nat.ceil z) ↔
      (q : ℝ) < z ∧ Nat.Prime q ∧ ¬q ∣ N := by
  rw [mem_sievePrimes, Nat.lt_ceil]

/-- Omitting centre primes is harmless precisely because the receiver is
coprime to the centre. Equality at the real cutoff is not removed. -/
theorem chenPrimeRough_iff_coprime_sieveProduct {N n : ℕ} (z : ℝ)
    (hcop : Nat.Coprime n N) :
    ChenPrimeRough z n ↔ Nat.Coprime n (sieveProduct N (Nat.ceil z)) := by
  classical
  constructor
  · intro hrough
    unfold sieveProduct
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    obtain ⟨hqz, hp, _⟩ := mem_sievePrimes_chen_real_cap.mp hq
    exact (hp.coprime_iff_not_dvd.mpr
      (fun hqn => (not_lt_of_ge (hrough q hp hqn)) hqz)).symm
  · intro hs q hp hqn
    by_contra hnot
    have hqz : (q : ℝ) < z := lt_of_not_ge hnot
    have hqN : ¬q ∣ N := hp.coprime_iff_not_dvd.mp (hcop.of_dvd_left hqn)
    have hqmem : q ∈ sievePrimes N (Nat.ceil z) :=
      mem_sievePrimes_chen_real_cap.mpr ⟨hqz, hp, hqN⟩
    have hnq : Nat.Coprime n q :=
      Nat.coprime_prod_right_iff.mp hs q hqmem
    exact (hp.coprime_iff_not_dvd.mp hnq.symm) hqn

/-- The genuine sifted receiver source at an arbitrary real cutoff. -/
def chenSiftedPrimeSource (N : ℕ) (z : ℝ) : Finset ℕ := by
  classical
  exact (chenPrimeReceiverSource N).filter
    (fun n => Nat.Coprime n (sieveProduct N (Nat.ceil z)))

open Classical in
theorem chenSiftedPrimeSource_eq_rough_filter (N : ℕ) (z : ℝ) :
    chenSiftedPrimeSource N z =
      (chenPrimeReceiverSource N).filter (ChenPrimeRough z) := by
  classical
  ext n
  simp only [chenSiftedPrimeSource, Finset.mem_filter]
  constructor
  · rintro ⟨hn, hs⟩
    exact ⟨hn, (chenPrimeRough_iff_coprime_sieveProduct z
      (chenPrimeReceiverSource_data hn).2.2).mpr hs⟩
  · rintro ⟨hn, hr⟩
    exact ⟨hn, (chenPrimeRough_iff_coprime_sieveProduct z
      (chenPrimeReceiverSource_data hn).2.2).mp hr⟩

/-- Unit receiver is retained for every cutoff, with no error term. -/
theorem one_mem_chenSiftedPrimeSource_iff (N : ℕ) (z : ℝ) :
    1 ∈ chenSiftedPrimeSource N z ↔ 1 < N ∧ Nat.Prime (N - 1) := by
  classical
  rw [chenSiftedPrimeSource, Finset.mem_filter]
  constructor
  · intro h
    exact (one_mem_chenPrimeReceiverSource_iff N).mp h.1
  · intro h
    exact ⟨(one_mem_chenPrimeReceiverSource_iff N).mpr h, Nat.coprime_one_left _⟩

/-- A genuine mathlib sieve of the actual additive-prime source. -/
def chenInitialBoundingSieve (N : ℕ) (z : ℝ) (hN : Even N) : BoundingSieve where
  support := chenPrimeReceiverSource N
  prodPrimes := sieveProduct N (Nat.ceil z)
  prodPrimes_squarefree := sieveProduct_squarefree N (Nat.ceil z)
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := ((chenAdditivePrimeCarrier N).card : ℝ)
  nu := halfProductDensity
  nu_mult := halfProductDensity_isMultiplicative
  nu_pos_of_prime := fun _ hp _ => halfProductDensity_pos_of_prime hp
  nu_lt_one_of_prime := fun _ hp hd =>
    halfProductDensity_lt_one_of_prime hp (two_lt_prime_of_dvd_sieveProduct hN hp hd)

theorem chenInitialBoundingSieve_totalMass_eq_sum (N : ℕ) (z : ℝ) (hN : Even N) :
    (chenInitialBoundingSieve N z hN).totalMass =
      ∑ n ∈ (chenInitialBoundingSieve N z hN).support,
        (chenInitialBoundingSieve N z hN).weights n := by
  simp [chenInitialBoundingSieve, chenPrimeReceiverSource_card]

theorem chenInitialBoundingSieve_prime_density (N : ℕ) (z : ℝ) (hN : Even N)
    {q : ℕ} (hq : Nat.Prime q) :
    (chenInitialBoundingSieve N z hN).nu q = 1 / ((q : ℝ) - 1) := by
  change 1 / (Nat.totient q : ℝ) = _
  rw [Nat.totient_prime hq, Nat.cast_sub (by have := hq.two_le; omega : 1 ≤ q),
    Nat.cast_one]

theorem chenInitialBoundingSieve_siftedSum (N : ℕ) (z : ℝ) (hN : Even N) :
    (chenInitialBoundingSieve N z hN).siftedSum =
      ((chenSiftedPrimeSource N z).card : ℝ) := by
  classical
  change (∑ n ∈ chenPrimeReceiverSource N,
      if Nat.Coprime (sieveProduct N (Nat.ceil z)) n then (1 : ℝ) else 0) = _
  simp_rw [@Nat.coprime_comm (sieveProduct N (Nat.ceil z))]
  rw [← Finset.sum_filter]
  simp [chenSiftedPrimeSource]

theorem chenInitialBoundingSieve_siftedSum_eq_Y1 (N : ℕ) (z : ℝ) (hN : Even N) :
    (chenInitialBoundingSieve N z hN).siftedSum =
      ∑ P ∈ chenAdditivePrimeCarrier N, (chenY1 (N - P) z : ℝ) := by
  classical
  change (∑ n ∈ chenPrimeReceiverSource N,
      if Nat.Coprime (sieveProduct N (Nat.ceil z)) n then (1 : ℝ) else 0) = _
  rw [sum_chenPrimeReceiverSource]
  apply Finset.sum_congr rfl
  intro P hP
  have hcop : Nat.Coprime (N - P) N :=
    (Nat.coprime_self_sub_left (mem_chenAdditivePrimeCarrier.mp hP).1.le).mpr
      (mem_chenAdditivePrimeCarrier.mp hP).2.2
  have hiff : Nat.Coprime (sieveProduct N (Nat.ceil z)) (N - P) ↔
      ChenPrimeRough z (N - P) := by
    constructor
    · intro hs
      exact (chenPrimeRough_iff_coprime_sieveProduct z hcop).mpr hs.symm
    · intro hr
      exact ((chenPrimeRough_iff_coprime_sieveProduct z hcop).mp hr).symm
  simp only [hiff]
  by_cases hr : ChenPrimeRough z (N - P)
  · simp [chenY1, hr]
  · simp [chenY1, hr]

/-- Actual Upsilon 1, with its literal manuscript exponent. -/
theorem chenUpsilon1_eq_actual_siftedSum (N : ℕ) (hN : Even N) :
    chenUpsilon1 N =
      (chenInitialBoundingSieve N ((N : ℝ) ^ (100 / 1149 : ℝ)) hN).siftedSum := by
  symm
  exact chenInitialBoundingSieve_siftedSum_eq_Y1 N _ hN

/-- Actual Upsilon 2, using the same source and the larger strict cap. -/
theorem chenUpsilon2_eq_actual_siftedSum (N : ℕ) (hN : Even N) :
    chenUpsilon2 N =
      (chenInitialBoundingSieve N ((N : ℝ) ^ (50 / 309 : ℝ)) hN).siftedSum := by
  symm
  exact chenInitialBoundingSieve_siftedSum_eq_Y1 N _ hN

theorem chenUpsilon1_eq_actual_sifted_card (N : ℕ) (hN : Even N) :
    chenUpsilon1 N =
      ((chenSiftedPrimeSource N ((N : ℝ) ^ (100 / 1149 : ℝ))).card : ℝ) := by
  rw [chenUpsilon1_eq_actual_siftedSum N hN, chenInitialBoundingSieve_siftedSum]

theorem chenUpsilon2_eq_actual_sifted_card (N : ℕ) (hN : Even N) :
    chenUpsilon2 N =
      ((chenSiftedPrimeSource N ((N : ℝ) ^ (50 / 309 : ℝ))).card : ℝ) := by
  rw [chenUpsilon2_eq_actual_siftedSum N hN, chenInitialBoundingSieve_siftedSum]

/-- Filtering an injective receiver image preserves the original prime
labels, so no multiplicity can be lost in a divisibility fibre. -/
theorem chenPrimeReceiverSource_filter_eq_image (N : ℕ) (q : ℕ → Prop)
    [DecidablePred q] :
    (chenPrimeReceiverSource N).filter q =
      ((chenAdditivePrimeCarrier N).filter (fun P => q (N - P))).image
        (fun P : ℕ => N - P) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hn, hq⟩ := Finset.mem_filter.mp hn
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_image.mpr ⟨P, Finset.mem_filter.mpr ⟨hP, hq⟩, rfl⟩
  · intro hn
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hP, hq⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨P, hP, rfl⟩, hq⟩

theorem chenAdditivePrimeCarrier_filter_dvd_eq_AP (N d : ℕ) :
    (chenAdditivePrimeCarrier N).filter (fun P => d ∣ N - P) =
      (chenAdditivePrimeCarrier N).filter (fun P => Nat.ModEq d P N) := by
  classical
  ext P
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hP, hd⟩
    exact ⟨hP, (dvd_sub_iff_modEq_of_le
      (mem_chenAdditivePrimeCarrier.mp hP).1.le).mp hd⟩
  · rintro ⟨hP, hd⟩
    exact ⟨hP, (dvd_sub_iff_modEq_of_le
      (mem_chenAdditivePrimeCarrier.mp hP).1.le).mpr hd⟩

/-- Literal set-level divisibility fibre equals the image of the actual
prime AP source, for every modulus, even zero and one. -/
theorem chenPrimeReceiverSource_divisibility_fibre (N d : ℕ) :
    (chenPrimeReceiverSource N).filter (fun n => d ∣ n) =
      ((chenAdditivePrimeCarrier N).filter (fun P => Nat.ModEq d P N)).image
        (fun P : ℕ => N - P) := by
  classical
  rw [chenPrimeReceiverSource_filter_eq_image,
    chenAdditivePrimeCarrier_filter_dvd_eq_AP]

theorem chenPrimeReceiverSource_divisibility_fibre_card (N d : ℕ) :
    ((chenPrimeReceiverSource N).filter (fun n => d ∣ n)).card =
      ((chenAdditivePrimeCarrier N).filter (fun P => Nat.ModEq d P N)).card := by
  classical
  rw [chenPrimeReceiverSource_divisibility_fibre]
  apply Finset.card_image_of_injOn
  intro P hP Q hQ heq
  exact chenPrimeReceiverSource_shift_injective
    (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hQ).1 heq

/-- The actual fibre is the inclusive prime AP count minus exactly those
prime divisors of the centre which lie in that same AP. -/
theorem chenAdditivePrimeCarrier_AP_count (N a d : ℕ) :
    (((chenAdditivePrimeCarrier N).filter (fun P => Nat.ModEq d P a)).card : ℝ) =
      chenPrimeAPCount N a d - chenCentrePrimeAPCount N a d := by
  classical
  rw [chenAdditivePrimeCarrier_eq_prefix_filter]
  have hf : ((chenPrimePrefix N).filter (fun P => ¬P ∣ N)).filter
      (fun P => Nat.ModEq d P a) =
      ((chenPrimePrefix N).filter (fun P => Nat.ModEq d P a)).filter
        (fun P => ¬P ∣ N) := by
    ext P
    simp only [Finset.mem_filter]
    tauto
  rw [hf, chen_card_filter_not_cast]
  simp only [chenPrimeAPCount, chenCentrePrimeAPCount, Finset.filter_filter]

theorem chenInitialBoundingSieve_multSum (N : ℕ) (z : ℝ) (hN : Even N) (d : ℕ) :
    (chenInitialBoundingSieve N z hN).multSum d =
      chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d := by
  classical
  change (∑ n ∈ chenPrimeReceiverSource N,
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
    chenPrimeReceiverSource_divisibility_fibre_card]
  exact chenAdditivePrimeCarrier_AP_count N N d

/-- Exact AP remainder, retaining the full centre-prime correction. -/
theorem chenInitialBoundingSieve_rem (N : ℕ) (z : ℝ) (hN : Even N) (d : ℕ) :
    (chenInitialBoundingSieve N z hN).rem d =
      chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d -
        ((chenAdditivePrimeCarrier N).card : ℝ) / (Nat.totient d : ℝ) := by
  rw [BoundingSieve.rem, chenInitialBoundingSieve_multSum]
  change chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d -
    (1 / (Nat.totient d : ℝ)) * ((chenAdditivePrimeCarrier N).card : ℝ) = _
  ring

/-- Supplier-facing error relative to the complete prime prefix. Both
centre-divisor terms are explicit, with their correct signs. -/
theorem chenInitialBoundingSieve_rem_eq_primeAP_error
    (N : ℕ) (z : ℝ) (hN : Even N) (d : ℕ) :
    (chenInitialBoundingSieve N z hN).rem d =
      (chenPrimeAPCount N N d - ((chenPrimePrefix N).card : ℝ) /
        (Nat.totient d : ℝ)) + chenPrimeDivisorCount N N / (Nat.totient d : ℝ) -
          chenCentrePrimeAPCount N N d := by
  rw [chenInitialBoundingSieve_rem, chenAdditivePrimeCarrier_card_cast]
  ring

/-- The modulus-prime term in the coprime normalization is an actual
bounded prime-divisor count, not a vanished mask. -/
theorem chenPrimePrefix_coprime_mass (N d : ℕ) :
    finiteCoprimeMass (chenPrimePrefix N) (fun _ => 1) d =
      ((chenPrimePrefix N).card : ℝ) - chenPrimeDivisorCount N d := by
  classical
  have hf : (chenPrimePrefix N).filter (fun P => Nat.Coprime P d) =
      (chenPrimePrefix N).filter (fun P => ¬P ∣ d) := by
    ext P
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hP, hc⟩
      exact ⟨hP, (mem_chenPrimePrefix.mp hP).2.coprime_iff_not_dvd.mp hc⟩
    · rintro ⟨hP, hc⟩
      exact ⟨hP, (mem_chenPrimePrefix.mp hP).2.coprime_iff_not_dvd.mpr hc⟩
  unfold finiteCoprimeMass
  rw [hf]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact chen_card_filter_not_cast (chenPrimePrefix N) (fun P => P ∣ d)

/-- Exact recentering to the full prime prefix, including both exceptional
prime sets. No prime dividing the modulus is lost from the total mass. -/
theorem chenInitialBoundingSieve_rem_eq_primitive_error
    (N : ℕ) (z : ℝ) (hN : Even N) (d : ℕ) :
    (chenInitialBoundingSieve N z hN).rem d =
      finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N d +
        (chenPrimeDivisorCount N N - chenPrimeDivisorCount N d) /
          (Nat.totient d : ℝ) - chenCentrePrimeAPCount N N d := by
  have hAP : finiteCongruenceMass (chenPrimePrefix N) (fun _ => 1) N d =
      chenPrimeAPCount N N d := by
    simp [finiteCongruenceMass, chenPrimeAPCount]
  rw [chenInitialBoundingSieve_rem_eq_primeAP_error,
    finitePrimitiveDiscrepancy, hAP, chenPrimePrefix_coprime_mass]
  ring

/-- In the actual prime source, the nonprimitive part is precisely the
prime divisors of the modulus, when the modulus is coprime to the centre. -/
theorem chenAdditivePrimeCarrier_nonprimitive_filter {N d : ℕ}
    (hdN : Nat.Coprime d N) :
    (chenAdditivePrimeCarrier N).filter (fun P => ¬Nat.Coprime P d) =
      (chenPrimePrefix N).filter (fun P => P ∣ d) := by
  classical
  ext P
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hP, hnot⟩
    obtain ⟨hPN, hp, _⟩ := mem_chenAdditivePrimeCarrier_iff_le.mp hP
    refine ⟨mem_chenPrimePrefix.mpr ⟨hPN, hp⟩, ?_⟩
    by_contra hndvd
    exact hnot (hp.coprime_iff_not_dvd.mpr hndvd)
  · rintro ⟨hP, hPd⟩
    obtain ⟨hPN, hp⟩ := mem_chenPrimePrefix.mp hP
    exact ⟨mem_chenAdditivePrimeCarrier_iff_le.mpr
      ⟨hPN, hp, hdN.of_dvd_left hPd⟩,
      fun hcop => (hp.coprime_iff_not_dvd.mp hcop) hPd⟩

/-- The actual coprime source mass differs from the total mass by the
literal modulus-prime correction, even for allowed sieve moduli. -/
theorem chenAdditivePrimeCarrier_coprime_mass {N d : ℕ}
    (hdN : Nat.Coprime d N) :
    finiteCoprimeMass (chenAdditivePrimeCarrier N) (fun _ => 1) d =
      ((chenAdditivePrimeCarrier N).card : ℝ) - chenPrimeDivisorCount N d := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := chenAdditivePrimeCarrier N) (fun P => Nat.Coprime P d)
  rw [chenAdditivePrimeCarrier_nonprimitive_filter hdN] at h
  have hR : (((chenAdditivePrimeCarrier N).filter
      (fun P => Nat.Coprime P d)).card : ℝ) + chenPrimeDivisorCount N d =
      ((chenAdditivePrimeCarrier N).card : ℝ) := by
    unfold chenPrimeDivisorCount
    exact_mod_cast h
  unfold finiteCoprimeMass
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

/-- Recentring on the actual source has a nonzero modulus-prime correction.
This identity prevents a false replacement of total by coprime mass. -/
theorem chenInitialBoundingSieve_rem_eq_source_discrepancy
    (N : ℕ) (z : ℝ) (hN : Even N) {d : ℕ} (hdN : Nat.Coprime d N) :
    (chenInitialBoundingSieve N z hN).rem d =
      finitePrimitiveDiscrepancy (chenAdditivePrimeCarrier N) (fun _ => 1) N d -
        chenPrimeDivisorCount N d / (Nat.totient d : ℝ) := by
  have hAP : finiteCongruenceMass (chenAdditivePrimeCarrier N) (fun _ => 1) N d =
      chenPrimeAPCount N N d - chenCentrePrimeAPCount N N d := by
    classical
    simpa [finiteCongruenceMass] using chenAdditivePrimeCarrier_AP_count N N d
  rw [chenInitialBoundingSieve_rem, finitePrimitiveDiscrepancy, hAP,
    chenAdditivePrimeCarrier_coprime_mass hdN]
  ring

/-- A prime in a primitive progression cannot divide its modulus. This
applies to the fibre only, and not to the whole prime source. -/
theorem chenPrimeAP_not_dvd_modulus {P a d : ℕ}
    (hP : Nat.Prime P) (hAP : Nat.ModEq d P a) (ha : Nat.Coprime a d) :
    ¬P ∣ d := by
  apply hP.coprime_iff_not_dvd.mp
  change Nat.gcd P d = 1
  rw [hAP.gcd_eq]
  exact ha

/-- Every allowed modulus gives the actual primitive residue `N`. -/
theorem chenInitial_allowed_fibre_not_dvd_modulus {N P d : ℕ} {z : ℝ}
    (hd : d ∣ sieveProduct N (Nat.ceil z))
    (hP : P ∈ chenAdditivePrimeCarrier N) (hf : d ∣ N - P) : ¬P ∣ d := by
  exact chenPrimeAP_not_dvd_modulus (mem_chenAdditivePrimeCarrier.mp hP).2.1
    ((dvd_sub_iff_modEq_of_le (mem_chenAdditivePrimeCarrier.mp hP).1.le).mp hf)
    (coprime_of_dvd_sieveProduct hd).symm

/-- Modulus one has zero exact remainder, including both corrections. -/
@[simp] theorem chenInitialBoundingSieve_rem_one (N : ℕ) (z : ℝ) (hN : Even N) :
    (chenInitialBoundingSieve N z hN).rem 1 = 0 := by
  classical
  rw [BoundingSieve.rem]
  change (∑ n ∈ chenPrimeReceiverSource N,
      if 1 ∣ n then (1 : ℝ) else 0) -
        halfProductDensity 1 * ((chenAdditivePrimeCarrier N).card : ℝ) = 0
  simp [chenPrimeReceiverSource_card]

end

end ImbalancedChen
