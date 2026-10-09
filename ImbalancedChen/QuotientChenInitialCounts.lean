import ImbalancedChen.QuotientChenFourCounts

/-!
# The actual first six terms of the repaired eleven-term Chen weight

The definitions below retain the literal quotient predicate in every summand.
Their finite carriers are the actual prime divisors of the positive receiver;
the membership theorems remove that carrier restriction and identify precisely
the manuscript's nonzero summands. The source-set equalities then prove the
first six cardinality identities, without assuming any target count identity.

For an `A`-rough receiver, removing selected prime divisors preserves
`A`-roughness. Distinct prime divisors have a product dividing the receiver,
even without squarefreeness. Thus the individual identities here hold under
the weaker hypothesis `n ≠ 0`; the final bundle specializes them to the
squarefree, ordered-cutoff setting. All upper endpoints are strict, and the
second-prime band in `Y6` includes its lower endpoint `H`. Receiver one is
included explicitly.
-/

namespace ImbalancedChen

/-- Roughness passes to an actual divisor, including divisor one. -/
theorem ChenPrimeRough.of_dvd {y : ℝ} {n m : ℕ}
    (hrough : ChenPrimeRough y n) (hd : m ∣ n) : ChenPrimeRough y m := by
  intro q hq hqm
  exact hrough q hq (hqm.trans hd)

/-- Removing a divisor of an `A`-rough receiver gives its actual quotient
indicator, rather than an indicator imposed on the original receiver. -/
theorem chenQuotient_of_rough {n b : ℕ} {A : ℝ}
    (hrough : ChenPrimeRough A n) (hd : b ∣ n) : ChenQuotient b A n := by
  refine ⟨hd, hrough.of_dvd ?_⟩
  calc
    n / b ∣ b * (n / b) := dvd_mul_left _ _
    _ = n := Nat.mul_div_cancel' hd

@[simp] theorem chenQuotient_one_iff {n : ℕ} {A : ℝ} :
    ChenQuotient 1 A n ↔ ChenPrimeRough A n := by
  simp [ChenQuotient]

/-- The divisibility bridge for two distinct selected prime factors. -/
theorem chen_two_prime_product_dvd {n p₁ p₂ : ℕ}
    (h₁ : Nat.Prime p₁) (h₂ : Nat.Prime p₂) (h₁₂ : p₁ < p₂)
    (hd₁ : p₁ ∣ n) (hd₂ : p₂ ∣ n) : p₁ * p₂ ∣ n := by
  exact ((Nat.coprime_primes h₁ h₂).mpr (ne_of_lt h₁₂)).mul_dvd_of_dvd_of_dvd hd₁ hd₂

noncomputable section

/-- The literal `Q_1(A;n)` summand. -/
def chenY1 (n : ℕ) (A : ℝ) : ℕ := by
  classical
  exact if ChenQuotient 1 A n then 1 else 0

/-- The literal `Q_1(H;n)` summand. -/
def chenY2 (n : ℕ) (H : ℝ) : ℕ := by
  classical
  exact if ChenQuotient 1 H n then 1 else 0

/-- Common actual nonzero one-prime support for `Y3` and `Y4`. -/
def chenSinglePrimeTuples (n : ℕ) (A U : ℝ) : Finset ℕ := by
  classical
  exact n.primeFactors.filter fun p =>
    A ≤ (p : ℝ) ∧ (p : ℝ) < U ∧ ChenQuotient p A n

/-- Carrier for the actual two-factor summands of `Y5` and `Y6`. -/
def chenInitialPairCarrier (n : ℕ) : Finset (ℕ × ℕ) :=
  n.primeFactors ×ˢ n.primeFactors

/-- The literal `Y5` support, with two strictly increasing factors below `H`. -/
def chenY5Tuples (n : ℕ) (A H : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (chenInitialPairCarrier n).filter fun t =>
    A ≤ (t.1 : ℝ) ∧ t.1 < t.2 ∧ (t.2 : ℝ) < H ∧
    ChenQuotient (t.1 * t.2) A n

/-- The literal `Y6` support. Equality at `H` belongs to the second factor. -/
def chenY6Tuples (n : ℕ) (A H D : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (chenInitialPairCarrier n).filter fun t =>
    A ≤ (t.1 : ℝ) ∧ (t.1 : ℝ) < H ∧ H ≤ (t.2 : ℝ) ∧ (t.2 : ℝ) < D ∧
    ChenQuotient (t.1 * t.2) A n

/-- `Y3`, with upper endpoint `T = N^(1/3)` in the manuscript. -/
def chenY3 (n : ℕ) (A T : ℝ) : ℕ := (chenSinglePrimeTuples n A T).card

/-- `Y4`, with upper endpoint `D = N^d` in the manuscript. -/
def chenY4 (n : ℕ) (A D : ℝ) : ℕ := (chenSinglePrimeTuples n A D).card

def chenY5 (n : ℕ) (A H : ℝ) : ℕ := (chenY5Tuples n A H).card

def chenY6 (n : ℕ) (A H D : ℝ) : ℕ := (chenY6Tuples n A H D).card

/-- Exact bridge to the literal one-factor summand, with no prime-factor
carrier restriction left on the right-hand side. -/
theorem mem_chenSinglePrimeTuples_iff {n p : ℕ} {A U : ℝ} (hn : n ≠ 0) :
    p ∈ chenSinglePrimeTuples n A U ↔
      Nat.Prime p ∧ A ≤ (p : ℝ) ∧ (p : ℝ) < U ∧ ChenQuotient p A n := by
  classical
  rw [chenSinglePrimeTuples, Finset.mem_filter]
  constructor
  · rintro ⟨hpf, hA, hU, hQ⟩
    obtain ⟨hp, _, _⟩ := Nat.mem_primeFactors.mp hpf
    exact ⟨hp, hA, hU, hQ⟩
  · rintro ⟨hp, hA, hU, hQ⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp, hQ.1, hn⟩, hA, hU, hQ⟩

theorem mem_chenInitialPairCarrier {n p₁ p₂ : ℕ} (hn : n ≠ 0) :
    (p₁, p₂) ∈ chenInitialPairCarrier n ↔
      (Nat.Prime p₁ ∧ p₁ ∣ n) ∧ (Nat.Prime p₂ ∧ p₂ ∣ n) := by
  rw [chenInitialPairCarrier, Finset.mem_product]
  constructor
  · rintro ⟨hpf₁, hpf₂⟩
    obtain ⟨hp₁, hd₁, _⟩ := Nat.mem_primeFactors.mp hpf₁
    obtain ⟨hp₂, hd₂, _⟩ := Nat.mem_primeFactors.mp hpf₂
    exact ⟨⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩⟩
  · rintro ⟨⟨hp₁, hd₁⟩, ⟨hp₂, hd₂⟩⟩
    exact ⟨Nat.mem_primeFactors.mpr ⟨hp₁, hd₁, hn⟩,
      Nat.mem_primeFactors.mpr ⟨hp₂, hd₂, hn⟩⟩

/-- Exact bridge to the manuscript's `Y5` summand. -/
theorem mem_chenY5Tuples_iff {n p₁ p₂ : ℕ} {A H : ℝ} (hn : n ≠ 0) :
    (p₁, p₂) ∈ chenY5Tuples n A H ↔
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ A ≤ (p₁ : ℝ) ∧ p₁ < p₂ ∧
      (p₂ : ℝ) < H ∧ ChenQuotient (p₁ * p₂) A n := by
  classical
  rw [chenY5Tuples, Finset.mem_filter, mem_chenInitialPairCarrier hn]
  constructor
  · rintro ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩, hrest⟩
    exact ⟨h₁, h₂, hrest⟩
  · rintro ⟨h₁, h₂, hA, h₁₂, hH, hQ⟩
    refine ⟨⟨⟨h₁, ?_⟩, ⟨h₂, ?_⟩⟩, hA, h₁₂, hH, hQ⟩
    · exact (dvd_mul_right p₁ p₂).trans hQ.1
    · exact (dvd_mul_left p₂ p₁).trans hQ.1

/-- Exact bridge to the manuscript's `Y6` summand. Strict ordering of the
factors follows from `p₁ < H ≤ p₂`, so no extra restriction is introduced. -/
theorem mem_chenY6Tuples_iff {n p₁ p₂ : ℕ} {A H D : ℝ} (hn : n ≠ 0) :
    (p₁, p₂) ∈ chenY6Tuples n A H D ↔
      Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ A ≤ (p₁ : ℝ) ∧ (p₁ : ℝ) < H ∧
      H ≤ (p₂ : ℝ) ∧ (p₂ : ℝ) < D ∧ ChenQuotient (p₁ * p₂) A n := by
  classical
  rw [chenY6Tuples, Finset.mem_filter, mem_chenInitialPairCarrier hn]
  constructor
  · rintro ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩, hrest⟩
    exact ⟨h₁, h₂, hrest⟩
  · rintro ⟨h₁, h₂, hA, h₁H, hH₂, h₂D, hQ⟩
    refine ⟨⟨⟨h₁, ?_⟩, ⟨h₂, ?_⟩⟩, hA, h₁H, hH₂, h₂D, hQ⟩
    · exact (dvd_mul_right p₁ p₂).trans hQ.1
    · exact (dvd_mul_left p₂ p₁).trans hQ.1

/-- The one-factor source bijection is the identity on the actual prime
values; quotient roughness follows from roughness of the receiver. -/
theorem chenSinglePrimeTuples_eq_primesBelow {n : ℕ} {A U : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenSinglePrimeTuples n A U = chenPrimesBelow n U := by
  classical
  ext p
  rw [mem_chenSinglePrimeTuples_iff hn, mem_chenPrimesBelow hn]
  constructor
  · rintro ⟨hp, _, hU, hQ⟩
    exact ⟨hp, hQ.1, hU⟩
  · rintro ⟨hp, hd, hU⟩
    exact ⟨hp, hrough p hp hd, hU, chenQuotient_of_rough hrough hd⟩

/-- The actual `Y5` source is exactly the strictly ordered pairs from the
prime divisors below `H`. This equality supplies both directions of the
source bijection, not an assumed count identity. -/
theorem chenY5Tuples_eq_ordered_pairs {n : ℕ} {A H : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenY5Tuples n A H =
      ((chenPrimesBelow n H) ×ˢ (chenPrimesBelow n H)).filter
        (fun t : ℕ × ℕ => t.1 < t.2) := by
  classical
  ext ⟨p₁, p₂⟩
  rw [mem_chenY5Tuples_iff hn, Finset.mem_filter, Finset.mem_product,
    mem_chenPrimesBelow hn, mem_chenPrimesBelow hn]
  constructor
  · rintro ⟨h₁, h₂, _, h₁₂, h₂H, hQ⟩
    have hd₁ : p₁ ∣ n := (dvd_mul_right p₁ p₂).trans hQ.1
    have hd₂ : p₂ ∣ n := (dvd_mul_left p₂ p₁).trans hQ.1
    have h₁H : (p₁ : ℝ) < H := lt_trans (by exact_mod_cast h₁₂) h₂H
    exact ⟨⟨⟨h₁, hd₁, h₁H⟩, ⟨h₂, hd₂, h₂H⟩⟩, h₁₂⟩
  · rintro ⟨⟨⟨h₁, hd₁, _⟩, ⟨h₂, hd₂, h₂H⟩⟩, h₁₂⟩
    exact ⟨h₁, h₂, hrough p₁ h₁ hd₁, h₁₂, h₂H,
      chenQuotient_of_rough hrough (chen_two_prime_product_dvd h₁ h₂ h₁₂ hd₁ hd₂)⟩

/-- The actual `Y6` source is the entire Cartesian product of factors below
`H` and factors in `[H,D)`. Their strict ordering and distinctness are
consequences of the endpoints. -/
theorem chenY6Tuples_eq_product {n : ℕ} {A H D : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenY6Tuples n A H D = (chenPrimesBelow n H) ×ˢ (chenPrimeBand n H D) := by
  classical
  ext ⟨p₁, p₂⟩
  rw [mem_chenY6Tuples_iff hn, Finset.mem_product,
    mem_chenPrimesBelow hn, mem_chenPrimeBand hn]
  constructor
  · rintro ⟨h₁, h₂, _, h₁H, hH₂, h₂D, hQ⟩
    exact ⟨⟨h₁, (dvd_mul_right p₁ p₂).trans hQ.1, h₁H⟩,
      ⟨h₂, (dvd_mul_left p₂ p₁).trans hQ.1, hH₂, h₂D⟩⟩
  · rintro ⟨⟨h₁, hd₁, h₁H⟩, ⟨h₂, hd₂, hH₂, h₂D⟩⟩
    have h₁₂ : p₁ < p₂ := by exact_mod_cast (lt_of_lt_of_le h₁H hH₂)
    exact ⟨h₁, h₂, hrough p₁ h₁ hd₁, h₁H, hH₂, h₂D,
      chenQuotient_of_rough hrough (chen_two_prime_product_dvd h₁ h₂ h₁₂ hd₁ hd₂)⟩

/-- Absence of prime divisors strictly below the cutoff is exactly inclusive
prime-divisor roughness, also at receiver one. -/
theorem chenPrimeRough_iff_primesBelow_card_zero {n : ℕ} {H : ℝ}
    (hn : n ≠ 0) : ChenPrimeRough H n ↔ (chenPrimesBelow n H).card = 0 := by
  classical
  constructor
  · intro hrough
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hprime, hd, hH⟩ := (mem_chenPrimesBelow hn).mp hp
    exact (not_lt_of_ge (hrough p hprime hd)) hH
  · intro hcard p hprime hd
    by_contra hH
    have hp : p ∈ chenPrimesBelow n H :=
      (mem_chenPrimesBelow hn).mpr ⟨hprime, hd, lt_of_not_ge hH⟩
    rw [Finset.card_eq_zero.mp hcard] at hp
    exact Finset.notMem_empty p hp

/-- Literal `Y1 = 1` on rough receivers. -/
theorem chenY1_eq_one {n : ℕ} {A : ℝ} (hrough : ChenPrimeRough A n) :
    chenY1 n A = 1 := by
  classical
  simp [chenY1, hrough]

/-- Literal `Y2` is the indicator that no prime factor is strictly below `H`. -/
theorem chenY2_eq_indicator {n : ℕ} {H : ℝ} (hn : n ≠ 0) :
    chenY2 n H = if (chenPrimesBelow n H).card = 0 then 1 else 0 := by
  classical
  simp only [chenY2, chenQuotient_one_iff, chenPrimeRough_iff_primesBelow_card_zero hn]

theorem chenY3_eq_card {n : ℕ} {A T : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenY3 n A T = (chenPrimesBelow n T).card := by
  unfold chenY3
  rw [chenSinglePrimeTuples_eq_primesBelow hn hrough]

theorem chenY4_eq_card {n : ℕ} {A D : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenY4 n A D = (chenPrimesBelow n D).card := by
  unfold chenY4
  rw [chenSinglePrimeTuples_eq_primesBelow hn hrough]

theorem chenY5_eq_choose {n : ℕ} {A H : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenY5 n A H = (chenPrimesBelow n H).card.choose 2 := by
  classical
  unfold chenY5
  rw [chenY5Tuples_eq_ordered_pairs hn hrough]
  exact Finset.card_product_filter_lt

theorem chenY6_eq_mul_band {n : ℕ} {A H D : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) :
    chenY6 n A H D = (chenPrimesBelow n H).card * (chenPrimeBand n H D).card := by
  unfold chenY6
  rw [chenY6Tuples_eq_product hn hrough]
  exact Finset.card_product _ _

/-- The exact `r(s-r)` count uses the full second-prime interval `[H,D)`. -/
theorem chenY6_eq_mul_sub {n : ℕ} {A H D : ℝ}
    (hn : n ≠ 0) (hrough : ChenPrimeRough A n) (hHD : H ≤ D) :
    chenY6 n A H D = (chenPrimesBelow n H).card *
      ((chenPrimesBelow n D).card - (chenPrimesBelow n H).card) := by
  rw [chenY6_eq_mul_band hn hrough, chenPrimeBand_card hn hHD]

/-- Ordered real cutoffs give ordered actual prime-divisor counts. -/
theorem chenPrimesBelow_card_mono {n : ℕ} {H D : ℝ} (hHD : H ≤ D) :
    (chenPrimesBelow n H).card ≤ (chenPrimesBelow n D).card := by
  classical
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpf, hpH⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hpf, lt_of_lt_of_le hpH hHD⟩

/-- All six manuscript identities in the squarefree ordered-cutoff setting.
The source has been proved from actual quotient summands, and no target
identity or arbitrary count variable is assumed. -/
theorem chen_first_six_identities {n : ℕ} {A H D T : ℝ}
    (hn : Squarefree n) (hrough : ChenPrimeRough A n)
    (_hApos : 0 < A) (_hAH : A ≤ H) (hHD : H ≤ D) (hDT : D ≤ T) :
    let r := (chenPrimesBelow n H).card
    let s := (chenPrimesBelow n D).card
    let t := (chenPrimesBelow n T).card
    r ≤ s ∧ s ≤ t ∧
      chenY1 n A = 1 ∧ chenY2 n H = (if r = 0 then 1 else 0) ∧
      chenY3 n A T = t ∧ chenY4 n A D = s ∧
      chenY5 n A H = r.choose 2 ∧ chenY6 n A H D = r * (s - r) := by
  dsimp only
  exact ⟨chenPrimesBelow_card_mono hHD, chenPrimesBelow_card_mono hDT,
    chenY1_eq_one hrough, chenY2_eq_indicator hn.ne_zero,
    chenY3_eq_card hn.ne_zero hrough, chenY4_eq_card hn.ne_zero hrough,
    chenY5_eq_choose hn.ne_zero hrough, chenY6_eq_mul_sub hn.ne_zero hrough hHD⟩

/-- At receiver one both zero-factor indicators are one and every actual
prime-tuple sum is zero, for arbitrary real cutoffs. -/
theorem chen_first_six_at_one (A H D T : ℝ) :
    chenY1 1 A = 1 ∧ chenY2 1 H = 1 ∧ chenY3 1 A T = 0 ∧
      chenY4 1 A D = 0 ∧ chenY5 1 A H = 0 ∧ chenY6 1 A H D = 0 := by
  classical
  simp [chenY1, chenY2, chenY3, chenY4, chenY5, chenY6,
    chenSinglePrimeTuples, chenY5Tuples, chenY6Tuples, chenInitialPairCarrier]

end

end ImbalancedChen
