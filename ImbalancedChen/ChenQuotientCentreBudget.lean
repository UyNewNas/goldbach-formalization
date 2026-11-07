import ImbalancedChen.ChenQuotientSieveRemainders
import ImbalancedChen.ChenInitialCorrectionBudget

/-!
# Paying the pooled selected-multiplier centre corrections

Both literal correction counts are retained. The new input is finite
incidence pooling: after summing over centre primes `P ∣ N`, selected
single primes dividing the positive receiver `N - P` lie in its prime
factors, and selected ordered pairs lie in the square of that carrier.
Consequently the total incidence is at most `(log N / log 2)^2` for each
single selector and `(log N / log 2)^3` for each pair selector.

On positive moduli the complete cost `C(b)/phi(d) + C(b*d)` is at most
`2*C(b)`. Arbitrary row-dependent modulus sets in `Icc 1 D` therefore
cost at most `2*D` times the pooled incidence. For all four actual terms,
`D <= sqrt N` gives an explicit `sqrt N * (log N)^3` bound and arbitrary
fixed logarithmic accuracy. No prime-distribution hypothesis is used.

The prime-centre endpoint is not discarded: nonprimality is explicit in
the incidence bound and is derived from evenness and `N >= 4` in the
actual application. Modulus one and empty modulus families are retained.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

/-- The actual prime divisors of the centre in the inclusive prefix. -/
def chenCentrePrimeCarrier (N : ℕ) : Finset ℕ :=
  (chenPrimePrefix N).filter (fun P => P ∣ N)

@[simp] theorem mem_chenCentrePrimeCarrier {N P : ℕ} :
    P ∈ chenCentrePrimeCarrier N ↔ P ≤ N ∧ Nat.Prime P ∧ P ∣ N := by
  simp only [chenCentrePrimeCarrier, Finset.mem_filter, mem_chenPrimePrefix]
  tauto

/-- At a nonprime centre every centre-prime receiver is genuinely positive.
This excludes the zero receiver by proof, not by changing the prefix. -/
theorem chenCentrePrimeCarrier_sub_pos {N P : ℕ} (hNP : ¬Nat.Prime N)
    (hP : P ∈ chenCentrePrimeCarrier N) : 0 < N - P := by
  obtain ⟨hPN, hp, _⟩ := mem_chenCentrePrimeCarrier.mp hP
  have hne : P ≠ N := fun heq => hNP (heq ▸ hp)
  omega

/-- The centre AP correction is exactly a receiver-divisibility incidence.
This remains valid at zero and unit moduli and at a prime centre. -/
theorem chenCentrePrimeAPCount_eq_filter_dvd (N k : ℕ) :
    chenCentrePrimeAPCount N N k =
      (((chenCentrePrimeCarrier N).filter (fun P => k ∣ N - P)).card : ℝ) := by
  have hf : (chenPrimePrefix N).filter (fun P => Nat.ModEq k P N ∧ P ∣ N) =
      (chenCentrePrimeCarrier N).filter (fun P => k ∣ N - P) := by
    ext P
    constructor
    · intro hP
      obtain ⟨hP, hAP, hdiv⟩ := Finset.mem_filter.mp hP
      have hPN := (mem_chenPrimePrefix.mp hP).1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨hP, hdiv⟩,
          (dvd_sub_iff_modEq_of_le hPN).mpr hAP⟩
    · intro hP
      obtain ⟨hP, hdiv⟩ := Finset.mem_filter.mp hP
      obtain ⟨hpref, hPN⟩ := Finset.mem_filter.mp hP
      exact Finset.mem_filter.mpr ⟨hpref,
        (dvd_sub_iff_modEq_of_le (mem_chenPrimePrefix.mp hpref).1).mp hdiv, hPN⟩
  unfold chenCentrePrimeAPCount
  rw [hf]

/-- Multiplication of the modulus only reduces the actual correction. -/
theorem chenCentrePrimeAPCount_mul_le (N b d : ℕ) :
    chenCentrePrimeAPCount N N (b * d) ≤ chenCentrePrimeAPCount N N b := by
  rw [chenCentrePrimeAPCount_eq_filter_dvd, chenCentrePrimeAPCount_eq_filter_dvd]
  have hsub : (chenCentrePrimeCarrier N).filter (fun P => b * d ∣ N - P) ⊆
      (chenCentrePrimeCarrier N).filter (fun P => b ∣ N - P) := by
    intro P hP
    obtain ⟨hP, hdiv⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_filter.mpr ⟨hP, (dvd_mul_right b d).trans hdiv⟩
  exact_mod_cast Finset.card_le_card hsub

/-- Literal total centre incidence over labelled selected multipliers. -/
def chenSelectedCentreMass {α : Type*} (N : ℕ) (T : Finset α) (b : α → ℕ) : ℝ :=
  ∑ t ∈ T, chenCentrePrimeAPCount N N (b t)

/-- Finite Fubini pools centre incidences without collapsing outer labels. -/
theorem chenSelectedCentreMass_eq_incidence {α : Type*} [DecidableEq α]
    (N : ℕ) (T : Finset α) (b : α → ℕ) :
    chenSelectedCentreMass N T b =
      ∑ P ∈ chenCentrePrimeCarrier N,
        ((T.filter (fun t => b t ∣ N - P)).card : ℝ) := by
  unfold chenSelectedCentreMass
  simp_rw [chenCentrePrimeAPCount_eq_filter_dvd]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  exact Finset.sum_comm

/-- Every selected divisor prime is an actual prime factor of a nonzero
receiver. Selector cutoffs and centre masks remain unchanged. -/
theorem chenSinglePrimeSelector_filter_dvd_card_le {N n : ℕ} (hn : n ≠ 0)
    (A U : ℝ) :
    ((chenSinglePrimeSelector N A U).filter (fun p => p ∣ n)).card ≤
      n.primeFactors.card := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp, hdiv⟩ := Finset.mem_filter.mp hp
  have hprime := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1
  exact Nat.mem_primeFactors.mpr ⟨hprime, hdiv, hn⟩

/-- The fifth term's ordered pair incidence lies in the square of the
actual receiver prime-factor carrier, including repeated receiver factors. -/
theorem chenY5PrimeSelector_filter_dvd_card_le {N n : ℕ} (hn : n ≠ 0)
    (A H : ℝ) :
    ((chenY5PrimeSelector N A H).filter (fun t => t.1 * t.2 ∣ n)).card ≤
      n.primeFactors.card ^ 2 := by
  have hsub : (chenY5PrimeSelector N A H).filter (fun t => t.1 * t.2 ∣ n) ⊆
      n.primeFactors ×ˢ n.primeFactors := by
    intro t ht
    obtain ⟨ht, hdiv⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
    exact Finset.mem_product.mpr
      ⟨Nat.mem_primeFactors.mpr
        ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1, (dvd_mul_right t.1 t.2).trans hdiv, hn⟩,
        Nat.mem_primeFactors.mpr
        ⟨(mem_chenAdditivePrimeCarrier.mp h₂).2.1, (dvd_mul_left t.2 t.1).trans hdiv, hn⟩⟩
  simpa only [Finset.card_product, pow_two] using Finset.card_le_card hsub

/-- The sixth term's full half-open band has the same incidence bound.
Its ordered pair labels are retained, rather than mapped to a set of products. -/
theorem chenY6PrimeSelector_filter_dvd_card_le {N n : ℕ} (hn : n ≠ 0)
    (A H U : ℝ) :
    ((chenY6PrimeSelector N A H U).filter (fun t => t.1 * t.2 ∣ n)).card ≤
      n.primeFactors.card ^ 2 := by
  have hsub : (chenY6PrimeSelector N A H U).filter (fun t => t.1 * t.2 ∣ n) ⊆
      n.primeFactors ×ˢ n.primeFactors := by
    intro t ht
    obtain ⟨ht, hdiv⟩ := Finset.mem_filter.mp ht
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp ht).1
    exact Finset.mem_product.mpr
      ⟨Nat.mem_primeFactors.mpr
        ⟨(mem_chenAdditivePrimeCarrier.mp h₁).2.1, (dvd_mul_right t.1 t.2).trans hdiv, hn⟩,
        Nat.mem_primeFactors.mpr
        ⟨(mem_chenAdditivePrimeCarrier.mp h₂).2.1, (dvd_mul_left t.2 t.1).trans hdiv, hn⟩⟩
  simpa only [Finset.card_product, pow_two] using Finset.card_le_card hsub

/-- The proved logarithmic distinct-prime bound is uniform below `N`. -/
theorem chen_primeFactors_card_le_log_of_le {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (n.primeFactors.card : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
  refine (chen_primeFactors_card_le_log hn).trans ?_
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by exact_mod_cast hn) (by exact_mod_cast hnN))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

/-- A bound for each centre-prime incidence fibre pays the literal mass
with the actual number of centre prime divisors. -/
theorem chenSelectedCentreMass_le_of_incidence_bound {α : Type*} [DecidableEq α]
    (N : ℕ) (T : Finset α) (b : α → ℕ) (K : ℝ)
    (hK : ∀ P ∈ chenCentrePrimeCarrier N,
      ((T.filter (fun t => b t ∣ N - P)).card : ℝ) ≤ K) :
    chenSelectedCentreMass N T b ≤ chenPrimeDivisorCount N N * K := by
  rw [chenSelectedCentreMass_eq_incidence]
  calc
    _ ≤ ∑ _P ∈ chenCentrePrimeCarrier N, K := Finset.sum_le_sum hK
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl

/-- Pooled one-prime corrections cost two logarithms, independently of
the size of the outer selector and of its real endpoints. -/
theorem chenSinglePrimeSelector_centreMass_le_log_sq {N : ℕ}
    (hN : 0 < N) (hNP : ¬Nat.Prime N) (A U : ℝ) :
    chenSelectedCentreMass N (chenSinglePrimeSelector N A U) id ≤
      (Real.log (N : ℝ) / Real.log 2) ^ 2 := by
  let L : ℝ := Real.log (N : ℝ) / Real.log 2
  have hL : 0 ≤ L := div_nonneg (Real.log_natCast_nonneg N)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hinc : ∀ P ∈ chenCentrePrimeCarrier N,
      (((chenSinglePrimeSelector N A U).filter (fun p => id p ∣ N - P)).card : ℝ) ≤ L := by
    intro P hP
    have hn := chenCentrePrimeCarrier_sub_pos hNP hP
    have hcard : (((chenSinglePrimeSelector N A U).filter
        (fun p => p ∣ N - P)).card : ℝ) ≤ ((N - P).primeFactors.card : ℝ) := by
      exact_mod_cast chenSinglePrimeSelector_filter_dvd_card_le hn.ne' A U
    exact hcard.trans (chen_primeFactors_card_le_log_of_le hn (Nat.sub_le N P))
  calc
    _ ≤ chenPrimeDivisorCount N N * L :=
      chenSelectedCentreMass_le_of_incidence_bound N _ id L hinc
    _ ≤ L * L := mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N hN) hL
    _ = _ := by dsimp [L]; ring

/-- Pooled fifth-term corrections cost three logarithms. -/
theorem chenY5PrimeSelector_centreMass_le_log_cube {N : ℕ}
    (hN : 0 < N) (hNP : ¬Nat.Prime N) (A H : ℝ) :
    chenSelectedCentreMass N (chenY5PrimeSelector N A H) (fun t => t.1 * t.2) ≤
      (Real.log (N : ℝ) / Real.log 2) ^ 3 := by
  let L : ℝ := Real.log (N : ℝ) / Real.log 2
  have hinc : ∀ P ∈ chenCentrePrimeCarrier N,
      (((chenY5PrimeSelector N A H).filter (fun t => t.1 * t.2 ∣ N - P)).card : ℝ) ≤ L ^ 2 := by
    intro P hP
    have hn := chenCentrePrimeCarrier_sub_pos hNP hP
    have hcard : (((chenY5PrimeSelector N A H).filter
        (fun t => t.1 * t.2 ∣ N - P)).card : ℝ) ≤
          ((N - P).primeFactors.card : ℝ) ^ 2 := by
      exact_mod_cast chenY5PrimeSelector_filter_dvd_card_le hn.ne' A H
    exact hcard.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (chen_primeFactors_card_le_log_of_le hn (Nat.sub_le N P)) 2)
  calc
    _ ≤ chenPrimeDivisorCount N N * L ^ 2 :=
      chenSelectedCentreMass_le_of_incidence_bound N _ _ (L ^ 2) hinc
    _ ≤ L * L ^ 2 :=
      mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N hN) (sq_nonneg L)
    _ = _ := by dsimp [L]; ring

/-- Pooled sixth-term corrections retain the full literal second band. -/
theorem chenY6PrimeSelector_centreMass_le_log_cube {N : ℕ}
    (hN : 0 < N) (hNP : ¬Nat.Prime N) (A H U : ℝ) :
    chenSelectedCentreMass N (chenY6PrimeSelector N A H U) (fun t => t.1 * t.2) ≤
      (Real.log (N : ℝ) / Real.log 2) ^ 3 := by
  let L : ℝ := Real.log (N : ℝ) / Real.log 2
  have hinc : ∀ P ∈ chenCentrePrimeCarrier N,
      (((chenY6PrimeSelector N A H U).filter (fun t => t.1 * t.2 ∣ N - P)).card : ℝ) ≤ L ^ 2 := by
    intro P hP
    have hn := chenCentrePrimeCarrier_sub_pos hNP hP
    have hcard : (((chenY6PrimeSelector N A H U).filter
        (fun t => t.1 * t.2 ∣ N - P)).card : ℝ) ≤
          ((N - P).primeFactors.card : ℝ) ^ 2 := by
      exact_mod_cast chenY6PrimeSelector_filter_dvd_card_le hn.ne' A H U
    exact hcard.trans (pow_le_pow_left₀ (Nat.cast_nonneg _)
      (chen_primeFactors_card_le_log_of_le hn (Nat.sub_le N P)) 2)
  calc
    _ ≤ chenPrimeDivisorCount N N * L ^ 2 :=
      chenSelectedCentreMass_le_of_incidence_bound N _ _ (L ^ 2) hinc
    _ ≤ L * L ^ 2 :=
      mul_le_mul_of_nonneg_right (chenPrimeDivisorCount_le_log N hN) (sq_nonneg L)
    _ = _ := by dsimp [L]; ring

/-- Both centre terms are paid, including the conservative cost at `d=1`.
Only positivity of the modulus is needed for this elementary majorant. -/
theorem chenQuotientCentreCost_le_two_mul (N b : ℕ) {d : ℕ} (hd : 0 < d) :
    chenQuotientCentreCost N b d ≤ 2 * chenCentrePrimeAPCount N N b := by
  have hphi : (1 : ℝ) ≤ (Nat.totient d : ℝ) := by
    exact_mod_cast (show 1 ≤ Nat.totient d from Nat.totient_pos.mpr hd)
  have hdiv : chenCentrePrimeAPCount N N b / (Nat.totient d : ℝ) ≤
      chenCentrePrimeAPCount N N b := by
    exact div_le_self (chenCentrePrimeAPCount_nonneg N N b) hphi
  unfold chenQuotientCentreCost
  have hsub := chenCentrePrimeAPCount_mul_le N b d
  linarith

/-- Positive selected moduli in the inclusive cap have at most `D` labels,
including the empty cap `D=0`. -/
theorem chenQuotientCentreCost_sum_le_two_cap (N b D : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 D) :
    (∑ d ∈ S, chenQuotientCentreCost N b d) ≤
      2 * (D : ℝ) * chenCentrePrimeAPCount N N b := by
  have hcard : (S.card : ℝ) ≤ (D : ℝ) := by
    have hc : S.card ≤ D := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hS
    exact_mod_cast hc
  calc
    _ ≤ ∑ _d ∈ S, 2 * chenCentrePrimeAPCount N N b := by
      apply Finset.sum_le_sum
      intro d hd
      exact chenQuotientCentreCost_le_two_mul N b (Finset.mem_Icc.mp (hS hd)).1
    _ = (S.card : ℝ) * (2 * chenCentrePrimeAPCount N N b) := by simp
    _ ≤ (D : ℝ) * (2 * chenCentrePrimeAPCount N N b) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (by norm_num) (chenCentrePrimeAPCount_nonneg N N b))
    _ = _ := by ring

/-- Actual full correction cost for arbitrary row-dependent modulus sets.
Outer labels and their multiplicities are retained. -/
def chenSelectedCentreCost {α : Type*} (N : ℕ) (T : Finset α)
    (b : α → ℕ) (S : α → Finset ℕ) : ℝ :=
  ∑ t ∈ T, ∑ d ∈ S t, chenQuotientCentreCost N (b t) d

/-- Pool before estimating: no cardinality of the full outer selector
appears in this payment. The modulus cap may vary within each row. -/
theorem chenSelectedCentreCost_le_mass {α : Type*} [DecidableEq α]
    (N D : ℕ) (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (hS : ∀ t ∈ T, S t ⊆ Finset.Icc 1 D) :
    chenSelectedCentreCost N T b S ≤ 2 * (D : ℝ) * chenSelectedCentreMass N T b := by
  unfold chenSelectedCentreCost chenSelectedCentreMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  exact chenQuotientCentreCost_sum_le_two_cap N (b t) D (S t) (hS t ht)

theorem chenSinglePrimeSelector_centreCost_le_log_sq {N D : ℕ}
    (hN : 0 < N) (hNP : ¬Nat.Prime N) (A U : ℝ) (S : ℕ → Finset ℕ)
    (hS : ∀ p ∈ chenSinglePrimeSelector N A U, S p ⊆ Finset.Icc 1 D) :
    chenSelectedCentreCost N (chenSinglePrimeSelector N A U) id S ≤
      2 * (D : ℝ) * (Real.log (N : ℝ) / Real.log 2) ^ 2 := by
  exact (chenSelectedCentreCost_le_mass N D _ id S hS).trans
    (mul_le_mul_of_nonneg_left (chenSinglePrimeSelector_centreMass_le_log_sq hN hNP A U)
      (by positivity))

theorem chenY5PrimeSelector_centreCost_le_log_cube {N D : ℕ}
    (hN : 0 < N) (hNP : ¬Nat.Prime N) (A H : ℝ) (S : (ℕ × ℕ) → Finset ℕ)
    (hS : ∀ t ∈ chenY5PrimeSelector N A H, S t ⊆ Finset.Icc 1 D) :
    chenSelectedCentreCost N (chenY5PrimeSelector N A H) (fun t => t.1 * t.2) S ≤
      2 * (D : ℝ) * (Real.log (N : ℝ) / Real.log 2) ^ 3 := by
  exact (chenSelectedCentreCost_le_mass N D _ _ S hS).trans
    (mul_le_mul_of_nonneg_left (chenY5PrimeSelector_centreMass_le_log_cube hN hNP A H)
      (by positivity))

theorem chenY6PrimeSelector_centreCost_le_log_cube {N D : ℕ}
    (hN : 0 < N) (hNP : ¬Nat.Prime N) (A H U : ℝ) (S : (ℕ × ℕ) → Finset ℕ)
    (hS : ∀ t ∈ chenY6PrimeSelector N A H U, S t ⊆ Finset.Icc 1 D) :
    chenSelectedCentreCost N (chenY6PrimeSelector N A H U) (fun t => t.1 * t.2) S ≤
      2 * (D : ℝ) * (Real.log (N : ℝ) / Real.log 2) ^ 3 := by
  exact (chenSelectedCentreCost_le_mass N D _ _ S hS).trans
    (mul_le_mul_of_nonneg_left (chenY6PrimeSelector_centreMass_le_log_cube hN hNP A H U)
      (by positivity))

/-- All four literal selected-multiplier costs, with unit absolute outer
coefficients as in the third through sixth terms of the Chen weight. -/
def chenUpsilon36CentreCost (N : ℕ) (S₃ S₄ : ℕ → Finset ℕ)
    (S₅ S₆ : (ℕ × ℕ) → Finset ℕ) : ℝ :=
  chenSelectedCentreCost N
      (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))
      id S₃ +
    chenSelectedCentreCost N
      (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) id S₄ +
    chenSelectedCentreCost N
      (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)))
      (fun t => t.1 * t.2) S₅ +
    chenSelectedCentreCost N
      (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))))
      (fun t => t.1 * t.2) S₆

/-- Large even centres are nonprime, justifying positive exceptional
receivers in the final actual application. -/
theorem chen_not_prime_of_even_four_le {N : ℕ} (hN : Even N) (hN4 : 4 ≤ N) :
    ¬Nat.Prime N := by
  intro hp
  have heq : 2 = N := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hN.two_dvd
  omega

/-- A finite pooled bound for all four actual selectors. The row sets
may differ with every selected prime or pair; only the common cap is used. -/
theorem chenUpsilon36CentreCost_le_eight_cap_log_cube {N D : ℕ}
    (hN : Even N) (hN4 : 4 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (S₃ S₄ : ℕ → Finset ℕ) (S₅ S₆ : (ℕ × ℕ) → Finset ℕ)
    (hS₃ : ∀ p, S₃ p ⊆ Finset.Icc 1 D) (hS₄ : ∀ p, S₄ p ⊆ Finset.Icc 1 D)
    (hS₅ : ∀ t, S₅ t ⊆ Finset.Icc 1 D) (hS₆ : ∀ t, S₆ t ⊆ Finset.Icc 1 D) :
    chenUpsilon36CentreCost N S₃ S₄ S₅ S₆ ≤
      8 * (D : ℝ) * (Real.log (N : ℝ) / Real.log 2) ^ 3 := by
  have hpos : 0 < N := by omega
  have hNP := chen_not_prime_of_even_four_le hN hN4
  let L : ℝ := Real.log (N : ℝ) / Real.log 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htwo1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hL : 1 ≤ L := (le_div_iff₀ htwo).mpr (by simpa using htwo1.trans hlog)
  have hpow : L ^ 2 ≤ L ^ 3 := by
    have h := mul_nonneg (sub_nonneg.mpr hL) (sq_nonneg L)
    nlinarith
  have h₃ := chenSinglePrimeSelector_centreCost_le_log_sq hpos hNP
    ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) S₃ (fun p _ => hS₃ p)
  have h₄ := chenSinglePrimeSelector_centreCost_le_log_sq hpos hNP
    ((N : ℝ) ^ (100 / 1149 : ℝ))
    ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) S₄ (fun p _ => hS₄ p)
  have h₅ := chenY5PrimeSelector_centreCost_le_log_cube hpos hNP
    ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)) S₅ (fun t _ => hS₅ t)
  have h₆ := chenY6PrimeSelector_centreCost_le_log_cube hpos hNP
    ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))
    ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))) S₆ (fun t _ => hS₆ t)
  have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * (D : ℝ))
  change _ ≤ 8 * (D : ℝ) * L ^ 3
  change _ ≤ 2 * (D : ℝ) * L ^ 2 at h₃ h₄
  change _ ≤ 2 * (D : ℝ) * L ^ 3 at h₅ h₆
  unfold chenUpsilon36CentreCost
  linarith

/-- The actual selected correction cost is power-saving uniformly in
all four row-dependent modulus families below the square-root level. -/
theorem chenUpsilon36CentreCost_le_sqrt_log_cube {N D : ℕ}
    (hN : Even N) (hN4 : 4 ≤ N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hD : (D : ℝ) ≤ Real.sqrt (N : ℝ))
    (S₃ S₄ : ℕ → Finset ℕ) (S₅ S₆ : (ℕ × ℕ) → Finset ℕ)
    (hS₃ : ∀ p, S₃ p ⊆ Finset.Icc 1 D) (hS₄ : ∀ p, S₄ p ⊆ Finset.Icc 1 D)
    (hS₅ : ∀ t, S₅ t ⊆ Finset.Icc 1 D) (hS₆ : ∀ t, S₆ t ⊆ Finset.Icc 1 D) :
    chenUpsilon36CentreCost N S₃ S₄ S₅ S₆ ≤
      (8 / (Real.log 2) ^ 3) * (N : ℝ) ^ (1 / 2 : ℝ) * (Real.log (N : ℝ)) ^ 3 := by
  have hL : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_natCast_nonneg N) (Real.log_pos (by norm_num)).le
  calc
    _ ≤ 8 * (D : ℝ) * (Real.log (N : ℝ) / Real.log 2) ^ 3 :=
      chenUpsilon36CentreCost_le_eight_cap_log_cube hN hN4 hlog
        S₃ S₄ S₅ S₆ hS₃ hS₄ hS₅ hS₆
    _ ≤ 8 * Real.sqrt (N : ℝ) * (Real.log (N : ℝ) / Real.log 2) ^ 3 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num))
        (pow_nonneg hL 3)
    _ = _ := by rw [Real.sqrt_eq_rpow, div_pow]; ring

/-- Unconditional arbitrary fixed logarithmic accuracy for the complete
pooled centre cost. No AP-error or desired remainder estimate is assumed. -/
theorem eventually_chenUpsilon36CentreCost_le_logAccuracy (K : ℕ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N : ℕ in atTop, ∀ hN : Even N, ∀ D : ℕ,
        ∀ S₃ S₄ : ℕ → Finset ℕ, ∀ S₅ S₆ : (ℕ × ℕ) → Finset ℕ,
        (D : ℝ) ≤ Real.sqrt (N : ℝ) →
        (∀ p, S₃ p ⊆ Finset.Icc 1 D) → (∀ p, S₄ p ⊆ Finset.Icc 1 D) →
        (∀ t, S₅ t ⊆ Finset.Icc 1 D) → (∀ t, S₆ t ⊆ Finset.Icc 1 D) →
        chenUpsilon36CentreCost N S₃ S₄ S₅ S₆ ≤
          epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  intro epsilon hepsilon
  filter_upwards
    [eventually_powerLog_le_logAccuracy (8 / (Real.log 2) ^ 3) (1 / 2) 3 K
      (by norm_num) epsilon hepsilon,
      eventually_one_le_nat_log, eventually_ge_atTop (4 : ℕ)] with N hpower hlog hN4
  intro hN D S₃ S₄ S₅ S₆ hD hS₃ hS₄ hS₅ hS₆
  exact (chenUpsilon36CentreCost_le_sqrt_log_cube hN hN4 hlog hD
    S₃ S₄ S₅ S₆ hS₃ hS₄ hS₅ hS₆).trans hpower

end

end ImbalancedChen
