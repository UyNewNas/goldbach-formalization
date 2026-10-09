import ImbalancedChen.ChenQuotientSieveRemainders
import ImbalancedChen.DivisorMomentBudget
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Pooling the actual third through sixth quotient-sieve AP errors

This candidate has not been compiled. Only the existing project's CI may
perform Lean verification. It imports no held foreign adapter.

The selected multiplier is coprime to the strict sieve product, while the
inner modulus divides that product. Hence the full product modulus recovers
its inner modulus by gcd. After proving that each actual selector determines
its multiplier injectively, there is no multiplicity loss within a term.
The inner divisor set may vary with the outer label.

All AP errors, secondary mass errors, and centre corrections remain literal.
No distribution estimate, optimized sieve estimate, or asymptotic hypothesis
appears below. The final fourth-moment budget is an existing proved finite
elementary estimate applied to the new squarefree pooled support.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- The pooled set records literal product moduli. The labelled domain is
retained in every reindexing theorem, and injectivity is proved first. -/
def chenPooledQuotientModuli {α : Type*} (T : Finset α)
    (b : α → ℕ) (S : α → Finset ℕ) : Finset ℕ :=
  (T.sigma S).image (fun x => b x.1 * x.2)

/-- A full product modulus recovers its sieve divisor exactly. This does
not hold for arbitrary inner moduli outside the allowed divisor set. -/
theorem chenQuotient_product_gcd_sieveProduct
    {P b d : ℕ} (hb : Nat.Coprime b P) (hd : d ∣ P) :
    Nat.gcd (b * d) P = d :=
  Nat.gcd_mul_of_coprime_of_dvd hb hd

/-- Separation of the rough multiplier and allowed sieve divisor. Zero
inner moduli are excluded by actual divisor membership, even at `P = 0`. -/
theorem chenQuotient_product_factors_unique
    {P b c d e : ℕ} (hb : Nat.Coprime b P) (hc : Nat.Coprime c P)
    (hd : d ∈ P.divisors) (he : e ∈ P.divisors)
    (hprod : b * d = c * e) : b = c ∧ d = e := by
  have hde : d = e := by
    calc
      d = Nat.gcd (b * d) P :=
        (chenQuotient_product_gcd_sieveProduct hb (Nat.dvd_of_mem_divisors hd)).symm
      _ = Nat.gcd (c * e) P := by rw [hprod]
      _ = e := chenQuotient_product_gcd_sieveProduct hc (Nat.dvd_of_mem_divisors he)
  subst e
  exact ⟨(mul_left_inj' (Nat.pos_of_mem_divisors hd).ne').mp hprod, rfl⟩

/-- The injection preserves outer labels, rather than silently replacing
a labelled sum by an image sum that might forget multiplicity. -/
theorem chenPooledQuotientModuli_injOn {α : Type*}
    (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ) (P : ℕ)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) P)
    (hbinj : Set.InjOn b (T : Set α))
    (hS : ∀ t ∈ T, S t ⊆ P.divisors) :
    Set.InjOn (fun x : Σ _ : α, ℕ => b x.1 * x.2) (T.sigma S : Set (Σ _ : α, ℕ)) := by
  rintro ⟨t, d⟩ htd ⟨u, e⟩ hue hprod
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp htd
  obtain ⟨hu, he⟩ := Finset.mem_sigma.mp hue
  obtain ⟨hbu, hde⟩ := chenQuotient_product_factors_unique
    (hb t ht) (hb u hu) (hS t ht hd) (hS u hu he) hprod
  have htu := hbinj ht hu hbu
  subst u
  subst e
  rfl

/-- Exact finite pooling for arbitrary real summands. No positivity and
no cap is needed for this equality. -/
theorem sum_chenPooledQuotientModuli {α : Type*}
    (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ) (P : ℕ)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) P)
    (hbinj : Set.InjOn b (T : Set α))
    (hS : ∀ t ∈ T, S t ⊆ P.divisors) (F : ℕ → ℝ) :
    (∑ t ∈ T, ∑ d ∈ S t, F (b t * d)) =
      ∑ k ∈ chenPooledQuotientModuli T b S, F k := by
  unfold chenPooledQuotientModuli
  rw [Finset.sum_image (chenPooledQuotientModuli_injOn T b S P hb hbinj hS)]
  exact (Finset.sum_sigma T S (fun x => F (b x.1 * x.2))).symm

/-- Pooling into the primitive global product-modulus range. The cap is
on `b t * d`, not on `d` alone and not on an lcm. -/
theorem chenPooledQuotientModuli_subset_primitive
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (A : ℝ) (Q : ℕ)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hS : ∀ t ∈ T, S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ T, ∀ d ∈ S t, b t * d ≤ Q) :
    chenPooledQuotientModuli T b S ⊆
      (Finset.Icc 1 Q).filter (fun k => Nat.Coprime k N) := by
  intro k hk
  obtain ⟨⟨t, d⟩, htd, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp htd
  have hdP := hS t ht hd
  refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
    ⟨Nat.mul_pos (hbpos t ht) (Nat.pos_of_mem_divisors hdP), hcap t ht d hd⟩, ?_⟩
  exact (chenQuotient_allowed_primitive (hbN t ht)
    (Nat.dvd_of_mem_divisors hdP)).symm

/-- Unweighted AP-error pooling costs no outer cardinality or divisor
multiplicity factor. The literal ordinary AP error is not bounded here. -/
theorem sum_chenQuotientPrimeAPError_product_le_primitive
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (A M : ℝ) (Q : ℕ)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)))
    (hbinj : Set.InjOn b (T : Set α))
    (hS : ∀ t ∈ T, S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ T, ∀ d ∈ S t, b t * d ≤ Q) :
    (∑ t ∈ T, ∑ d ∈ S t, |chenQuotientPrimeAPError N M (b t * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N, |chenQuotientPrimeAPError N M k| := by
  rw [sum_chenPooledQuotientModuli T b S _ hb hbinj hS]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (chenPooledQuotientModuli_subset_primitive T b S N A Q hbpos hbN hS hcap)
    (fun _ _ _ => abs_nonneg _)

/-- The exact existing quotient remainder transfer, now pooled over
varying allowed divisor sets. The secondary base-modulus error and both
centre corrections remain separate, with their original outer labels. -/
theorem sum_abs_chenQuotient_rem_le_pooled_primeAP
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (A M : ℝ) (Q : ℕ) (hN : Even N)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)))
    (hbinj : Set.InjOn b (T : Set α))
    (hS : ∀ t ∈ T, S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ T, ∀ d ∈ S t, b t * d ≤ Q) :
    (∑ t ∈ T.attach, ∑ d ∈ S t.val,
      |(chenQuotientBoundingSieve N (b t.val) A hN (hb t.val t.property)).rem d|) ≤
      (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N, |chenQuotientPrimeAPError N M k|) +
        (∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)| *
          ∑ d ∈ S t, 1 / (Nat.totient d : ℝ)) +
        ∑ t ∈ T, ∑ d ∈ S t, chenQuotientCentreCost N (b t) d := by
  have hsum := Finset.sum_le_sum (s := T.attach) (fun t _ =>
    sum_abs_chenQuotientBoundingSieve_rem_le_primeAP_errors N (b t.val) A hN
      (hb t.val t.property) (S t.val)
      (fun d hd => Nat.dvd_of_mem_divisors (hS t.val t.property hd)) M)
  simp only [Finset.sum_add_distrib] at hsum
  rw [Finset.sum_attach T (fun t =>
      ∑ d ∈ S t, |chenQuotientPrimeAPError N M (b t * d)|),
    Finset.sum_attach T (fun t => |chenQuotientPrimeAPError N M (b t)| *
      ∑ d ∈ S t, 1 / (Nat.totient d : ℝ)),
    Finset.sum_attach T (fun t =>
      ∑ d ∈ S t, chenQuotientCentreCost N (b t) d)] at hsum
  exact hsum.trans (add_le_add_right (add_le_add_right
    (sum_chenQuotientPrimeAPError_product_le_primitive T b S N A M Q
      hbpos hbN hb hbinj hS hcap) _) _)

/-- The secondary term has an elementary uniform reciprocal-totient
cost. It is not discarded or disguised as the pooled product-modulus term. -/
theorem chenQuotient_secondary_AP_sum_le_log
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (M : ℝ) (D : ℕ)
    (hS : ∀ t ∈ T, S t ⊆ Finset.Icc 1 D) :
    (∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)| *
      ∑ d ∈ S t, 1 / (Nat.totient d : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (D : ℝ)))) *
        ∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)| := by
  calc
    _ ≤ ∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)| *
        (4 * (1 + Real.log (max 1 (D : ℝ)))) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (sum_reciprocal_totient_subset_le_log (S t) D (hS t ht)) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- Squarefreeness of the full product is proved from squarefreeness of
the selected multiplier and the actual sieve product. -/
theorem chenPooledQuotientModuli_squarefree
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (A : ℝ)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)))
    (hbsq : ∀ t ∈ T, Squarefree (b t))
    (hS : ∀ t ∈ T, S t ⊆ (sieveProduct N (Nat.ceil A)).divisors) :
    ∀ k ∈ chenPooledQuotientModuli T b S, Squarefree k := by
  intro k hk
  obtain ⟨⟨t, d⟩, htd, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨ht, hd⟩ := Finset.mem_sigma.mp htd
  have hdP := Nat.dvd_of_mem_divisors (hS t ht hd)
  exact (Nat.squarefree_mul (chenQuotient_allowed_coprime (hb t ht) hdP)).mpr
    ⟨hbsq t ht, (sieveProduct_squarefree N (Nat.ceil A)).squarefree_of_dvd hdP⟩

/-- An unconditional meaningful divisor budget on the pooled support.
There is no extra selector-cardinality factor. This fourth moment can
pay a square of a `tau(k)^2` coefficient through finite Cauchy. -/
theorem sum_chenQuotient_product_divisor_fourth_moment_le_log
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (A : ℝ) (Q : ℕ)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)))
    (hbinj : Set.InjOn b (T : Set α)) (hbsq : ∀ t ∈ T, Squarefree (b t))
    (hS : ∀ t ∈ T, S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ T, ∀ d ∈ S t, b t * d ≤ Q) :
    (∑ t ∈ T, ∑ d ∈ S t,
      ((b t * d).divisors.card : ℝ) ^ 4 / (Nat.totient (b t * d) : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (Q : ℝ)))) ^ 16 := by
  rw [sum_chenPooledQuotientModuli T b S _ hb hbinj hS]
  apply sum_divisor_fourth_moment_le_log _ Q
  · exact (chenPooledQuotientModuli_subset_primitive T b S N A Q hbpos hbN hS hcap).trans
      (Finset.filter_subset _ _)
  · exact chenPooledQuotientModuli_squarefree T b S N A hb hbsq hS

/-- The fifth selector already stores strictly ordered distinct primes. -/
theorem chenY5PrimeSelector_ordered_prime_data {N : ℕ} {A H : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ chenY5PrimeSelector N A H) :
    Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ t.1 < t.2 := by
  obtain ⟨hc, _, hlt, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  exact ⟨(mem_chenAdditivePrimeCarrier.mp hc₁).2.1,
    (mem_chenAdditivePrimeCarrier.mp hc₂).2.1, hlt⟩

/-- The sixth selector's strict first upper endpoint and inclusive
second lower endpoint force the same strict ordering. -/
theorem chenY6PrimeSelector_ordered_prime_data {N : ℕ} {A H D : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ chenY6PrimeSelector N A H D) :
    Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ t.1 < t.2 := by
  obtain ⟨hc, _, hH₁, hH₂, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  refine ⟨(mem_chenAdditivePrimeCarrier.mp hc₁).2.1,
    (mem_chenAdditivePrimeCarrier.mp hc₂).2.1, ?_⟩
  exact_mod_cast hH₁.trans_le hH₂

/-- Ordered-prime factor uniqueness is reused from the existing core. -/
theorem chenY5PrimeSelector_multiplier_injOn (N : ℕ) (A H : ℝ) :
    Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2)
      (chenY5PrimeSelector N A H : Set (ℕ × ℕ)) := by
  intro t ht u hu hprod
  obtain ⟨ht₁, ht₂, hto⟩ := chenY5PrimeSelector_ordered_prime_data ht
  obtain ⟨hu₁, hu₂, huo⟩ := chenY5PrimeSelector_ordered_prime_data hu
  obtain ⟨h₁, h₂⟩ := ordered_prime_factors_unique ht₁ ht₂ hu₁ hu₂ hto.le huo.le hprod
  exact Prod.ext h₁ h₂

theorem chenY6PrimeSelector_multiplier_injOn (N : ℕ) (A H D : ℝ) :
    Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2)
      (chenY6PrimeSelector N A H D : Set (ℕ × ℕ)) := by
  intro t ht u hu hprod
  obtain ⟨ht₁, ht₂, hto⟩ := chenY6PrimeSelector_ordered_prime_data ht
  obtain ⟨hu₁, hu₂, huo⟩ := chenY6PrimeSelector_ordered_prime_data hu
  obtain ⟨h₁, h₂⟩ := ordered_prime_factors_unique ht₁ ht₂ hu₁ hu₂ hto.le huo.le hprod
  exact Prod.ext h₁ h₂

theorem chenSinglePrimeSelector_multiplier_squarefree {N : ℕ} {A U : ℝ} {p : ℕ}
    (hp : p ∈ chenSinglePrimeSelector N A U) : Squarefree p :=
  (mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1).2.1.squarefree

private theorem chenPooled_ordered_prime_product_squarefree {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hlt : p < q) : Squarefree (p * q) := by
  have hcop : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr (fun hd =>
    hlt.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))
  exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hq.squarefree⟩

theorem chenY5PrimeSelector_multiplier_squarefree {N : ℕ} {A H : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ chenY5PrimeSelector N A H) : Squarefree (t.1 * t.2) := by
  obtain ⟨hp, hq, hlt⟩ := chenY5PrimeSelector_ordered_prime_data ht
  exact chenPooled_ordered_prime_product_squarefree hp hq hlt

theorem chenY6PrimeSelector_multiplier_squarefree {N : ℕ} {A H D : ℝ} {t : ℕ × ℕ}
    (ht : t ∈ chenY6PrimeSelector N A H D) : Squarefree (t.1 * t.2) := by
  obtain ⟨hp, hq, hlt⟩ := chenY6PrimeSelector_ordered_prime_data ht
  exact chenPooled_ordered_prime_product_squarefree hp hq hlt

/-- Literal one-prime selection, with arbitrary label-dependent allowed
divisor sets. This simultaneously covers the different third/fourth bands. -/
theorem chenSinglePrimeSelector_pooled_AP_bound
    (N : ℕ) (A U M : ℝ) (Q : ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ p ∈ chenSinglePrimeSelector N A U,
      S p ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ p ∈ chenSinglePrimeSelector N A U, ∀ d ∈ S p, p * d ≤ Q) :
    (∑ p ∈ chenSinglePrimeSelector N A U, ∑ d ∈ S p,
      |chenQuotientPrimeAPError N M (p * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| := by
  exact sum_chenQuotientPrimeAPError_product_le_primitive
    (chenSinglePrimeSelector N A U) (fun p => p) S N A M Q
    (fun p hp => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data hp).1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.2)
    (fun _ _ _ _ h => h) hS hcap

theorem chenY5PrimeSelector_pooled_AP_bound
    (N : ℕ) (A H M : ℝ) (Q : ℕ) (S : (ℕ × ℕ) → Finset ℕ)
    (hS : ∀ t ∈ chenY5PrimeSelector N A H,
      S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ chenY5PrimeSelector N A H, ∀ d ∈ S t, (t.1 * t.2) * d ≤ Q) :
    (∑ t ∈ chenY5PrimeSelector N A H, ∑ d ∈ S t,
      |chenQuotientPrimeAPError N M ((t.1 * t.2) * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| := by
  exact sum_chenQuotientPrimeAPError_product_le_primitive
    (chenY5PrimeSelector N A H) (fun t => t.1 * t.2) S N A M Q
    (fun t ht => lt_trans Nat.zero_lt_one (chenY5PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.2)
    (chenY5PrimeSelector_multiplier_injOn N A H) hS hcap

theorem chenY6PrimeSelector_pooled_AP_bound
    (N : ℕ) (A H D M : ℝ) (Q : ℕ) (S : (ℕ × ℕ) → Finset ℕ)
    (hS : ∀ t ∈ chenY6PrimeSelector N A H D,
      S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ chenY6PrimeSelector N A H D, ∀ d ∈ S t,
      (t.1 * t.2) * d ≤ Q) :
    (∑ t ∈ chenY6PrimeSelector N A H D, ∑ d ∈ S t,
      |chenQuotientPrimeAPError N M ((t.1 * t.2) * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| := by
  exact sum_chenQuotientPrimeAPError_product_le_primitive
    (chenY6PrimeSelector N A H D) (fun t => t.1 * t.2) S N A M Q
    (fun t ht => lt_trans Nat.zero_lt_one (chenY6PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.2)
    (chenY6PrimeSelector_multiplier_injOn N A H D) hS hcap

/-- The third term's original strict upper cap is exactly `N^(1/3)`. -/
theorem chenUpsilon3_pooled_AP_bound
    (N : ℕ) (M : ℝ) (Q : ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
      S p ⊆ (sieveProduct N (Nat.ceil ((N : ℝ) ^ (100 / 1149 : ℝ)))).divisors)
    (hcap : ∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), ∀ d ∈ S p, p * d ≤ Q) :
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), ∑ d ∈ S p,
      |chenQuotientPrimeAPError N M (p * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| :=
  chenSinglePrimeSelector_pooled_AP_bound N _ _ M Q S hS hcap

/-- The fourth term keeps its distinct strict upper cap. -/
theorem chenUpsilon4_pooled_AP_bound
    (N : ℕ) (M : ℝ) (Q : ℕ) (S : ℕ → Finset ℕ)
    (hS : ∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
      S p ⊆ (sieveProduct N (Nat.ceil ((N : ℝ) ^ (100 / 1149 : ℝ)))).divisors)
    (hcap : ∀ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
      ∀ d ∈ S p, p * d ≤ Q) :
    (∑ p ∈ chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))), ∑ d ∈ S p,
      |chenQuotientPrimeAPError N M (p * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| :=
  chenSinglePrimeSelector_pooled_AP_bound N _ _ M Q S hS hcap

/-- The fifth term retains the original ordered pair and small-prime band. -/
theorem chenUpsilon5_pooled_AP_bound
    (N : ℕ) (M : ℝ) (Q : ℕ) (S : (ℕ × ℕ) → Finset ℕ)
    (hS : ∀ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ)),
      S t ⊆ (sieveProduct N (Nat.ceil ((N : ℝ) ^ (100 / 1149 : ℝ)))).divisors)
    (hcap : ∀ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ)), ∀ d ∈ S t, (t.1 * t.2) * d ≤ Q) :
    (∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ)), ∑ d ∈ S t,
      |chenQuotientPrimeAPError N M ((t.1 * t.2) * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| :=
  chenY5PrimeSelector_pooled_AP_bound N _ _ M Q S hS hcap

/-- The sixth term keeps `[H,D)` at the second prime, including equality at H. -/
theorem chenUpsilon6_pooled_AP_bound
    (N : ℕ) (M : ℝ) (Q : ℕ) (S : (ℕ × ℕ) → Finset ℕ)
    (hS : ∀ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
      S t ⊆ (sieveProduct N (Nat.ceil ((N : ℝ) ^ (100 / 1149 : ℝ)))).divisors)
    (hcap : ∀ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))),
      ∀ d ∈ S t, (t.1 * t.2) * d ≤ Q) :
    (∑ t ∈ chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
        ((N : ℝ) ^ (50 / 309 : ℝ))
        ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))), ∑ d ∈ S t,
      |chenQuotientPrimeAPError N M ((t.1 * t.2) * d)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| :=
  chenY6PrimeSelector_pooled_AP_bound N _ _ _ M Q S hS hcap

end

end ImbalancedChen
