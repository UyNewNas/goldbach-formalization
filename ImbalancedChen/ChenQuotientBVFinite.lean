import ImbalancedChen.ChenPooledQuotientAP
import ImbalancedChen.ChenQuotientCentreBudget

/-!
# Active-row pooling for the actual third through sixth quotient remainders

This owned-only candidate retains the secondary base-modulus AP error.
Only nonempty rows enter its multiplier pool: the product cap then bounds
both the multiplier and every inner modulus by Q. The proved logarithmic
reciprocal-totient bound pays each row, and multiplier injectivity removes
any selector-cardinality loss. No analytic estimate is assumed or proved.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

/-- The secondary AP term pools only active rows. Empty rows contribute
zero even when their multiplier is larger than the product-modulus cap. -/
theorem chenQuotient_secondary_AP_sum_le_primitive_log
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (M : ℝ) (Q : ℕ)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hbinj : Set.InjOn b (T : Set α))
    (hdpos : ∀ t ∈ T, ∀ d ∈ S t, 0 < d)
    (hcap : ∀ t ∈ T, ∀ d ∈ S t, b t * d ≤ Q) :
    (∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)| *
      ∑ d ∈ S t, 1 / (Nat.totient d : ℝ)) ≤
      (4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N M k| := by
  let U := T.filter (fun t => (S t).Nonempty)
  have hUT : U ⊆ T := Finset.filter_subset _ _
  have hrow : ∀ t ∈ U, S t ⊆ Finset.Icc 1 Q := by
    intro t ht d hd
    have hbt : 1 ≤ b t := hbpos t (hUT ht)
    have hle : d ≤ b t * d := by
      simpa only [one_mul] using Nat.mul_le_mul_right d hbt
    exact Finset.mem_Icc.mpr
      ⟨hdpos t (hUT ht) d hd, hle.trans (hcap t (hUT ht) d hd)⟩
  have hremove : (∑ t ∈ T, |chenQuotientPrimeAPError N M (b t)| *
      ∑ d ∈ S t, 1 / (Nat.totient d : ℝ)) =
      ∑ t ∈ U, |chenQuotientPrimeAPError N M (b t)| *
        ∑ d ∈ S t, 1 / (Nat.totient d : ℝ) := by
    symm
    apply Finset.sum_subset hUT
    intro t ht hnot
    have hempty : S t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      exact hnot (Finset.mem_filter.mpr ⟨ht, ⟨d, hd⟩⟩)
    simp only [hempty, Finset.sum_empty, mul_zero]
  have hsub : U.image b ⊆ (Finset.Icc 1 Q).filter (fun k => Nat.Coprime k N) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨d, hd⟩ := (Finset.mem_filter.mp ht).2
    have hd1 : 1 ≤ d := hdpos t (hUT ht) d hd
    have hle : b t ≤ b t * d := by
      simpa only [mul_one] using Nat.mul_le_mul_left (b t) hd1
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hbpos t (hUT ht), hle.trans (hcap t (hUT ht) d hd)⟩,
        hbN t (hUT ht)⟩
  have hbase : (∑ t ∈ U, |chenQuotientPrimeAPError N M (b t)|) ≤
      ∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
        |chenQuotientPrimeAPError N M k| := by
    calc
      _ = ∑ k ∈ U.image b, |chenQuotientPrimeAPError N M k| := by
        symm
        apply Finset.sum_image
        intro t ht u hu htu
        exact hbinj (hUT ht) (hUT hu) htu
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => abs_nonneg _)
  rw [hremove]
  exact (chenQuotient_secondary_AP_sum_le_log U b S N M Q hrow).trans
    (mul_le_mul_of_nonneg_left hbase (by
      have hlog : 0 ≤ Real.log (max 1 (Q : ℝ)) := Real.log_nonneg (le_max_left _ _)
      positivity))

/-- Both literal ordinary-AP errors now have one common primitive pool.
The complete centre cost remains explicit, with its original labels. -/
theorem sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    {α : Type*} (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (N : ℕ) (A M : ℝ) (Q : ℕ) (hN : Even N)
    (hbpos : ∀ t ∈ T, 0 < b t) (hbN : ∀ t ∈ T, Nat.Coprime (b t) N)
    (hb : ∀ t ∈ T, Nat.Coprime (b t) (sieveProduct N (Nat.ceil A)))
    (hbinj : Set.InjOn b (T : Set α))
    (hS : ∀ t ∈ T, S t ⊆ (sieveProduct N (Nat.ceil A)).divisors)
    (hcap : ∀ t ∈ T, ∀ d ∈ S t, b t * d ≤ Q) :
    (∑ t ∈ T.attach, ∑ d ∈ S t.val,
      |(chenQuotientBoundingSieve N (b t.val) A hN (hb t.val t.property)).rem d|) ≤
      (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N M k|) + chenSelectedCentreCost N T b S := by
  have hsecondary := chenQuotient_secondary_AP_sum_le_primitive_log T b S N M Q
    hbpos hbN hbinj (fun t ht d hd => Nat.pos_of_mem_divisors (hS t ht hd)) hcap
  have h := (sum_abs_chenQuotient_rem_le_pooled_primeAP T b S N A M Q hN
    hbpos hbN hb hbinj hS hcap).trans
      (add_le_add (add_le_add le_rfl hsecondary) le_rfl)
  unfold chenSelectedCentreCost
  nlinarith only [h]

/-- Literal admissibility: every selected row lies in the actual sieve
product's divisors and every full product modulus is at most Q. Nothing
is required of rows outside T. -/
def ChenQuotientRows {α : Type*} (N : ℕ) (A : ℝ) (Q : ℕ)
    (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ) : Prop :=
  ∀ t ∈ T, S t ⊆ ((sieveProduct N (Nat.ceil A)).divisors.filter
    (fun d => b t * d ≤ Q))

/-- Positive multipliers turn the full product cap into an inner cap. -/
theorem ChenQuotientRows.subset_Icc {α : Type*} {N Q : ℕ} {A : ℝ}
    {T : Finset α} {b : α → ℕ} {S : α → Finset ℕ}
    (h : ChenQuotientRows N A Q T b S) (hbpos : ∀ t ∈ T, 0 < b t) :
    ∀ t ∈ T, S t ⊆ Finset.Icc 1 Q := by
  intro t ht d hd
  obtain ⟨hdP, hcap⟩ := Finset.mem_filter.mp (h t ht hd)
  have hle : d ≤ b t * d := by
    simpa only [one_mul] using Nat.mul_le_mul_right d (hbpos t ht)
  exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdP, hle.trans hcap⟩

/-- Exactly the original four selector bands, sharing only a full
product-modulus cap and allowing four independent varying row families. -/
def ChenUpsilon36Rows (N Q : ℕ) (S₃ S₄ : ℕ → Finset ℕ)
    (S₅ S₆ : (ℕ × ℕ) → Finset ℕ) : Prop :=
  ChenQuotientRows N ((N : ℝ) ^ (100 / 1149 : ℝ)) Q
    (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))
    id S₃ ∧
  ChenQuotientRows N ((N : ℝ) ^ (100 / 1149 : ℝ)) Q
    (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))) id S₄ ∧
  ChenQuotientRows N ((N : ℝ) ^ (100 / 1149 : ℝ)) Q
    (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)))
    (fun t => t.1 * t.2) S₅ ∧
  ChenQuotientRows N ((N : ℝ) ^ (100 / 1149 : ℝ)) Q
    (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))))
    (fun t => t.1 * t.2) S₆

/-- The four actual absolute remainder sums with unit outer coefficients.
The attached labels provide precisely the proved local-density gates. -/
def chenUpsilon36RemainderSum (N : ℕ) (hN : Even N)
    (S₃ S₄ : ℕ → Finset ℕ) (S₅ S₆ : (ℕ × ℕ) → Finset ℕ) : ℝ :=
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))).attach, ∑ d ∈ S₃ p.val,
    |(chenQuotientBoundingSieve N p.val ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
      (chenSinglePrimeSelector_sieve_data p.property).2.2).rem d|) +
  (∑ p ∈ (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))).attach, ∑ d ∈ S₄ p.val,
    |(chenQuotientBoundingSieve N p.val ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
      (chenSinglePrimeSelector_sieve_data p.property).2.2).rem d|) +
  (∑ t ∈ (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (50 / 309 : ℝ))).attach, ∑ d ∈ S₅ t.val,
    |(chenQuotientBoundingSieve N (t.val.1 * t.val.2) ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
      (chenY5PrimeSelector_sieve_data t.property).2.2).rem d|) +
  (∑ t ∈ (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ (50 / 309 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ)))).attach, ∑ d ∈ S₆ t.val,
    |(chenQuotientBoundingSieve N (t.val.1 * t.val.2) ((N : ℝ) ^ (100 / 1149 : ℝ)) hN
      (chenY6PrimeSelector_sieve_data t.property).2.2).rem d|)

/-- The full four-term pool pays both AP errors and retains every centre
correction. Coincident moduli across different terms cost the explicit 4. -/
theorem chenUpsilon36RemainderSum_le_primitive_log_add_cost
    (N Q : ℕ) (hN : Even N) (M : ℝ)
    (S₃ S₄ : ℕ → Finset ℕ) (S₅ S₆ : (ℕ × ℕ) → Finset ℕ)
    (hrows : ChenUpsilon36Rows N Q S₃ S₄ S₅ S₆) :
    chenUpsilon36RemainderSum N hN S₃ S₄ S₅ S₆ ≤
      4 * (1 + 4 * (1 + Real.log (max 1 (Q : ℝ)))) *
        (∑ k ∈ Finset.Icc 1 Q with Nat.Coprime k N,
          |chenQuotientPrimeAPError N M k|) + chenUpsilon36CentreCost N S₃ S₄ S₅ S₆ := by
  obtain ⟨hr₃, hr₄, hr₅, hr₆⟩ := hrows
  have h₃ := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))
    id S₃ N ((N : ℝ) ^ (100 / 1149 : ℝ)) M Q hN
    (fun p hp => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data hp).1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.2)
    (fun _ _ _ _ h => h)
    (fun p hp d hd => (Finset.mem_filter.mp (hr₃ p hp hd)).1)
    (fun p hp d hd => (Finset.mem_filter.mp (hr₃ p hp hd)).2)
  have h₄ := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenSinglePrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))))
    id S₄ N ((N : ℝ) ^ (100 / 1149 : ℝ)) M Q hN
    (fun p hp => lt_trans Nat.zero_lt_one (chenSinglePrimeSelector_sieve_data hp).1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.1)
    (fun p hp => (chenSinglePrimeSelector_sieve_data hp).2.2)
    (fun _ _ _ _ h => h)
    (fun p hp d hd => (Finset.mem_filter.mp (hr₄ p hp hd)).1)
    (fun p hp d hd => (Finset.mem_filter.mp (hr₄ p hp hd)).2)
  have h₅ := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenY5PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ)))
    (fun t => t.1 * t.2) S₅ N ((N : ℝ) ^ (100 / 1149 : ℝ)) M Q hN
    (fun t ht => lt_trans Nat.zero_lt_one (chenY5PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.1)
    (fun t ht => (chenY5PrimeSelector_sieve_data ht).2.2)
    (chenY5PrimeSelector_multiplier_injOn N _ _)
    (fun t ht d hd => (Finset.mem_filter.mp (hr₅ t ht hd)).1)
    (fun t ht d hd => (Finset.mem_filter.mp (hr₅ t ht hd)).2)
  have h₆ := sum_abs_chenQuotient_rem_le_primitive_log_add_cost
    (chenY6PrimeSelector N ((N : ℝ) ^ (100 / 1149 : ℝ)) ((N : ℝ) ^ (50 / 309 : ℝ))
      ((N : ℝ) ^ ((1 / 2 : ℝ) - 3 * (100 / 1149 : ℝ))))
    (fun t => t.1 * t.2) S₆ N ((N : ℝ) ^ (100 / 1149 : ℝ)) M Q hN
    (fun t ht => lt_trans Nat.zero_lt_one (chenY6PrimeSelector_sieve_data ht).1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.1)
    (fun t ht => (chenY6PrimeSelector_sieve_data ht).2.2)
    (chenY6PrimeSelector_multiplier_injOn N _ _ _)
    (fun t ht d hd => (Finset.mem_filter.mp (hr₆ t ht hd)).1)
    (fun t ht d hd => (Finset.mem_filter.mp (hr₆ t ht hd)).2)
  unfold chenUpsilon36RemainderSum chenUpsilon36CentreCost
  linarith only [h₃, h₄, h₅, h₆]

/-- Intersecting all rows with the common cap changes no selected row.
This permits the existing centre-cost theorem without imposing conditions
on unused labels outside the actual selector. -/
private theorem chenSelectedCentreCost_inter_rows {α : Type*}
    (N Q : ℕ) (T : Finset α) (b : α → ℕ) (S : α → Finset ℕ)
    (hS : ∀ t ∈ T, S t ⊆ Finset.Icc 1 Q) :
    chenSelectedCentreCost N T b (fun t => S t ∩ Finset.Icc 1 Q) =
      chenSelectedCentreCost N T b S := by
  unfold chenSelectedCentreCost
  apply Finset.sum_congr rfl
  intro t ht
  have heq : S t ∩ Finset.Icc 1 Q = S t := by
    ext d
    simp only [Finset.mem_inter]
    constructor
    · exact And.left
    · intro hd
      exact ⟨hd, hS t ht hd⟩
  rw [heq]

/-- The proved arbitrary-logarithmic centre budget applies under the
literal product-row assumptions, uniformly over all four families. -/
theorem eventually_chenUpsilon36CentreCost_le_of_rows (K : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ hN : Even N, ∀ Q : ℕ,
      ∀ S₃ S₄ : ℕ → Finset ℕ, ∀ S₅ S₆ : (ℕ × ℕ) → Finset ℕ,
      (Q : ℝ) ≤ Real.sqrt (N : ℝ) → ChenUpsilon36Rows N Q S₃ S₄ S₅ S₆ →
      chenUpsilon36CentreCost N S₃ S₄ S₅ S₆ ≤
        epsilon * (N : ℝ) / (Real.log (N : ℝ)) ^ K := by
  filter_upwards [eventually_chenUpsilon36CentreCost_le_logAccuracy K epsilon hepsilon]
    with N hcost
  intro hN Q S₃ S₄ S₅ S₆ hQ hrows
  obtain ⟨hr₃, hr₄, hr₅, hr₆⟩ := hrows
  have h₃ := chenSelectedCentreCost_inter_rows N Q _ id S₃
    (hr₃.subset_Icc (fun p hp => lt_trans Nat.zero_lt_one
      (chenSinglePrimeSelector_sieve_data hp).1))
  have h₄ := chenSelectedCentreCost_inter_rows N Q _ id S₄
    (hr₄.subset_Icc (fun p hp => lt_trans Nat.zero_lt_one
      (chenSinglePrimeSelector_sieve_data hp).1))
  have h₅ := chenSelectedCentreCost_inter_rows N Q _ (fun t : ℕ × ℕ => t.1 * t.2) S₅
    (hr₅.subset_Icc (fun t ht => lt_trans Nat.zero_lt_one
      (chenY5PrimeSelector_sieve_data ht).1))
  have h₆ := chenSelectedCentreCost_inter_rows N Q _ (fun t : ℕ × ℕ => t.1 * t.2) S₆
    (hr₆.subset_Icc (fun t ht => lt_trans Nat.zero_lt_one
      (chenY6PrimeSelector_sieve_data ht).1))
  have h := hcost hN Q (fun p => S₃ p ∩ Finset.Icc 1 Q)
    (fun p => S₄ p ∩ Finset.Icc 1 Q) (fun t => S₅ t ∩ Finset.Icc 1 Q)
    (fun t => S₆ t ∩ Finset.Icc 1 Q) hQ
    (fun _ => Finset.inter_subset_right) (fun _ => Finset.inter_subset_right)
    (fun _ => Finset.inter_subset_right) (fun _ => Finset.inter_subset_right)
  unfold chenUpsilon36CentreCost at h ⊢
  rwa [h₃, h₄, h₅, h₆] at h

end

end ImbalancedChen
