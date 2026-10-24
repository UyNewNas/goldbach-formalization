import ImbalancedChen.CurrentChenP5U9OrderedBranches
import ImbalancedChen.CurrentChenUpsilon9UnitBudget

/-!
# The two actual repeated-factor exceptions in the marked ninth source

SOURCE ONLY / UNCOMPILED. The first import names the preceding source-only
candidate in this directory. Repetition is never excluded by a convention:
q=p₁ belongs to the middle branch and q=p₂ to the last branch. Since p₁<p₂,
these are the only two repeated-factor events and they are disjoint.

Each repeated event retains one original pair label and therefore has at
most the cardinality of the actual selector. An explicit finite rectangle
gives at most 4*N^(92/125) per event, hence 8*N^(92/125) in total. This pays
the original prime-receiver counting exception in singularNormalization.
It does not assert a bound for a full signed PP modulus sum.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

/-- j=0 is q=p₁, j=1 is q=p₂. Both events include the original source. -/
def p5z_u9_repeatLabels (j : Fin 2) (N : ℕ) : Finset P5zU9Triple :=
  (p5z_u9_switchedLabels N).filter (fun t => t.2 = ![t.1.1, t.1.2] j)

def p5z_u9_repeatedLabels (N : ℕ) : Finset P5zU9Triple :=
  (p5z_u9_switchedLabels N).filter (fun t => t.2 = t.1.1 ∨ t.2 = t.1.2)

theorem p5z_u9_repeatLabels_union (N : ℕ) :
    p5z_u9_repeatLabels 0 N ∪ p5z_u9_repeatLabels 1 N = p5z_u9_repeatedLabels N := by
  ext t
  simp only [p5z_u9_repeatLabels, p5z_u9_repeatedLabels, Finset.mem_union,
    Finset.mem_filter, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · rintro (⟨hs, hq⟩ | ⟨hs, hq⟩)
    · exact ⟨hs, Or.inl hq⟩
    · exact ⟨hs, Or.inr hq⟩
  · rintro ⟨hs, hq | hq⟩
    · exact Or.inl ⟨hs, hq⟩
    · exact Or.inr ⟨hs, hq⟩

theorem p5z_u9_repeatLabels_disjoint (N : ℕ) :
    Disjoint (p5z_u9_repeatLabels 0 N) (p5z_u9_repeatLabels 1 N) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  obtain ⟨hs, hq₁⟩ := Finset.mem_filter.mp ht
  have hq₂ := (Finset.mem_filter.mp hu).2
  have hp := (chenY9PrimeSelector_ordered_prime_data
    (p5z_u9_order_source_data hs).1).2.2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hq₁ hq₂
  omega

/-- Equality with the first original prime is owned by the middle branch. -/
theorem p5z_u9_repeatFirst_subset_middle (N : ℕ) :
    p5z_u9_repeatLabels 0 N ⊆ p5z_u9_orderBranch 1 N := by
  intro t ht
  obtain ⟨hs, hq⟩ := Finset.mem_filter.mp ht
  have hp := (chenY9PrimeSelector_ordered_prime_data
    (p5z_u9_order_source_data hs).1).2.2
  have heq : t.2 = t.1.1 := by simpa using hq
  apply Finset.mem_filter.mpr
  exact ⟨hs, by simp [p5z_u9_orderGate, heq, hp]⟩

/-- Equality with the second original prime is owned by the last branch. -/
theorem p5z_u9_repeatSecond_subset_last (N : ℕ) :
    p5z_u9_repeatLabels 1 N ⊆ p5z_u9_orderBranch 2 N := by
  intro t ht
  obtain ⟨hs, hq⟩ := Finset.mem_filter.mp ht
  have heq : t.2 = t.1.2 := by simpa using hq
  apply Finset.mem_filter.mpr
  exact ⟨hs, by simp [p5z_u9_orderGate, heq]⟩

/-- After removing exactly those two explicit exceptions, each branch has
strictly ordered three prime factors. The reverse implication is exact. -/
theorem p5z_u9_orderBranch_strict_iff_not_repeated {N : ℕ} {j : Fin 3} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_orderBranch j N) :
    (p5z_u9_orderedNat j t 0 < p5z_u9_orderedNat j t 1 ∧
      p5z_u9_orderedNat j t 1 < p5z_u9_orderedNat j t 2) ↔
        t ∉ p5z_u9_repeatedLabels N := by
  obtain ⟨hs, hg⟩ := Finset.mem_filter.mp ht
  have hp := (chenY9PrimeSelector_ordered_prime_data
    (p5z_u9_order_source_data hs).1).2.2
  constructor
  · intro hstrict hrep
    have heq := (Finset.mem_filter.mp hrep).2
    fin_cases j <;> simp [p5z_u9_orderGate, p5z_u9_orderedNat] at hg hstrict <;>
      rcases heq with heq | heq <;> omega
  · intro hnot
    have hq₁ : t.2 ≠ t.1.1 := fun heq =>
      hnot (Finset.mem_filter.mpr ⟨hs, Or.inl heq⟩)
    have hq₂ : t.2 ≠ t.1.2 := fun heq =>
      hnot (Finset.mem_filter.mpr ⟨hs, Or.inr heq⟩)
    fin_cases j <;> simp [p5z_u9_orderGate, p5z_u9_orderedNat] at hg ⊢ <;> omega

/-- At a repeated factor the original pair label uniquely determines the
terminal prime. Thus no unweighted product-image argument is needed. -/
theorem p5z_u9_repeatLabels_card_le_selector (j : Fin 2) (N : ℕ) :
    (p5z_u9_repeatLabels j N).card ≤
      (chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ))).card := by
  apply Finset.card_le_card_of_injOn (fun t : P5zU9Triple => t.1)
  · intro t ht
    exact (p5z_u9_order_source_data (Finset.mem_filter.mp ht).1).1
  · intro t ht u hu heq
    have htq := (Finset.mem_filter.mp ht).2
    have huq := (Finset.mem_filter.mp hu).2
    have hv := congrArg (fun p : ℕ × ℕ => ![p.1, p.2] j) heq
    have hq : t.2 = u.2 := htq.trans (hv.trans huq.symm)
    apply Sigma.ext heq
    exact heq_of_eq hq

/-- This is the actual whole selector, not only the existing unit fibres. -/
theorem p5z_u9_selector_subset_rectangle (N : ℕ) :
    chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ)) ⊆
      Finset.range (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ))) ×ˢ
        Finset.range (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ))) := by
  intro p hp
  obtain ⟨hc, _hfirstlo, hfirsthi, _hsecondlo, hsecondhi⟩ := Finset.mem_filter.mp hp
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).1).2.1
  have hp₁one : (1 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast hp₁.one_le
  have hroot : Real.sqrt ((N : ℝ) / (p.1 : ℝ)) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using
      Real.sqrt_le_sqrt (div_le_self (Nat.cast_nonneg N) hp₁one)
  exact Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hfirsthi),
      Finset.mem_range.mpr (Nat.lt_ceil.mpr (hsecondhi.trans_le hroot))⟩

theorem p5z_u9_selector_card_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))).card : ℝ) ≤ 4 * (N : ℝ) ^ (92 / 125 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hcard : ((chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))).card : ℝ) ≤
      (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ) *
        (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) : ℝ) := by
    have h := Finset.card_le_card (p5z_u9_selector_subset_rectangle N)
    simp only [Finset.card_product, Finset.card_range] at h
    exact_mod_cast h
  have hfirstOne : 1 ≤ (N : ℝ) ^ (59 / 250 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hsecondOne : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hfirstCeil : (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (59 / 250 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (59 / 250 : ℝ))
    linarith
  have hsecondCeil : (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (1 / 2 : ℝ))
    linarith
  calc
    _ ≤ (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ) *
        (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) : ℝ) := hcard
    _ ≤ (2 * (N : ℝ) ^ (59 / 250 : ℝ)) * (2 * (N : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul hfirstCeil hsecondCeil (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hNp.le _))
    _ = 4 * (N : ℝ) ^ (92 / 125 : ℝ) := by
      rw [show (92 / 125 : ℝ) = 59 / 250 + 1 / 2 by norm_num, Real.rpow_add hNp]
      ring

theorem p5z_u9_repeatLabels_card_le_power (j : Fin 2) {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((p5z_u9_repeatLabels j N).card : ℝ) ≤ 4 * (N : ℝ) ^ (92 / 125 : ℝ) := by
  have h : ((p5z_u9_repeatLabels j N).card : ℝ) ≤
      ((chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
        ((N : ℝ) ^ (59 / 250 : ℝ))).card : ℝ) := by
    exact_mod_cast p5z_u9_repeatLabels_card_le_selector j N
  exact h.trans (p5z_u9_selector_card_le_power hN)

/-- The two disjoint exceptional families have a fully paid sublinear
cardinality budget, while retaining their exact original labels. -/
theorem p5z_u9_repeatedLabels_card_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    ((p5z_u9_repeatedLabels N).card : ℝ) ≤ 8 * (N : ℝ) ^ (92 / 125 : ℝ) := by
  have h0 := p5z_u9_repeatLabels_card_le_power (0 : Fin 2) hN
  have h1 := p5z_u9_repeatLabels_card_le_power (1 : Fin 2) hN
  have hcard : ((p5z_u9_repeatedLabels N).card : ℝ) =
      ((p5z_u9_repeatLabels 0 N).card : ℝ) + ((p5z_u9_repeatLabels 1 N).card : ℝ) := by
    rw [← p5z_u9_repeatLabels_union N,
      Finset.card_union_of_disjoint (p5z_u9_repeatLabels_disjoint N), Nat.cast_add]
  linarith only [hcard, h0, h1]

theorem eventually_p5z_u9_repeatedLabels_card_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((p5z_u9_repeatedLabels N).card : ℝ) ≤ ε * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    8 (92 / 125) 0 (by norm_num) ε hε
  filter_upwards [hpower, eventually_ge_atTop (1 : ℕ)] with N hpower hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (p5z_u9_repeatedLabels_card_le_power hNr).trans
  simpa only [pow_zero, mul_one] using hpower

/-- Exact receiver-prime restoration on the repeated exceptional family. -/
theorem p5z_u9_repeatedPrimeTriples_eq_filtered_source (N : ℕ) :
    (currentChenUpsilon9PrimeTriples N).filter
      (fun t => t.2 = t.1.1 ∨ t.2 = t.1.2) =
        (p5z_u9_repeatedLabels N).filter
          (fun t => p5z_u9_product t < N ∧ Nat.Prime (N - p5z_u9_product t)) := by
  rw [← p5z_u9_switchedLabels_filter_eq_primeTriples N]
  ext t
  simp only [p5z_u9_repeatedLabels, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hs, hprime⟩, hrepeat⟩
    exact ⟨⟨hs, hrepeat⟩, hprime⟩
  · rintro ⟨⟨hs, hrepeat⟩, hprime⟩
    exact ⟨⟨hs, hprime⟩, hrepeat⟩

/-- The repeated part of the original actual prime triples is a subset
of precisely this explicit unfiltered exceptional family. -/
theorem p5z_u9_repeatedPrimeTriples_subset (N : ℕ) :
    (currentChenUpsilon9PrimeTriples N).filter
      (fun t => t.2 = t.1.1 ∨ t.2 = t.1.2) ⊆ p5z_u9_repeatedLabels N := by
  intro t ht
  obtain ⟨hprime, heq⟩ := Finset.mem_filter.mp ht
  rw [← p5z_u9_switchedLabels_filter_eq_primeTriples N] at hprime
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hprime).1, heq⟩

theorem eventually_p5z_u9_repeatedPrimeTriples_card_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (((currentChenUpsilon9PrimeTriples N).filter
        (fun t => t.2 = t.1.1 ∨ t.2 = t.1.2)).card : ℝ) ≤
          ε * singularNormalization N := by
  filter_upwards [eventually_p5z_u9_repeatedLabels_card_le_singularNormalization ε hε]
    with N hbudget
  have hc : (((currentChenUpsilon9PrimeTriples N).filter
      (fun t => t.2 = t.1.1 ∨ t.2 = t.1.2)).card : ℝ) ≤
        ((p5z_u9_repeatedLabels N).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (p5z_u9_repeatedPrimeTriples_subset N)
  exact hc.trans hbudget

end

end ImbalancedChen
