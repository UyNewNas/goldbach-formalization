import ImbalancedChen.CurrentChenUpsilon9PrimeSource
import ImbalancedChen.OrderedBad

/-!
# The actual ninth product coefficient

The original half-open prime bands separate the two factors.  Ordered
prime-factor uniqueness therefore makes their product injective on the
literal selector, without a multiplicity hypothesis.  Its image supplies
a zero-one coefficient independent of the later sieve modulus.

The actual product band is `N^(97/250) <= a < N^(309/500)`.  Reindexing the
prime fibres preserves the square-root cutoff exactly; only after the
quotient is proved prime is that cutoff dropped in a finite upper bound.
No coprimality gate in the later Pan main term is removed in this module.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- The ninth selector itself forces strict ordered prime factors. -/
theorem chenY9PrimeSelector_ordered_prime_data {N : ℕ} {H D : ℝ}
    {t : ℕ × ℕ} (ht : t ∈ chenY9PrimeSelector N H D) :
    Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ t.1 < t.2 := by
  obtain ⟨hc, _, hfirst, hsecond, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  refine ⟨(mem_chenAdditivePrimeCarrier.mp hc₁).2.1,
    (mem_chenAdditivePrimeCarrier.mp hc₂).2.1, ?_⟩
  exact_mod_cast hfirst.trans_le hsecond

/-- The actual bands pay the product multiplicity before any analytic
coefficient is formed.  This reuses ordered prime-factor uniqueness. -/
theorem chenY9PrimeSelector_multiplier_injOn (N : ℕ) (H D : ℝ) :
    Set.InjOn (fun t : ℕ × ℕ => t.1 * t.2)
      (chenY9PrimeSelector N H D : Set (ℕ × ℕ)) := by
  intro t ht u hu hprod
  obtain ⟨ht₁, ht₂, hto⟩ := chenY9PrimeSelector_ordered_prime_data ht
  obtain ⟨hu₁, hu₂, huo⟩ := chenY9PrimeSelector_ordered_prime_data hu
  obtain ⟨h₁, h₂⟩ := ordered_prime_factors_unique
    ht₁ ht₂ hu₁ hu₂ hto.le huo.le hprod
  exact Prod.ext h₁ h₂

/-- The product image of the literal current ninth selector. -/
def currentChenUpsilon9PrefixProducts (N : ℕ) : Finset ℕ :=
  (chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
    ((N : ℝ) ^ (59 / 250 : ℝ))).image (fun t => t.1 * t.2)

/-- The actual bounded Pan coefficient; there is no modulus argument. -/
def currentChenUpsilon9ProductCoefficient (N a : ℕ) : ℝ :=
  if a ∈ currentChenUpsilon9PrefixProducts N then 1 else 0

/-- This is a proved bound on the actual coefficient, not a supplier
premise about an arbitrary coefficient. -/
theorem abs_currentChenUpsilon9ProductCoefficient_le_one (N a : ℕ) :
    |currentChenUpsilon9ProductCoefficient N a| ≤ 1 := by
  by_cases ha : a ∈ currentChenUpsilon9PrefixProducts N <;>
    simp only [currentChenUpsilon9ProductCoefficient, ha, if_true, if_false,
      abs_one, abs_zero, zero_le_one, le_refl]

/-- Every prefix-product label is positive and retains centre coprimality. -/
theorem currentChenUpsilon9PrefixProducts_data {N a : ℕ}
    (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    0 < a ∧ Nat.Coprime a N := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨hc, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp hc
  have hp₁ := mem_chenAdditivePrimeCarrier.mp hc₁
  have hp₂ := mem_chenAdditivePrimeCarrier.mp hc₂
  exact ⟨mul_pos hp₁.2.1.pos hp₂.2.1.pos, hp₁.2.2.mul_left hp₂.2.2⟩

/-- Both current endpoints follow from actual selector membership.  The
upper endpoint uses the moving square-root wall and the strict first cap. -/
theorem currentChenUpsilon9_multiplier_power_bounds {N : ℕ} {t : ℕ × ℕ}
    (hN : (1 : ℝ) ≤ N)
    (ht : t ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ))) :
    (N : ℝ) ^ (97 / 250 : ℝ) ≤ ((t.1 * t.2 : ℕ) : ℝ) ∧
      ((t.1 * t.2 : ℕ) : ℝ) < (N : ℝ) ^ (309 / 500 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  obtain ⟨hc, hH, hfirst, hsecond, hcap⟩ := Finset.mem_filter.mp ht
  obtain ⟨hc₁, _⟩ := Finset.mem_product.mp hc
  have hp₁ : (0 : ℝ) < t.1 := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hc₁).2.1.pos
  have hlo : (N : ℝ) ^ (19 / 125 : ℝ) * (N : ℝ) ^ (59 / 250 : ℝ) ≤
      ((t.1 * t.2 : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact mul_le_mul hH hsecond (Real.rpow_nonneg hNp.le _) (Nat.cast_nonneg _)
  have hcapsq : (t.2 : ℝ) ^ 2 < (N : ℝ) / (t.1 : ℝ) := by
    have h := (sq_lt_sq₀ (Nat.cast_nonneg t.2) (Real.sqrt_nonneg _)).mpr hcap
    rwa [Real.sq_sqrt (div_nonneg hNp.le hp₁.le)] at h
  have hcapmul : (t.2 : ℝ) ^ 2 * (t.1 : ℝ) < (N : ℝ) :=
    (lt_div_iff₀ hp₁).mp hcapsq
  have hprodsq : ((t.1 : ℝ) * (t.2 : ℝ)) ^ 2 < (N : ℝ) * (t.1 : ℝ) := by
    have h := mul_lt_mul_of_pos_right hcapmul hp₁
    nlinarith only [h]
  have hfirstmul : (N : ℝ) * (t.1 : ℝ) <
      (N : ℝ) * (N : ℝ) ^ (59 / 250 : ℝ) :=
    mul_lt_mul_of_pos_left hfirst hNp
  have hpowersq : ((N : ℝ) ^ (309 / 500 : ℝ)) ^ 2 =
      (N : ℝ) * (N : ℝ) ^ (59 / 250 : ℝ) := by
    rw [← Real.rpow_mul_natCast hNp.le (309 / 500 : ℝ) 2,
      show (309 / 500 : ℝ) * ((2 : ℕ) : ℝ) = 1 + 59 / 250 by norm_num,
      Real.rpow_add hNp, Real.rpow_one]
  constructor
  · rw [← Real.rpow_add hNp] at hlo
    convert hlo using 1
    norm_num
  · rw [Nat.cast_mul]
    apply (sq_lt_sq₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.rpow_nonneg hNp.le _)).mp
    rw [hpowersq]
    exact hprodsq.trans hfirstmul

/-- The same band belongs to each actual zero-one coefficient label. -/
theorem currentChenUpsilon9PrefixProducts_power_bounds {N a : ℕ}
    (hN : (1 : ℝ) ≤ N) (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    (N : ℝ) ^ (97 / 250 : ℝ) ≤ (a : ℝ) ∧
      (a : ℝ) < (N : ℝ) ^ (309 / 500 : ℝ) := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
  exact currentChenUpsilon9_multiplier_power_bounds hN ht

/-- The exact natural interval for the supplier's `A₁ < a <= A₂`
convention.  The ceiling-minus-one preserves both real endpoints. -/
def currentChenUpsilon9PanLower (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (97 / 250 : ℝ)) - 1

def currentChenUpsilon9PanUpper (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) - 1

/-- Every actual product label is in this same natural Pan interval. -/
theorem currentChenUpsilon9PrefixProducts_subset_pan_interval {N : ℕ}
    (hN : (1 : ℝ) ≤ N) :
    currentChenUpsilon9PrefixProducts N ⊆
      Finset.Ioc (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N) := by
  intro a ha
  obtain ⟨hlo, hhi⟩ := currentChenUpsilon9PrefixProducts_power_bounds hN ha
  have hceil : Nat.ceil ((N : ℝ) ^ (97 / 250 : ℝ)) ≤ a := Nat.ceil_le.mpr hlo
  have hceilpos : 1 ≤ Nat.ceil ((N : ℝ) ^ (97 / 250 : ℝ)) :=
    Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (zero_lt_one.trans_le hN) _)
  have hceilhi : a < Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) := Nat.lt_ceil.mpr hhi
  apply Finset.mem_Ioc.mpr
  dsimp [currentChenUpsilon9PanLower, currentChenUpsilon9PanUpper]
  omega

/-- The actual image sum is the same bounded coefficient on the full
source interval, with no factor counting pairs or possible factorizations. -/
theorem currentChenUpsilon9ProductCoefficient_sum {N : ℕ}
    (hN : (1 : ℝ) ≤ N) (G : ℕ → ℝ) :
    (∑ a ∈ Finset.Ioc (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N),
      currentChenUpsilon9ProductCoefficient N a * G a) =
        ∑ a ∈ currentChenUpsilon9PrefixProducts N, G a := by
  have hfilter :
      (Finset.Ioc (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N)).filter
        (fun a => a ∈ currentChenUpsilon9PrefixProducts N) =
          currentChenUpsilon9PrefixProducts N := by
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,
      fun ha => ⟨currentChenUpsilon9PrefixProducts_subset_pan_interval hN ha, ha⟩⟩
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ currentChenUpsilon9PrefixProducts N <;>
    simp only [currentChenUpsilon9ProductCoefficient, ha, if_true, if_false, one_mul, zero_mul]

/-- Reindexing the prime quotient fibres uses the proved product
injection and preserves the original coupled cutoff exactly. -/
theorem currentChenUpsilon9PrimeTriples_card_eq_product_fibres (N : ℕ) :
    ((currentChenUpsilon9PrimeTriples N).card : ℝ) =
      ∑ a ∈ currentChenUpsilon9PrefixProducts N,
        (((chenSiftedQuotientPrimeSource N a
          (Real.sqrt ((N : ℝ) / (a : ℝ)))).filter Nat.Prime).card : ℝ) := by
  rw [currentChenUpsilon9PrimeTriples, Finset.card_sigma, Nat.cast_sum,
    currentChenUpsilon9PrefixProducts,
    Finset.sum_image (chenY9PrimeSelector_multiplier_injOn N
      ((N : ℝ) ^ (19 / 125 : ℝ)) ((N : ℝ) ^ (59 / 250 : ℝ)))]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Nat.cast_mul]

/-- The switched prime fibre after dropping only the coupled cutoff.
The original additive prime and its centre-coprimality mask remain. -/
def currentChenUpsilon9SwitchedPrimeFibre (N a : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun q =>
    Nat.Prime q ∧ a * q < N ∧ N - a * q ∈ chenAdditivePrimeCarrier N

/-- A literal prime quotient belongs to the broader switched prime
fibre.  Primality is already established before the moving cutoff is lost. -/
theorem currentChenUpsilon9_prime_fibre_subset_switched {N a : ℕ}
    (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    (chenSiftedQuotientPrimeSource N a
      (Real.sqrt ((N : ℝ) / (a : ℝ)))).filter Nat.Prime ⊆
        currentChenUpsilon9SwitchedPrimeFibre N a := by
  intro q hq
  obtain ⟨hqsource, hprime⟩ := Finset.mem_filter.mp hq
  obtain ⟨hlt, hP, _⟩ :=
    (currentChenUpsilon9_prime_mem_iff
      (currentChenUpsilon9PrefixProducts_data ha).1 hprime _).mp hqsource
  have hqN := (chenQuotientPrimeSource_data (Finset.mem_filter.mp hqsource).1).2.1
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hqN), hprime, hlt, hP⟩

/-- The actual ninth count is bounded by the same product-coefficient
prime source and its separately retained actual unit fibres. -/
theorem currentChenUpsilon9_le_switched_prime_fibres_add_unitFibres (N : ℕ) :
    currentChenUpsilon9 N ≤
      (∑ a ∈ currentChenUpsilon9PrefixProducts N,
        ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)) +
          ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon9_eq_primeTriples_add_unitFibres,
    currentChenUpsilon9PrimeTriples_card_eq_product_fibres]
  refine add_le_add ?_ (le_refl _)
  apply Finset.sum_le_sum
  intro a ha
  exact_mod_cast Finset.card_le_card
    (currentChenUpsilon9_prime_fibre_subset_switched ha)

/-- The same literal switched count now carries the modulus-independent
bounded coefficient in Pan's actual source-window convention. -/
theorem currentChenUpsilon9_le_same_coefficient_switched_count {N : ℕ}
    (hN : (1 : ℝ) ≤ N) :
    currentChenUpsilon9 N ≤
      (∑ a ∈ Finset.Ioc (currentChenUpsilon9PanLower N) (currentChenUpsilon9PanUpper N),
        currentChenUpsilon9ProductCoefficient N a *
          ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)) +
            ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  rw [currentChenUpsilon9ProductCoefficient_sum hN]
  exact currentChenUpsilon9_le_switched_prime_fibres_add_unitFibres N

end

end ImbalancedChen
