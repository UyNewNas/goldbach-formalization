import ImbalancedChen.CurrentChenUpsilon9ProductCoefficient
import ImbalancedChen.CurrentChenUpsilon9UnitBudget

/-!
# The genuine ninth cutoff has only a sublinear switched-count defect

This source-only prerequisite keeps the literal `sqrt (N / (p₁*p₂))`.
The prime part of the original ninth count is exactly the switched prime
fibre restricted by that cutoff.  The complementary small-quotient fibres
have total cardinality at most `4*N^(231/250)`, and therefore have arbitrarily
small cost in the original singular normalization.

In particular, restoring this cutoff cannot by itself justify replacing the
ordinary leading coefficient eight by the manuscript's original `currentK`.
No density or desired U9 bound is assumed here.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical

/-- Actual switched prime quotients excluded by the original ninth cutoff.
The receiver prime and its centre-coprimality mask are retained. -/
def currentChenP5U9SmallQuotientFibre (N a : ℕ) : Finset ℕ :=
  (currentChenUpsilon9SwitchedPrimeFibre N a).filter fun q =>
    (q : ℝ) < Real.sqrt ((N : ℝ) / (a : ℝ))

/-- The whole actual switched prime mass, before imposing the moving
prime-quotient cutoff and before adding the original unit fibres. -/
def currentChenP5U9SwitchedPrimeMass (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N,
    ((currentChenUpsilon9SwitchedPrimeFibre N a).card : ℝ)

/-- The finite mass deleted by the original moving square-root cutoff. -/
def currentChenP5U9CutoffDefect (N : ℕ) : ℝ :=
  ∑ a ∈ currentChenUpsilon9PrefixProducts N,
    ((currentChenP5U9SmallQuotientFibre N a).card : ℝ)

/-- Exact restoration of the original `sqrt(N/a)` cutoff, with the actual
product label `a=p₁*p₂` unchanged. -/
theorem currentChenP5U9_primeFibre_eq_switched_filter {N a : ℕ}
    (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    (chenSiftedQuotientPrimeSource N a
      (Real.sqrt ((N : ℝ) / (a : ℝ)))).filter Nat.Prime =
        (currentChenUpsilon9SwitchedPrimeFibre N a).filter
          (fun q => Real.sqrt ((N : ℝ) / (a : ℝ)) ≤ (q : ℝ)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hqsource, hqprime⟩ := Finset.mem_filter.mp hq
    have hdata := (currentChenUpsilon9_prime_mem_iff
      (currentChenUpsilon9PrefixProducts_data ha).1 hqprime _).mp hqsource
    exact Finset.mem_filter.mpr
      ⟨currentChenUpsilon9_prime_fibre_subset_switched ha hq, hdata.2.2⟩
  · intro hq
    obtain ⟨hqswitched, hcut⟩ := Finset.mem_filter.mp hq
    obtain ⟨_hqN, hqprime, hlt, hreceiver⟩ := Finset.mem_filter.mp hqswitched
    exact Finset.mem_filter.mpr
      ⟨(currentChenUpsilon9_prime_mem_iff
        (currentChenUpsilon9PrefixProducts_data ha).1 hqprime _).mpr
          ⟨hlt, hreceiver, hcut⟩, hqprime⟩

/-- The two sides own the equality endpoint exactly: equality belongs to
the original prime source, and the defect is strictly below the cutoff. -/
theorem currentChenP5U9_primeFibre_card_partition {N a : ℕ}
    (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    ((chenSiftedQuotientPrimeSource N a
      (Real.sqrt ((N : ℝ) / (a : ℝ)))).filter Nat.Prime).card +
        (currentChenP5U9SmallQuotientFibre N a).card =
          (currentChenUpsilon9SwitchedPrimeFibre N a).card := by
  rw [currentChenP5U9_primeFibre_eq_switched_filter ha]
  simpa only [currentChenP5U9SmallQuotientFibre, not_le] using
    Finset.card_filter_add_card_filter_not
      (s := currentChenUpsilon9SwitchedPrimeFibre N a)
      (fun q => Real.sqrt ((N : ℝ) / (a : ℝ)) ≤ (q : ℝ))

theorem currentChenP5U9CutoffDefect_nonneg (N : ℕ) :
    0 ≤ currentChenP5U9CutoffDefect N := by
  exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- An exact finite count identity.  Neither the small-quotient defect nor
the original unit fibres is discarded or hidden in an analytic premise. -/
theorem currentChenP5U9_switched_add_units_eq_original_add_defect (N : ℕ) :
    currentChenP5U9SwitchedPrimeMass N +
      ((currentChenUpsilon9UnitFibres N).card : ℝ) =
        currentChenUpsilon9 N + currentChenP5U9CutoffDefect N := by
  have hsum :
      (∑ a ∈ currentChenUpsilon9PrefixProducts N,
        (((chenSiftedQuotientPrimeSource N a
          (Real.sqrt ((N : ℝ) / (a : ℝ)))).filter Nat.Prime).card : ℝ)) +
          currentChenP5U9CutoffDefect N = currentChenP5U9SwitchedPrimeMass N := by
    unfold currentChenP5U9CutoffDefect currentChenP5U9SwitchedPrimeMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    exact_mod_cast currentChenP5U9_primeFibre_card_partition ha
  rw [currentChenUpsilon9_eq_primeTriples_add_unitFibres,
    currentChenUpsilon9PrimeTriples_card_eq_product_fibres]
  linarith only [hsum]

/-- Both actual product endpoints, rather than a new source-window
assumption, bound every original square-root cutoff uniformly. -/
theorem currentChenP5U9_sqrt_cutoff_le_power {N a : ℕ}
    (hN : (1 : ℝ) ≤ N) (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    Real.sqrt ((N : ℝ) / (a : ℝ)) ≤ (N : ℝ) ^ (153 / 500 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hap : (0 : ℝ) < a := by
    exact_mod_cast (currentChenUpsilon9PrefixProducts_data ha).1
  have hquot : (N : ℝ) / (a : ℝ) ≤ (N : ℝ) ^ (153 / 250 : ℝ) := by
    apply (div_le_iff₀ hap).mpr
    calc
      (N : ℝ) = (N : ℝ) ^ (153 / 250 : ℝ) *
          (N : ℝ) ^ (97 / 250 : ℝ) := by
        rw [← Real.rpow_add hNp,
          show (153 / 250 : ℝ) + 97 / 250 = 1 by norm_num, Real.rpow_one]
      _ ≤ (N : ℝ) ^ (153 / 250 : ℝ) * (a : ℝ) :=
        mul_le_mul_of_nonneg_left
          (currentChenUpsilon9PrefixProducts_power_bounds hN ha).1
          (Real.rpow_nonneg hNp.le _)
  have hpow : ((N : ℝ) ^ (153 / 500 : ℝ)) ^ 2 =
      (N : ℝ) ^ (153 / 250 : ℝ) := by
    rw [← Real.rpow_mul_natCast hNp.le (153 / 500 : ℝ) 2]
    congr 1
    norm_num
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.rpow_nonneg hNp.le _)).mp
  rw [Real.sq_sqrt (div_nonneg hNp.le hap.le), hpow]
  exact hquot

/-- The actual deleted prime fibre lies in this finite natural range;
its receiver primality has not been used to reduce its cardinality. -/
theorem currentChenP5U9_smallQuotientFibre_card_le {N a : ℕ}
    (hN : (1 : ℝ) ≤ N) (ha : a ∈ currentChenUpsilon9PrefixProducts N) :
    (currentChenP5U9SmallQuotientFibre N a).card ≤
      Nat.ceil ((N : ℝ) ^ (153 / 500 : ℝ)) := by
  have hsubset : currentChenP5U9SmallQuotientFibre N a ⊆
      Finset.range (Nat.ceil ((N : ℝ) ^ (153 / 500 : ℝ))) := by
    intro q hq
    have hcut := (Finset.mem_filter.mp hq).2
    exact Finset.mem_range.mpr (Nat.lt_ceil.mpr
      (hcut.trans_le (currentChenP5U9_sqrt_cutoff_le_power hN ha)))
  simpa only [Finset.card_range] using Finset.card_le_card hsubset

/-- A genuine sublinear bound on the whole deleted mass.  The exponent is
`309/500 + 153/500 = 231/250 < 1`; four pays both ceiling losses. -/
theorem currentChenP5U9CutoffDefect_le_power {N : ℕ} (hN : (1 : ℝ) ≤ N) :
    currentChenP5U9CutoffDefect N ≤ 4 * (N : ℝ) ^ (231 / 250 : ℝ) := by
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hsubset : currentChenUpsilon9PrefixProducts N ⊆
      Finset.range (Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ))) := by
    intro a ha
    exact Finset.mem_range.mpr
      (Nat.lt_ceil.mpr (currentChenUpsilon9PrefixProducts_power_bounds hN ha).2)
  have hcard : ((currentChenUpsilon9PrefixProducts N).card : ℝ) ≤
      (Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) : ℝ) := by
    have h := Finset.card_le_card hsubset
    rw [Finset.card_range] at h
    exact_mod_cast h
  have hprodOne : 1 ≤ (N : ℝ) ^ (309 / 500 : ℝ) :=
    Real.one_le_rpow hN (by norm_num)
  have hquotOne : 1 ≤ (N : ℝ) ^ (153 / 500 : ℝ) :=
    Real.one_le_rpow hN (by norm_num)
  have hprodCeil : (Nat.ceil ((N : ℝ) ^ (309 / 500 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (309 / 500 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (309 / 500 : ℝ))
    linarith
  have hquotCeil : (Nat.ceil ((N : ℝ) ^ (153 / 500 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (153 / 500 : ℝ) := by
    have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hNp.le (153 / 500 : ℝ))
    linarith
  calc
    currentChenP5U9CutoffDefect N ≤
        ∑ _a ∈ currentChenUpsilon9PrefixProducts N,
          (Nat.ceil ((N : ℝ) ^ (153 / 500 : ℝ)) : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact_mod_cast currentChenP5U9_smallQuotientFibre_card_le hN ha
    _ = ((currentChenUpsilon9PrefixProducts N).card : ℝ) *
        (Nat.ceil ((N : ℝ) ^ (153 / 500 : ℝ)) : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * (N : ℝ) ^ (309 / 500 : ℝ)) *
        (2 * (N : ℝ) ^ (153 / 500 : ℝ)) :=
      mul_le_mul (hcard.trans hprodCeil) hquotCeil (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hNp.le _))
    _ = 4 * (N : ℝ) ^ (231 / 250 : ℝ) := by
      rw [show (231 / 250 : ℝ) = 309 / 500 + 153 / 500 by norm_num,
        Real.rpow_add hNp]
      ring

/-- The actual moving-cutoff defect is negligible in the unchanged
normalization, without a Pan or prime-distribution hypothesis. -/
theorem eventually_currentChenP5U9CutoffDefect_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      currentChenP5U9CutoffDefect N ≤ ε * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    4 (231 / 250) 0 (by norm_num) ε hε
  filter_upwards [hpower, eventually_ge_atTop (1 : ℕ)] with N hbudget hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  apply (currentChenP5U9CutoffDefect_le_power hNr).trans
  simpa only [pow_zero, mul_one] using hbudget

/-- Restoring the literal square-root cutoff and the literal unit fibres
changes the switched count by at most any prescribed normalized error.
This is a proved comparison of actual counts, not an adopted-K premise. -/
theorem eventually_currentChenP5U9_original_close_to_switched
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      currentChenP5U9SwitchedPrimeMass N - ε * singularNormalization N ≤
          currentChenUpsilon9 N ∧
        currentChenUpsilon9 N ≤
          currentChenP5U9SwitchedPrimeMass N + ε * singularNormalization N := by
  filter_upwards [eventually_currentChenP5U9CutoffDefect_le_singularNormalization ε hε,
    eventually_currentChenUpsilon9_unitFibres_le_singularNormalization ε hε]
    with N hdefect hunit
  have hid := currentChenP5U9_switched_add_units_eq_original_add_defect N
  have hdefect0 := currentChenP5U9CutoffDefect_nonneg N
  have hunit0 : (0 : ℝ) ≤ (currentChenUpsilon9UnitFibres N).card := Nat.cast_nonneg _
  constructor <;> linarith only [hid, hdefect, hunit, hdefect0, hunit0]

end

end ImbalancedChen
