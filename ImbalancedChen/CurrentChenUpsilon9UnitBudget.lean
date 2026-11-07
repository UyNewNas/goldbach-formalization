import ImbalancedChen.CurrentChenUpsilon9PrimeSource
import ImbalancedChen.PowerErrorBudget

/-!
# The actual ninth unit fibres have negligible normalized cost

Every unit fibre retains its original pair label.  The literal selector
places that pair inside a rectangle of side lengths `ceil (N^(59/250))`
and `ceil (N^(1/2))`.  Counting this rectangle gives the actual finite
bound `4*N^(92/125)` for `N ≥ 1`.  The proved power-error budget then
absorbs this count into any positive multiple of `singularNormalization`.

There is no product-image injectivity assumption and no analytic premise.
-/

namespace ImbalancedChen

open Filter Topology
open scoped BigOperators
open Classical

noncomputable section

/-- The actual unit pair labels lie in this literal finite rectangle.
The second coordinate bound follows from the actual first prime being
at least one, without simplifying the original selector by assumption. -/
theorem currentChenUpsilon9_unitFibres_subset_rectangle (N : ℕ) :
    currentChenUpsilon9UnitFibres N ⊆
      Finset.range (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ))) ×ˢ
        Finset.range (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ))) := by
  intro t ht
  have htselector := (Finset.mem_filter.mp ht).1
  obtain ⟨hcarrier, _, h₁D, _, hcap⟩ := Finset.mem_filter.mp htselector
  obtain ⟨h₁, _⟩ := Finset.mem_product.mp hcarrier
  have hp₁ := (mem_chenAdditivePrimeCarrier.mp h₁).2.1
  have hp₁real : (1 : ℝ) ≤ (t.1 : ℝ) := by exact_mod_cast hp₁.one_le
  have hsqrt : Real.sqrt ((N : ℝ) / (t.1 : ℝ)) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) := by
    simpa only [Real.sqrt_eq_rpow] using
      Real.sqrt_le_sqrt (div_le_self (Nat.cast_nonneg N) hp₁real)
  apply Finset.mem_product.mpr
  exact ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr h₁D),
    Finset.mem_range.mpr (Nat.lt_ceil.mpr (hcap.trans_le hsqrt))⟩

/-- Counting the rectangle retains every pair multiplicity and gives a
natural-valued finite bound on the actual unit fibres. -/
theorem currentChenUpsilon9_unitFibres_card_le_rectangle (N : ℕ) :
    (currentChenUpsilon9UnitFibres N).card ≤
      Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) *
        Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) := by
  have hcard := Finset.card_le_card
    (currentChenUpsilon9_unitFibres_subset_rectangle N)
  simpa only [Finset.card_product, Finset.card_range] using hcard

/-- The precise sublinear exponent of this actual unit count is
`59/250 + 1/2 = 92/125 < 1`.  The factor four pays both ceiling losses. -/
theorem currentChenUpsilon9_unitFibres_card_le_power {N : ℕ} (hN : 1 ≤ N) :
    ((currentChenUpsilon9UnitFibres N).card : ℝ) ≤
      4 * (N : ℝ) ^ (92 / 125 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le zero_lt_one hNreal
  have hfirst : 1 ≤ (N : ℝ) ^ (59 / 250 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hsecond : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hceilfirst : (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (59 / 250 : ℝ) := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg N) (59 / 250 : ℝ))
    linarith
  have hceilsecond : (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) : ℝ) ≤
      2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
    have hceil := Nat.ceil_lt_add_one
      (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 2 : ℝ))
    linarith
  have hcard : ((currentChenUpsilon9UnitFibres N).card : ℝ) ≤
      (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ) *
        (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) : ℝ) := by
    exact_mod_cast currentChenUpsilon9_unitFibres_card_le_rectangle N
  calc
    ((currentChenUpsilon9UnitFibres N).card : ℝ) ≤
        (Nat.ceil ((N : ℝ) ^ (59 / 250 : ℝ)) : ℝ) *
          (Nat.ceil ((N : ℝ) ^ (1 / 2 : ℝ)) : ℝ) := hcard
    _ ≤ (2 * (N : ℝ) ^ (59 / 250 : ℝ)) *
        (2 * (N : ℝ) ^ (1 / 2 : ℝ)) :=
      mul_le_mul hceilfirst hceilsecond (Nat.cast_nonneg _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = 4 * (N : ℝ) ^ (92 / 125 : ℝ) := by
      rw [show (92 / 125 : ℝ) = 59 / 250 + 1 / 2 by norm_num,
        Real.rpow_add hNpos]
      ring

/-- The actual ninth unit fibres cost an arbitrarily small multiple of
the manuscript's genuine singular normalization, on all large naturals. -/
theorem eventually_currentChenUpsilon9_unitFibres_le_singularNormalization
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((currentChenUpsilon9UnitFibres N).card : ℝ) ≤
        ε * singularNormalization N := by
  have hpower := eventually_powerLog_le_singularNormalization
    4 (92 / 125) 0 (by norm_num) ε hε
  filter_upwards [hpower, eventually_ge_atTop (1 : ℕ)] with N hbudget hN
  apply (currentChenUpsilon9_unitFibres_card_le_power hN).trans
  simpa only [pow_zero, mul_one] using hbudget

end

end ImbalancedChen
