import ImbalancedChen.P5U7OriginalInteriorBandError
import ImbalancedChen.P5U7OriginalRawMean

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual marked arithmetic rows are covered by the closed multiplicative
interior and the thin arithmetic boundary. Their overlap is retained in
an upper bound. Positivity bounds the closed interior main by the full
original main, so eta is removed without equating it with the distinct
strict affine gate used by prime-box transport.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set LiLiuPrereqBuchstab
open scoped BigOperators
open Classical

def p5U7OriginalRowMass (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  ((p5U7MassPrimeFibre N (t.1 * t.2) t.2).card : ℝ) +
    ((p5U7MassSemiprimePairs N t).card : ℝ)

theorem p5U7OriginalRowMass_nonneg (N : ℕ) (t : ℕ × ℕ) :
    0 ≤ p5U7OriginalRowMass N t := by
  unfold p5U7OriginalRowMass
  positivity

theorem p5U7Original_arithmetic_mass_eq_rows (N : ℕ) :
    ((p5U7ArithmeticThree N).card : ℝ) +
      ((p5U7ArithmeticFour N).card : ℝ) =
    ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
      p5U7OriginalRowMass N t := by
  have hfour : ((p5U7ArithmeticFour N).card : ℝ) =
      ∑ t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ)),
        ((p5U7MassSemiprimePairs N t).card : ℝ) := by
    change (((chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))).sigma
      (p5U7MassSemiprimePairs N)).card : ℝ) = _
    simp only [Finset.card_sigma, Nat.cast_sum]
  rw [p5U7Mass_three_card_eq_primeFibres, hfour, ← Finset.sum_add_distrib]
  rfl

theorem p5U7Original_boundary_mass_eq_rows (N : ℕ) (eta : ℝ) :
    ((p5U7BoundaryThree N eta).card : ℝ) +
      ((p5U7BoundaryFour N eta).card : ℝ) =
    ∑ t ∈ p5U7BoundaryPairs N eta, p5U7OriginalRowMass N t := by
  have heq : p5U7BoundaryFour N eta =
      (p5U7BoundaryPairs N eta).sigma (p5U7MassSemiprimePairs N) := by
    ext x
    simp only [p5U7BoundaryFour, p5U7BoundaryPairs, p5U7ArithmeticFour,
      p5U7MassSemiprimePairs, Finset.mem_filter, Finset.mem_sigma]
    constructor
    · rintro ⟨⟨ht, hq⟩, hg⟩
      exact ⟨⟨ht, hg⟩, hq⟩
    · rintro ⟨⟨ht, hg⟩, hq⟩
      exact ⟨⟨ht, hq⟩, hg⟩
  rw [p5U7Boundary_three_card_eq_primeFibres, heq]
  simp only [Finset.card_sigma, Nat.cast_sum, ← Finset.sum_add_distrib]
  rfl

/-- The two closed collars cover every actual row. Double ownership on
their common wall is harmless because every row has nonnegative mass. -/
theorem p5U7Original_rows_le_interior_add_boundary (N : ℕ) (eta : ℝ) :
    ((p5U7ArithmeticThree N).card : ℝ) +
      ((p5U7ArithmeticFour N).card : ℝ) ≤
    (∑ t ∈ p5U7InteriorPairs N eta, p5U7OriginalRowMass N t) +
      (((p5U7BoundaryThree N eta).card : ℝ) +
        ((p5U7BoundaryFour N eta).card : ℝ)) := by
  rw [p5U7Original_arithmetic_mass_eq_rows,
    p5U7Original_boundary_mass_eq_rows]
  unfold p5U7InteriorPairs p5U7BoundaryPairs
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  by_cases hi : (1 + eta) * Real.log (t.2 : ℝ) ≤
      Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ))
  · rw [if_pos hi]
    by_cases hb : p5U7BoundaryGate N eta t
    · rw [if_pos hb]
      linarith [p5U7OriginalRowMass_nonneg N t]
    · rw [if_neg hb, add_zero]
  · have hb : p5U7BoundaryGate N eta t := (le_of_not_ge hi)
    rw [if_neg hi, if_pos hb, zero_add]

theorem p5U7Original_main_row_nonneg {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    0 ≤ ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) *
      buchstab (Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
        Real.log (t.2 : ℝ)) / Real.log (t.2 : ℝ) := by
  have hg := p5U7Mass_outer_geometry ht
  obtain ⟨hc, _, _, _⟩ := Finset.mem_filter.mp ht
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hqR : (1 : ℝ) < t.2 := by exact_mod_cast hq.one_lt
  have hlog : 0 < Real.log (t.2 : ℝ) := Real.log_pos hqR
  have hx : 0 < (N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ) :=
    (zero_lt_one.trans hqR).trans hg.2.2.1
  have hs : 1 ≤ Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) /
      Real.log (t.2 : ℝ) := by
    apply (le_div_iff₀ hlog).mpr
    simpa only [one_mul] using
      (Real.log_le_log (zero_lt_one.trans hqR) hg.2.2.1.le)
  exact div_nonneg (mul_nonneg hx.le (buchstab_nonneg hs)) hlog.le

theorem p5U7InteriorBandMain_le_full (N : ℕ) (eta : ℝ) :
    p5U7InteriorBandMain N eta ≤ p5U7MassBuchstabMain N := by
  unfold p5U7InteriorBandMain p5U7MassBuchstabMain
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun t ht _ => p5U7Original_main_row_nonneg ht)

/-- The actual s-to-one boundary has now been removed. Eta is chosen
before N and then paid by the unconditional finite prime-window bound. -/
theorem p5U7Original_eventually_arithmetic_mass_le_main
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ((p5U7ArithmeticThree N).card : ℝ) +
        ((p5U7ArithmeticFour N).card : ℝ) ≤
      p5U7MassBuchstabMain N + epsilon * ((N : ℝ) / Real.log (N : ℝ)) := by
  let eta : ℝ := min 1 (epsilon / 200)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta1 : eta ≤ 1 := min_le_left _ _
  have hetae : 50 * eta ≤ epsilon / 4 := by
    have h := min_le_right (1 : ℝ) (epsilon / 200)
    dsimp [eta]
    linarith
  filter_upwards [p5U7Interior_eventually_arithmetic_rows_le_main eta heta
      (epsilon / 4) (by positivity),
    p5U7Boundary_eventually_arithmetic_mass_le (epsilon / 4) (by positivity),
    eventually_ge_atTop (2 : ℕ)] with N hi hb hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := by positivity
  have hcover := p5U7Original_rows_le_interior_add_boundary N eta
  have hbound := hb eta heta.le heta1
  have hmain := p5U7InteriorBandMain_le_full N eta
  change (∑ t ∈ p5U7InteriorPairs N eta, p5U7OriginalRowMass N t) ≤
    p5U7InteriorBandMain N eta + (epsilon / 4) *
      ((N : ℝ) / Real.log (N : ℝ)) at hi
  nlinarith only [hcover, hi, hbound, hmain,
    mul_le_mul_of_nonneg_right hetae hs, mul_nonneg hepsilon.le hs]

end

end ImbalancedChen
