import ImbalancedChen.P5U7OriginalBoundaryElimination
import ImbalancedChen.P5U7DoubleTriangularComposition

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
The native band theorem uses a weak multiplicative wall. The double-prime
transport uses its strict counterpart; the triangular transport changes
the intercept instead. This file records their precise finite relations.
All selectors retain original marked pairs and target-N prime exclusions.
The imported double-triangular composition pays its matching diagonal.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators
open Classical

private theorem p5U7Original_pair_log_identity {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) =
      Real.log (N : ℝ) - Real.log (t.1 : ℝ) - Real.log (t.2 : ℝ) := by
  obtain ⟨hc, _, _, _⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  have hp0 : (0 : ℝ) < t.1 := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq0 : (0 : ℝ) < t.2 := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [Nat.cast_mul, Real.log_div hN0.ne' (mul_ne_zero hp0.ne' hq0.ne'),
    Real.log_mul hp0.ne' hq0.ne']
  ring

private theorem p5U7Original_pair_log_order {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    actualPrimeTupleLog N ![t.1, t.2] 0 <
      actualPrimeTupleLog N ![t.1, t.2] 1 := by
  obtain ⟨hc, _, ho, _⟩ := Finset.mem_filter.mp ht
  have hp0 : (0 : ℝ) < t.1 := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).1).2.1.pos
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  change Real.log (t.1 : ℝ) / Real.log (N : ℝ) <
    Real.log (t.2 : ℝ) / Real.log (N : ℝ)
  apply (div_lt_div_iff_of_pos_right hL).mpr
  exact Real.log_lt_log hp0 (by exact_mod_cast ho)

/-- Exact weak wall of the native rough-count band theorem. -/
theorem p5U7InteriorPairs_iff_weak_affine {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    t ∈ p5U7InteriorPairs N eta ↔
      actualPrimeTupleLog N ![t.1, t.2] 0 +
        (2 + eta) * actualPrimeTupleLog N ![t.1, t.2] 1 ≤ 1 := by
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hid := p5U7Original_pair_log_identity hN ht
  simp only [p5U7InteriorPairs, Finset.mem_filter, ht, true_and,
    actualPrimeTupleLog, Matrix.cons_val_zero, Matrix.cons_val_one]
  have heq : Real.log (t.1 : ℝ) / Real.log (N : ℝ) +
      (2 + eta) * (Real.log (t.2 : ℝ) / Real.log (N : ℝ)) =
      (Real.log (t.1 : ℝ) + (2 + eta) * Real.log (t.2 : ℝ)) /
        Real.log (N : ℝ) := by ring
  rw [heq, div_le_iff₀ hL]
  constructor <;> intro h <;> nlinarith only [h, hid]

/-- Exact strict wall of the actual double-prime source. -/
theorem p5U7InteriorSelector_iff_strict_log {N : ℕ} (hN : 2 ≤ N)
    (eta : ℝ) {t : ℕ × ℕ}
    (ht : t ∈ chenY7PrimeSelector N ((N : ℝ) ^ (59 / 250 : ℝ))) :
    t ∈ p5U7InteriorSelector N eta ↔
      (1 + eta) * Real.log (t.2 : ℝ) <
        Real.log ((N : ℝ) / ((t.1 * t.2 : ℕ) : ℝ)) := by
  have hL : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hid := p5U7Original_pair_log_identity hN ht
  have ho := p5U7Original_pair_log_order hN ht
  simp only [p5U7InteriorSelector, Finset.mem_filter, ht, true_and,
    p5U7InteriorRegion_iff, ho, true_and,
    actualPrimeTupleLog, Matrix.cons_val_zero, Matrix.cons_val_one]
  have heq : Real.log (t.1 : ℝ) / Real.log (N : ℝ) +
      (2 + eta) * (Real.log (t.2 : ℝ) / Real.log (N : ℝ)) =
      (Real.log (t.1 : ℝ) + (2 + eta) * Real.log (t.2 : ℝ)) /
        Real.log (N : ℝ) := by ring
  rw [heq, div_lt_iff₀ hL]
  constructor <;> intro h <;> nlinarith only [h, hid]

theorem p5U7InteriorSelector_subset_band {N : ℕ} (hN : 2 ≤ N) (eta : ℝ) :
    p5U7InteriorSelector N eta ⊆ p5U7InteriorPairs N eta := by
  intro t ht
  have ho := (Finset.mem_filter.mp ht).1
  apply Finset.mem_filter.mpr
  exact ⟨ho, ((p5U7InteriorSelector_iff_strict_log hN eta ho).mp ht).le⟩

/-- A weak eta band fits the strict eta/2 band. Equality on the old wall
is kept and the positive amount eta/2 pays it. -/
theorem p5U7InteriorPairs_subset_half_selector {N : ℕ} (hN : 2 ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    p5U7InteriorPairs N eta ⊆ p5U7InteriorSelector N (eta / 2) := by
  intro t ht
  obtain ⟨ho, hgate⟩ := Finset.mem_filter.mp ht
  have hc := (Finset.mem_filter.mp ho).1
  have hq := (mem_chenAdditivePrimeCarrier.mp (Finset.mem_product.mp hc).2).2.1
  have hlog : 0 < Real.log (t.2 : ℝ) :=
    Real.log_pos (by exact_mod_cast hq.one_lt)
  apply (p5U7InteriorSelector_iff_strict_log hN (eta / 2) ho).mpr
  nlinarith only [hgate, mul_pos heta hlog]

/-- On the common cube the additive-intercept margin eta/2 implies the
multiplicative eta margin, since the second coordinate is below 1/2. -/
theorem p5U7TriangularInterior_subset_double_half_intercept {eta : ℝ}
    (heta : 0 ≤ eta) {x : Fin 2 → ℝ}
    (hx : x ∈ logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ)))
    (htri : x ∈ p5U7TriangularInterior (eta / 2)) :
    x ∈ p5U7InteriorRegion eta := by
  obtain ⟨ho, hcap⟩ := (mem_p5U7TriangularInterior_iff _ _).mp htri
  have hupper := ((mem_logPrimeBox.mp hx) 1).2
  apply (p5U7InteriorRegion_iff eta x).mpr
  exact ⟨ho, by nlinarith [mul_le_mul_of_nonneg_left hupper.le heta]⟩

/-- The opposite inclusion uses the exact lower cutoff d=59/250. -/
theorem p5U7InteriorRegion_subset_triangle_cutoff {eta : ℝ}
    (heta : 0 ≤ eta) {x : Fin 2 → ℝ}
    (hx : x ∈ logPrimeBox (fun _ : Fin 2 => (59 / 250 : ℝ))
      (fun _ => (1 / 2 : ℝ)))
    (hint : x ∈ p5U7InteriorRegion eta) :
    x ∈ p5U7TriangularInterior ((59 / 250 : ℝ) * eta) := by
  obtain ⟨ho, hcap⟩ := (p5U7InteriorRegion_iff eta x).mp hint
  have hlower := ((mem_logPrimeBox.mp hx) 1).1
  apply (mem_p5U7TriangularInterior_iff _ _).mpr
  exact ⟨ho, by nlinarith [mul_le_mul_of_nonneg_left hlower heta]⟩

end

end ImbalancedChen
