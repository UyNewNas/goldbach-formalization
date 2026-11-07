import ImbalancedChen.P4BLabelledPairDictionary
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Exact affine geometry of the genuine labelled pair indicator

YELLOW / SOURCE-ONLY / UNCOMPILED DRAFT.

The project import above is the future normal module name of the sibling
P4BLabelledPairDictionary.lean.txt draft. No actual source is installed.
All four walls are exact equivalences on the positive prime carrier.
Strictness and inclusive endpoints are retained; no boundary, null-volume,
smoothing licence or Part 3 distribution estimate is assumed.
-/

namespace ImbalancedChen.P4BLabelledLogGeometry

noncomputable section

open scoped BigOperators
open Classical
open ImbalancedChen.Part3 ImbalancedChen.P4BLabelledPairDictionary

/-- Actual normalized prime logarithms, with the original labelled slots. -/
def logPoint (N : ℕ) (t : Fin 2 → Fin (N + 1)) : Fin 2 → ℝ :=
  fun i => Real.log ((t i).val : ℝ) / Real.log (N : ℝ)

/-- Exact mixture of three closed walls and the strict badness wall. -/
def affineRegion (b lower : ℝ) (v : Fin 2 → ℝ) : Prop :=
  v 0 ≤ v 1 ∧ b * v 1 < v 0 ∧ lower ≤ v 0 + v 1 ∧ v 0 + v 1 ≤ 1

theorem order_iff_normalized_logs {N r q : ℕ}
    (hN : (1 : ℝ) < N) (hr : 0 < (r : ℝ)) (hq : 0 < (q : ℝ)) :
    r ≤ q ↔ Real.log (r : ℝ) / Real.log (N : ℝ) ≤
      Real.log (q : ℝ) / Real.log (N : ℝ) := by
  rw [div_le_div_iff_of_pos_right (Real.log_pos hN),
    Real.log_le_log_iff hr hq, Nat.cast_le]

/-- The strict power wall remains strict after taking logarithms. No sign
assumption on b is needed, because the prime base is positive. -/
theorem power_iff_normalized_logs {N r q : ℕ} (b : ℝ)
    (hN : (1 : ℝ) < N) (hr : 0 < (r : ℝ)) (hq : 0 < (q : ℝ)) :
    (q : ℝ) ^ b < (r : ℝ) ↔
      b * (Real.log (q : ℝ) / Real.log (N : ℝ)) <
        Real.log (r : ℝ) / Real.log (N : ℝ) := by
  rw [← mul_div_assoc, div_lt_div_iff_of_pos_right (Real.log_pos hN),
    ← Real.log_rpow hq b,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos hq b) hr]

/-- The lower cutoff is a closed affine wall, including exact equality. -/
theorem lowerCutoff_iff_normalized_logs {N r q : ℕ} {T : ℝ}
    (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hr : 0 < (r : ℝ)) (hq : 0 < (q : ℝ)) :
    T ≤ (r * q : ℕ) ↔ Real.log T / Real.log (N : ℝ) ≤
      Real.log (r : ℝ) / Real.log (N : ℝ) +
        Real.log (q : ℝ) / Real.log (N : ℝ) := by
  rw [Nat.cast_mul, ← add_div,
    div_le_div_iff_of_pos_right (Real.log_pos hN),
    ← Real.log_mul hr.ne' hq.ne', Real.log_le_log_iff hT (mul_pos hr hq)]

/-- The original inclusive product cap becomes x+y<=1 exactly. -/
theorem upperProduct_iff_normalized_logs {N r q : ℕ}
    (hN : (1 : ℝ) < N) (hr : 0 < (r : ℝ)) (hq : 0 < (q : ℝ)) :
    r * q ≤ N ↔ Real.log (r : ℝ) / Real.log (N : ℝ) +
      Real.log (q : ℝ) / Real.log (N : ℝ) ≤ 1 := by
  rw [← add_div, div_le_one (Real.log_pos hN),
    ← Real.log_mul hr.ne' hq.ne',
    Real.log_le_log_iff (mul_pos hr hq) (zero_lt_one.trans hN),
    ← Nat.cast_mul, Nat.cast_le]

/-- Positivity is supplied by the actual labelled prime carrier. -/
theorem labelled_prime_pair_pos {N : ℕ} {t : Fin 2 → Fin (N + 1)}
    (ht : t ∈ labelledPrimeTuples 2 N) :
    0 < ((tuplePair t).1 : ℝ) ∧ 0 < ((tuplePair t).2 : ℝ) := by
  classical
  have hp : ∀ i : Fin 2, Nat.Prime (t i).val :=
    (Finset.mem_filter.mp ht).2
  constructor
  · exact_mod_cast (hp 0).pos
  · exact_mod_cast (hp 1).pos

/-- Complete exact dictionary on every actual labelled prime tuple. The
prime condition is inherited from the carrier; geometry adds no new primes. -/
theorem geometry_iff_affineRegion {b T : ℝ} {N : ℕ}
    {t : Fin 2 → Fin (N + 1)} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (ht : t ∈ labelledPrimeTuples 2 N) :
    geometry b N T t ↔
      affineRegion b (Real.log T / Real.log (N : ℝ)) (logPoint N t) := by
  obtain ⟨hr, hq⟩ := labelled_prime_pair_pos ht
  exact and_congr (order_iff_normalized_logs hN hr hq)
    (and_congr (power_iff_normalized_logs b hN hr hq)
      (and_congr (lowerCutoff_iff_normalized_logs hN hT hr hq)
        (upperProduct_iff_normalized_logs hN hr hq)))

/-- The actual W is exactly this affine-region indicator, pointwise on the
whole original labelled prime carrier, including every boundary point. -/
theorem W_eq_affineIndicator {b T : ℝ} {N : ℕ}
    {t : Fin 2 → Fin (N + 1)} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (ht : t ∈ labelledPrimeTuples 2 N) :
    W b N T t =
      (if affineRegion b (Real.log T / Real.log (N : ℝ)) (logPoint N t)
        then (1 : ℝ) else 0) := by
  classical
  unfold W
  rw [geometry_iff_affineRegion hN hT ht]

/-- Rows in order: ordering, strict badness, lower cutoff, upper product.
The bounds are respectively 0, 0, -lower, 1. Only the second wall is strict. -/
def wallRow (b : ℝ) : Fin 4 → Fin 2 → ℝ :=
  ![![1, -1], ![-1, b], ![-1, -1], ![1, 1]]

def wallValue (b : ℝ) (i : Fin 4) (v : Fin 2 → ℝ) : ℝ :=
  ∑ j : Fin 2, wallRow b i j * v j

/-- Every displayed wall has a nonzero linear row for every real b. -/
theorem wallRow_ne_zero (b : ℝ) (i : Fin 4) : wallRow b i ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  fin_cases i <;> norm_num [wallRow] at h0

theorem wallValues (b : ℝ) (v : Fin 2 → ℝ) :
    wallValue b 0 v = v 0 - v 1 ∧
    wallValue b 1 v = -v 0 + b * v 1 ∧
    wallValue b 2 v = -(v 0 + v 1) ∧
    wallValue b 3 v = v 0 + v 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [wallValue, wallRow, Fin.sum_univ_two] <;> ring

/-- Direct row interface for an affine outer ramp. The strict wall remains
strict in this identity and the other walls remain closed. -/
theorem affineRegion_iff_rows (b lower : ℝ) (v : Fin 2 → ℝ) :
    affineRegion b lower v ↔
      wallValue b 0 v ≤ 0 ∧ wallValue b 1 v < 0 ∧
        wallValue b 2 v ≤ -lower ∧ wallValue b 3 v ≤ 1 := by
  obtain ⟨h0, h1, h2, h3⟩ := wallValues b v
  rw [h0, h1, h2, h3]
  unfold affineRegion
  constructor <;> rintro ⟨horder, hpower, hcutoff, hproduct⟩ <;>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end

end ImbalancedChen.P4BLabelledLogGeometry
