import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapCompiler

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual length conditions for merging two of the original four primes.
The box upper endpoints must be ADDED; a four-factor decomposition does
not itself provide a three-factor coefficient at arbitrary lengths.
The conditions below are checked on the original selected geometric
cell, before its arithmetic tuple. No residual beta factor is discarded.
-/

namespace ImbalancedChen.P5Z.U1011NativePrimePairMergeLengths

noncomputable section
open Classical
open U11Integral
open U1011OriginalSixteenArithmeticProducts
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenJointNativeCompiler
open P5U1011JointOverlap

/-- Exact physical merged length, on the same original prime tuple. -/
theorem pair_product_eq_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop}
    {t : Four} (ht : t ∈ jointSelector N E) (i k : Fin 4) :
    ((slots t i * slots t k : ℕ) : ℝ) =
      (N : ℝ) ^ (coordinates N t i + coordinates N t k) := by
  rw [Real.rpow_add (by exact_mod_cast (zero_lt_one.trans hN))]
  rw [actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) i,
    actualPrimeTupleLog_rpow hN (slots t) (slots_pos ht) k]
  exact Nat.cast_mul _ _

/-- An arithmetic pair can be put in a length N^a block precisely when
the SUM of its two true exponents fits. No one-slot bound suffices. -/
theorem pair_product_le_iff {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop}
    {t : Four} (ht : t ∈ jointSelector N E) (i k : Fin 4) (a : ℝ) :
    ((slots t i * slots t k : ℕ) : ℝ) ≤ (N : ℝ) ^ a ↔
      coordinates N t i + coordinates N t k ≤ a := by
  rw [pair_product_eq_rpow hN ht]
  exact Real.rpow_le_rpow_left_iff (by exact_mod_cast hN)

/-- Sufficient whole-cell length condition for an actual two-prime
merger. The rational corner is fixed before N and the arithmetic tuple. -/
theorem selected_cell_pair_length {n N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {j : Grid n} {t : Four}
    (ht : t ∈ selectedCellTuples n N E j) (i k : Fin 4) (a : ℝ)
    (hcorner : ((gridBox n j).hi i : ℝ) + ((gridBox n j).hi k : ℝ) ≤ a) :
    ((slots t i * slots t k : ℕ) : ℝ) ≤ (N : ℝ) ^ a := by
  have hs := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  apply (pair_product_le_iff hN hs i k a).mpr
  have hb := cell_subset_closed_box n j (selectedCellTuples_geometry hN ht)
  exact (add_le_add (hb.2 i) (hb.2 k)).trans hcorner

/-- The summed upper endpoint is also necessary for a claimed bound on
EVERY point of the closed safety box: its upper corner is a real point
of that box. This tests a geometric length assertion, not the existence
of a prime at a particular endpoint. -/
theorem whole_box_pair_condition (n : ℕ) (j : Grid n) (i k : Fin 4) (a : ℝ) :
    (∀ v ∈ (gridBox n j).region, v i + v k ≤ a) ↔
      ((gridBox n j).hi i : ℝ) + ((gridBox n j).hi k : ℝ) ≤ a := by
  constructor
  · intro h
    apply h (fun r => ((gridBox n j).hi r : ℝ))
    constructor
    · intro r
      exact_mod_cast gridBox_valid n j r
    · intro r
      exact le_rfl
  · intro h v hv
    exact (add_le_add (hv.2 i) (hv.2 k)).trans h

/-- Failure of the endpoint-sum test blocks this particular whole-box
merger certificate. It does not delete arithmetic boundary atoms. -/
theorem failed_corner_precludes_whole_box_pair_bound (n : ℕ) (j : Grid n)
    (i k : Fin 4) (a : ℝ)
    (hfail : a < ((gridBox n j).hi i : ℝ) + ((gridBox n j).hi k : ℝ)) :
    ¬ (∀ v ∈ (gridBox n j).region, v i + v k ≤ a) := by
  intro h
  exact (not_le_of_gt hfail) ((whole_box_pair_condition n j i k a).mp h)

end
end ImbalancedChen.P5Z.U1011NativePrimePairMergeLengths
