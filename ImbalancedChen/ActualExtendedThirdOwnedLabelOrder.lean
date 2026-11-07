import ImbalancedChen.ActualExtendedThirdFiniteCellIntegral
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Ordered integer endpoints of actual owned cells

The strict upper endpoint of the original owned Ico cell forces its labels
to be weakly decreasing. A closed physical cell alone does not have this
property: adjacent reversed labels can meet on their common boundary.

The integer upper endpoints are floors of the original power endpoints.
Actual prime atoms in the owned cell belong to the original exact power
box and to the resulting finite integer box. Every integer upper endpoint
stays below the original real endpoint. These are geometric dictionaries,
not a multi-label coefficient or factorial normalization statement.
-/

namespace ImbalancedChen

noncomputable section

open Set MeasureTheory
open VariableEnvelope
open scoped Classical

theorem actualExtendedThirdDyadicHi_le_lo_of_label_lt {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {i k : Fin 3} (h : j i < j k) :
    actualExtendedThirdDyadicHi m j i ≤ actualExtendedThirdDyadicLo m j k := by
  have hnat : (j i).val + 1 ≤ (j k).val := Nat.succ_le_of_lt h
  have hcast : (((j i).val + 1 : ℕ) : ℝ) ≤ ((j k).val : ℝ) := by
    exact_mod_cast hnat
  unfold actualExtendedThirdDyadicHi actualExtendedThirdDyadicLo
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcast (by norm_num [thirdPrefixRho])) (by positivity)

/-- The original Ico ownership, including either ordering wall, forces the
two adjacent label inequalities. -/
theorem actualExtendedThirdOwnedCell_labelOrder {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} {t : Fin 3 → ℝ}
    (ht : t ∈ actualExtendedThirdOwnedCell m j) :
    j 1 ≤ j 0 ∧ j 2 ≤ j 1 := by
  have hlabel (i k : Fin 3) (hki : t k ≤ t i) : j k ≤ j i := by
    by_contra hn
    have hsep := actualExtendedThirdDyadicHi_le_lo_of_label_lt
      (show j i < j k from lt_of_not_ge hn)
    have hupper := (ht.1 i (mem_univ _)).2
    have hlower := (ht.1 k (mem_univ _)).1
    exact (lt_irrefl (t i)) (hupper.trans_le (hsep.trans (hlower.trans hki)))
  exact ⟨hlabel 0 1 ht.2.2.2, hlabel 1 2 ht.2.2.1⟩

theorem actualExtendedThirdOwnedCell_nonempty_labelOrder {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m}
    (hj : (actualExtendedThirdOwnedCell m j).Nonempty) :
    j 1 ≤ j 0 ∧ j 2 ≤ j 1 := by
  obtain ⟨t, ht⟩ := hj
  exact actualExtendedThirdOwnedCell_labelOrder ht

theorem actualExtendedThirdOwnedCell_empty_of_label_lt {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hbad : j 0 < j 1 ∨ j 1 < j 2) :
    actualExtendedThirdOwnedCell m j = ∅ := by
  ext t
  constructor
  · intro ht
    have h := actualExtendedThirdOwnedCell_labelOrder ht
    rcases hbad with hbad | hbad
    · exact (not_lt_of_ge h.1) hbad
    · exact (not_lt_of_ge h.2) hbad
  · intro ht
    exact False.elim ht

/-- The actual prime carrier keeps primality and its exclusion of divisors
of the same target. An invalid label has no owned arithmetic atoms. -/
theorem actualExtendedThirdOwnedPrimeAtoms_empty_of_label_lt {N m : ℕ}
    (a b : Fin 3 → ℝ) {j : ActualExtendedThirdDyadicLabel m}
    (hbad : j 0 < j 1 ∨ j 1 < j 2) :
    ((actualPrimeBoxTuples N a b).filter
      (fun p => actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j)) = ∅ := by
  rw [actualExtendedThirdOwnedCell_empty_of_label_lt hbad]
  simp

theorem actualExtendedThirdRetainedCellIntegral_zero_of_label_lt {e : ℝ} {m : ℕ}
    {j : ActualExtendedThirdDyadicLabel m} (hbad : j 0 < j 1 ∨ j 1 < j 2) :
    actualExtendedThirdRetainedCellIntegral e m j = 0 := by
  unfold actualExtendedThirdRetainedCellIntegral
  rw [actualExtendedThirdOwnedCell_empty_of_label_lt hbad, Set.empty_inter]
  exact setIntegral_empty

/-- These are upper integer endpoints, with no ceil enlargement. -/
def actualExtendedThirdIntegerUpper (X : ℝ) (m : ℕ)
    (j : ActualExtendedThirdDyadicLabel m) : Fin 3 → ℕ :=
  fun i => Nat.floor (X ^ actualExtendedThirdDyadicHi m j i)

theorem actualExtendedThirdIntegerUpper_order_and_bound {X : ℝ} (hX : 1 ≤ X)
    {m : ℕ} {j : ActualExtendedThirdDyadicLabel m}
    (hj : j 1 ≤ j 0 ∧ j 2 ≤ j 1) :
    (actualExtendedThirdIntegerUpper X m j 1 ≤ actualExtendedThirdIntegerUpper X m j 0 ∧
      actualExtendedThirdIntegerUpper X m j 2 ≤ actualExtendedThirdIntegerUpper X m j 1) ∧
      ∀ i, (actualExtendedThirdIntegerUpper X m j i : ℝ) ≤
        X ^ actualExtendedThirdDyadicHi m j i := by
  have hhi {i k : Fin 3} (hik : j i ≤ j k) :
      actualExtendedThirdDyadicHi m j i ≤ actualExtendedThirdDyadicHi m j k := by
    have hnat : (j i).val ≤ (j k).val := hik
    have hcast : (((j i).val + 1 : ℕ) : ℝ) ≤ (((j k).val + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_le_add_right hnat 1
    unfold actualExtendedThirdDyadicHi
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcast (by norm_num [thirdPrefixRho])) (by positivity)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hX (hhi hj.1))
  · exact Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hX (hhi hj.2))
  · intro i
    exact Nat.floor_le (Real.rpow_nonneg (zero_le_one.trans hX) _)

/-- Original owned prime atoms lie in the exact original power box and
in a finite integer box with the same ordered upper endpoints. -/
theorem actualExtendedThirdOwnedCell_prime_integer_box {N m : ℕ} (hN : 1 < N)
    {j : ActualExtendedThirdDyadicLabel m} (p : Fin 3 → ℕ)
    (hp : ∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N)
    (ht : actualPrimeTupleLog N p ∈ actualExtendedThirdOwnedCell m j) :
    p ∈ actualPrimeBoxTuples N (actualExtendedThirdDyadicLo m j)
        (actualExtendedThirdDyadicHi m j) ∧
      p ∈ Fintype.piFinset (fun i => Finset.Icc 1
        (actualExtendedThirdIntegerUpper (N : ℝ) m j i)) ∧
      (actualExtendedThirdIntegerUpper (N : ℝ) m j 1 ≤
          actualExtendedThirdIntegerUpper (N : ℝ) m j 0 ∧
        actualExtendedThirdIntegerUpper (N : ℝ) m j 2 ≤
          actualExtendedThirdIntegerUpper (N : ℝ) m j 1) ∧
      ∀ i, (actualExtendedThirdIntegerUpper (N : ℝ) m j i : ℝ) ≤
        (N : ℝ) ^ actualExtendedThirdDyadicHi m j i := by
  have hbox : p ∈ actualPrimeBoxTuples N (actualExtendedThirdDyadicLo m j)
      (actualExtendedThirdDyadicHi m j) :=
    (mem_actualPrimeBoxTuples_log_iff hN _ _ p).mpr
      ⟨hp, mem_logPrimeBox.mpr (fun i => ht.1 i (mem_univ _))⟩
  have hupper := actualExtendedThirdIntegerUpper_order_and_bound
    (show (1 : ℝ) ≤ N by exact_mod_cast hN.le)
    (actualExtendedThirdOwnedCell_labelOrder ht)
  refine ⟨hbox, ?_, hupper⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_Icc.mpr
  refine ⟨(hp i).1.one_le, ?_⟩
  exact Nat.le_floor ((mem_actualPrimeBoxTuples_iff.mp hbox i).2.2.2.le)

end

end ImbalancedChen
