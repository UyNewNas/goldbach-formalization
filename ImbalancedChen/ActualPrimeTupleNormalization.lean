import ImbalancedChen.ActualSelectedPairFactorization

/-!
# Original prime-slot coefficients and the single factorial normalization

The carrier is the original finite set of ordered prime tuples for one
group of fixed slots.  Its intervals may overlap or repeat.  The coefficient
counts actual product fibres, before normalizing by the group size factorial.
Unique prime factorization bounds each fibre by the list of permutations of
one representative, including on nonsquarefree products.

For a fixed three-group assignment the original scalar is multiplied by
the three group factorials exactly once.  Any reciprocal repeated-label
factorial already present in that scalar is retained unchanged.  No
distribution estimate or claim that an assignment fibre is a Cartesian
prime box is made here.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical

/-- The original ordered-tuple convolution coefficient for a finite carrier. -/
def actualPrimeTupleCoefficient (T : Finset (List ℕ)) (n : ℕ) : ℕ :=
  (T.filter (fun ps => ps.prod = n)).card

/-- The manuscript's one normalization for a group of m original slots. -/
def actualNormalizedPrimeTupleCoefficient (T : Finset (List ℕ)) (m n : ℕ) : ℝ :=
  (actualPrimeTupleCoefficient T n : ℝ) / (m.factorial : ℝ)

/-- Different interval labels do not require disjoint prime supports.
Every product representation is a permutation of the same prime multiset. -/
theorem actualPrimeTupleCoefficient_le_factorial (T : Finset (List ℕ)) (m n : ℕ)
    (hlen : ∀ ps ∈ T, ps.length = m)
    (hprime : ∀ ps ∈ T, ∀ p ∈ ps, Nat.Prime p) :
    actualPrimeTupleCoefficient T n ≤ m.factorial := by
  by_cases hne : (T.filter (fun ps => ps.prod = n)).Nonempty
  · obtain ⟨ps, hps⟩ := hne
    obtain ⟨hpsT, hpsprod⟩ := Finset.mem_filter.mp hps
    have hperm (qs : List ℕ) (hqs : qs ∈ T.filter (fun qs => qs.prod = n)) :
        qs.Perm ps := by
      obtain ⟨hqsT, hqsprod⟩ := Finset.mem_filter.mp hqs
      exact (Nat.primeFactorsList_unique hqsprod (hprime qs hqsT)).trans
        (Nat.primeFactorsList_unique hpsprod (hprime ps hpsT)).symm
    calc
      actualPrimeTupleCoefficient T n ≤ ps.permutations.toFinset.card := by
        apply Finset.card_le_card
        intro qs hqs
        exact List.mem_toFinset.mpr (List.mem_permutations.mpr (hperm qs hqs))
      _ ≤ ps.permutations.length := List.toFinset_card_le
      _ = m.factorial := by rw [List.length_permutations, hlen ps hpsT]
  · simp only [actualPrimeTupleCoefficient,
      Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]
    exact Nat.zero_le _

/-- This one-bound is proved for all integers, including repeated-prime
products and integers outside the original tuple-convolution support. -/
theorem actualNormalizedPrimeTupleCoefficient_mem_Icc
    (T : Finset (List ℕ)) (m n : ℕ)
    (hlen : ∀ ps ∈ T, ps.length = m)
    (hprime : ∀ ps ∈ T, ∀ p ∈ ps, Nat.Prime p) :
    actualNormalizedPrimeTupleCoefficient T m n ∈ Set.Icc (0 : ℝ) 1 := by
  have hfact : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  unfold actualNormalizedPrimeTupleCoefficient
  refine ⟨div_nonneg (Nat.cast_nonneg _) hfact.le, (div_le_one hfact).mpr ?_⟩
  exact_mod_cast actualPrimeTupleCoefficient_le_factorial T m n hlen hprime

theorem actualNormalizedPrimeTupleCoefficient_abs_le_one
    (T : Finset (List ℕ)) (m n : ℕ)
    (hlen : ∀ ps ∈ T, ps.length = m)
    (hprime : ∀ ps ∈ T, ∀ p ∈ ps, Nat.Prime p) :
    |actualNormalizedPrimeTupleCoefficient T m n| ≤ 1 := by
  have h := actualNormalizedPrimeTupleCoefficient_mem_Icc T m n hlen hprime
  rw [abs_of_nonneg h.1]
  exact h.2

/-- Restoring a group factorial returns the original coefficient exactly. -/
theorem factorial_mul_actualNormalizedPrimeTupleCoefficient
    (T : Finset (List ℕ)) (m n : ℕ) :
    (m.factorial : ℝ) * actualNormalizedPrimeTupleCoefficient T m n =
      (actualPrimeTupleCoefficient T n : ℝ) := by
  have hfact : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  unfold actualNormalizedPrimeTupleCoefficient
  calc
    _ = (actualPrimeTupleCoefficient T n : ℝ) * m.factorial / m.factorial := by ring
    _ = _ := mul_div_cancel_right₀ _ hfact

/-- The original scalar c, including its original repeated-label symmetry
factor, is retained. Only the three group factorials move into that scalar. -/
theorem actualPrimeTuple_threeGroup_scalar_identity
    (c : ℝ) (T₁ T₂ T₃ : Finset (List ℕ)) (m₁ m₂ m₃ n₁ n₂ n₃ : ℕ) :
    c * (actualPrimeTupleCoefficient T₁ n₁ : ℝ) *
        (actualPrimeTupleCoefficient T₂ n₂ : ℝ) * (actualPrimeTupleCoefficient T₃ n₃ : ℝ) =
      (c * (m₁.factorial : ℝ) * (m₂.factorial : ℝ) * (m₃.factorial : ℝ)) *
        actualNormalizedPrimeTupleCoefficient T₁ m₁ n₁ *
        actualNormalizedPrimeTupleCoefficient T₂ m₂ n₂ *
        actualNormalizedPrimeTupleCoefficient T₃ m₃ n₃ := by
  rw [← factorial_mul_actualNormalizedPrimeTupleCoefficient T₁ m₁ n₁,
    ← factorial_mul_actualNormalizedPrimeTupleCoefficient T₂ m₂ n₂,
    ← factorial_mul_actualNormalizedPrimeTupleCoefficient T₃ m₃ n₃]
  ring

end

end ImbalancedChen
